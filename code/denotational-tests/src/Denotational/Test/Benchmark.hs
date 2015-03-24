{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE QuasiQuotes               #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE LambdaCase                #-}
module Denotational.Test.Benchmark where

import qualified FunLogic.Core                         as FL
import qualified FunLogic.Semantics.Denotational       as Core
import qualified FunLogic.Semantics.PartialOrder       as PO
import qualified FunLogic.Semantics.Pruning            as Pruning
import qualified FunLogic.Semantics.Search             as Search
import qualified Language.CuMin                        as CuMin
import qualified Language.CuMin.Semantics.Denotational as DC
import qualified Language.CuminToSalt                  as C2S
import qualified Language.SaLT                         as SaLT
import qualified Language.SaLT.Semantics.Denotational  as DS

import qualified Denotational.Test.Common              as Common

import           Control.Applicative
import           Control.Lens
import qualified Control.Monad.Logic                   as Logic
import           Criterion.Main
import qualified Data.List                             as List
import           Data.Proxy
import qualified System.Environment                    as Env
import qualified Text.PrettyPrint.ANSI.Leijen          as PP

import qualified Debug.Trace as Dbg

-- | Checks for a bottom in a SaLT value, nested sets are not searched.
containsBottomSalt :: DS.Value n -> Bool
containsBottomSalt (DS.VBot _)        = True
containsBottomSalt (DS.VFun _ _)      = False
containsBottomSalt (DS.VNat _)        = False
containsBottomSalt (DS.VSet _ _)      = False
containsBottomSalt (DS.VCon _ args _) = any containsBottomSalt args

containsBottomCuMin :: DC.Value n -> Bool
containsBottomCuMin (DC.VBot _)        = True
containsBottomCuMin (DC.VFun _ _)      = False
containsBottomCuMin (DC.VNat _)        = False
containsBottomCuMin (DC.VCon _ args _) = any containsBottomCuMin args

-- | CuMin module containing the benchmarks
testModCumin :: CuMin.Module
testModCumin = $(CuMin.moduleFromFileWithPrelude CuMin.preludeModule "files/TestEnv.cumin")

data BenchmarkEnv = BenchmarkEnv
  { _benchCuminMod :: CuMin.Module
  , _benchSaltMod  :: SaLT.Module
  , _benchName     :: FL.BindingName
  , _benchCuminBnd :: CuMin.Binding
  , _benchSaltBnd  :: SaLT.Binding
  }

makeLenses ''BenchmarkEnv

runBenchmark :: IO ()
runBenchmark = do
  -- merge prelude into benchmark module and translate to SaLT
  testModCuminPrelude <- either (fail . show) return $ CuMin.importUnqualified testModCumin CuMin.preludeModule
  let testModSalt = C2S.cuminToSalt False testModCuminPrelude
  -- check if the resulting SaLT program is indeed correct
  either (fail . show . PP.plain . PP.pretty) (const $ return ())
    $ SaLT.evalTC' (SaLT.checkModule testModSalt)
  -- extract name of bindings
  bindings <- either fail return $ Common.testBindings "bench" testModCuminPrelude testModSalt

  defaultMain
      $ map (mkBenchmarks . mkEnv testModCuminPrelude testModSalt) bindings

mkEnv :: CuMin.Module -> SaLT.Module -> (FL.BindingName, CuMin.Binding, SaLT.Binding) -> BenchmarkEnv
mkEnv cuminMod saltMod (name, cuminBnd, saltBnd) = BenchmarkEnv cuminMod saltMod name cuminBnd saltBnd

data BenchSearch = SearchDFS | SearchBFS | SearchIter deriving (Eq, Ord, Enum, Bounded, Show)
data BenchLanguage = LangCumin | LangSalt deriving (Eq, Ord, Enum, Bounded, Show)
data BenchPruning = PruningNone | PruningNonMax | PruningDuplicates deriving (Eq, Ord, Enum, Bounded, Show)

pruningNone :: (Search.MonadSearch m) => m a -> m a
pruningNone m = Search.peek m >>= \case
  Nothing -> Logic.mzero
  Just (v,vs) -> Logic.mplus (return v) vs

-- | Creates a single evaluation benchmark using the supplied configuration.
evalBenchmark :: BenchSearch -> BenchPruning -> BenchLanguage -> BenchmarkEnv -> Benchmarkable
evalBenchmark s p l BenchmarkEnv {..} = withLang l where
  withLang LangCumin = (case s of
        SearchDFS  -> benchmarkCumin dfsProxy (DC.eval cuminExp) pruningImpl
        SearchBFS  -> benchmarkCumin bfsProxy (DC.eval cuminExp) pruningImpl
        SearchIter -> benchmarkCumin dfsProxy (DC.iterDeep $ DC.eval cuminExp) pruningImpl
    ) DC.StepInfinity _benchCuminMod
  withLang LangSalt = (case s of
        SearchDFS  -> benchmarkSalt dfsProxy (DS.eval saltExp) pruningImpl
        SearchBFS  -> benchmarkSalt bfsProxy (DS.eval saltExp) pruningImpl
        SearchIter -> benchmarkSalt dfsProxy (DS.iterDeep $ DS.eval saltExp) pruningImpl
    ) DS.StepInfinity _benchSaltMod

  cuminExp = _benchCuminBnd ^. FL.bindingExpr
  saltExp  = _benchSaltBnd ^. FL.bindingExpr

  pruningImpl :: (Search.MonadSearch m, Show a, PO.PartialOrd a, Ord a) => m a -> m a
  pruningImpl = case p of
      PruningNone       -> pruningNone
      PruningNonMax     -> Pruning.pruneNonMaximal
      PruningDuplicates -> Pruning.pruneDuplicates

-- creates a benchmark group for each item in the list named using the @Show@ instance.
bgroupForEach :: Show a => [a] -> (a -> [Benchmark]) -> [Benchmark]
bgroupForEach xs f = map go xs where
  go x = bgroup (show x) (f x)

-- | Create benchmarks for all possible configurations for a given environment.
mkBenchmarks :: BenchmarkEnv -> Benchmark
mkBenchmarks benv =
  bgroup (view benchName benv) $
    bgroupForEach [minBound..maxBound] $ \strategy ->
      bgroupForEach [minBound..maxBound] $ \pruning ->
        flip map [minBound..maxBound] $ \lang ->
          bench (show lang) $ evalBenchmark strategy pruning lang benv

-- | Proxy used to force LogicT as non-determinism monad
bfsProxy :: Proxy Logic.Logic
bfsProxy = Proxy

-- | Proxy used to force unfair LogicT as non-determinism monad
dfsProxy :: Proxy (Search.UnFair Logic.Logic)
dfsProxy = Proxy

-- | Benchmarks a CuMin evaluation by measuring the time needed to produce the first fully defined result.
benchmarkCumin :: (Search.MonadSearch n, Search.Observable n)
    => Proxy n -> DC.Eval n (DC.Value n) -> DC.PruningF n DC.Value -> Core.StepIndex
    -> CuMin.Module -> Benchmarkable
benchmarkCumin _ action pruning stepIdx modul =
  whnf (List.find (not . containsBottomCuMin) . Search.observeAll . DC.runEval action modul stepIdx) pruning

-- | Benchmarks a SaLT evaluation by measuring the time needed to produce the first fully defined result.
benchmarkSalt :: (Search.MonadSearch n, Search.Observable n)
    => Proxy n -> DS.EvalExp n (DS.Value n) -> DS.PruningF n DS.Value -> Core.StepIndex
    -> SaLT.Module -> Benchmarkable
benchmarkSalt _ action pruning stepIdx modul =
      whnf (List.find (not . containsBottomSalt) . Search.observeAll . ensureSet . DS.runEval action modul stepIdx) pruning
  where
    ensureSet (DS.VSet vs _) = vs
    ensureSet _ = error "result not a set"