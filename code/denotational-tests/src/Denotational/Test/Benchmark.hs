{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE QuasiQuotes               #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE TemplateHaskell           #-}
module Denotational.Test.Benchmark where

import qualified FunLogic.Core                         as FL
import qualified FunLogic.Semantics.Denotational       as Core
import qualified FunLogic.Semantics.PartialOrder       as PO
import qualified FunLogic.Semantics.Pruning            as Pruning
import qualified FunLogic.Semantics.Search             as Search
import qualified Language.CuMin                        as CuMin
import qualified Language.CuMin.Semantics.Denotational as DC
import qualified Language.CuminToSalt                  as C2S
import qualified Language.CuminToSalt.Util             as C2S
import qualified Language.SaLT                         as SaLT
import qualified Language.SaLT.Semantics.Denotational  as DS

import qualified Denotational.Test.Common              as Common

import           Control.Lens
import           Control.Monad
import qualified Control.Monad.Logic                   as Logic
import           Control.Monad.Reader
import           Criterion.Main
import qualified Data.List                             as List
import           Data.Maybe
import           Data.Proxy
import qualified Text.PrettyPrint.ANSI.Leijen          as PP

-- | Checks if a SaLT value is total, i.e. contains no bottoms.
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
  testModCuminPrelude <- either (fail . show) return $ CuMin.importUnqualified testModCumin CuMin.preludeModule
  let testModSalt = C2S.cuminToSalt True testModCuminPrelude
  -- check if the resulting SaLT program is indeed correct
  either (fail . show . PP.plain . PP.pretty) (const $ return ())
    $ SaLT.evalTC' (SaLT.checkModule testModSalt)

  bindings <- either fail return $ Common.testBindings "bench" testModCuminPrelude testModSalt

  defaultMain $ mkBenchmarks $ map (mkEnv testModCuminPrelude testModSalt) bindings

mkEnv :: CuMin.Module -> SaLT.Module -> (FL.BindingName, CuMin.Binding, SaLT.Binding) -> BenchmarkEnv
mkEnv cuminMod saltMod (name, cuminBnd, saltBnd) = BenchmarkEnv cuminMod saltMod name cuminBnd saltBnd

data SomeProxy = forall n. (Search.Observable n, Search.MonadSearch n) => SomeProxy (Proxy n)

data BenchSearch = SearchDFS | SearchBFS | SearchIter deriving (Eq, Ord, Enum, Bounded, Show)
data BenchLanguage = LangCumin | LangSalt deriving (Eq, Ord, Enum, Bounded, Show)
data BenchPruning = PruningNone | PruningNonMax | PruningDuplicates deriving (Eq, Ord, Enum, Bounded, Show)

mkBenchmark :: BenchSearch -> BenchPruning -> BenchLanguage -> BenchmarkEnv -> Benchmark
mkBenchmark s p l BenchmarkEnv {..} = bench "eval" $ withLang l where
  withLang LangCumin = (case s of
        SearchDFS  -> benchmarkCumin dfsProxy (DC.eval cuminExp) (pruningFor p)
        SearchBFS  -> benchmarkCumin bfsProxy (DC.eval cuminExp) (pruningFor p)
        SearchIter -> benchmarkCumin dfsProxy (DC.iterDeep $ DC.eval cuminExp) (pruningFor p)
    ) DC.StepInfinity _benchCuminMod
  withLang LangSalt = (case s of
        SearchDFS  -> benchmarkSalt dfsProxy (DS.eval saltExp) (pruningFor p)
        SearchBFS  -> benchmarkSalt bfsProxy (DS.eval saltExp) (pruningFor p)
        SearchIter -> benchmarkSalt dfsProxy (DS.iterDeep $ DS.eval saltExp) (pruningFor p)
    ) DS.StepInfinity _benchSaltMod

  cuminExp = _benchCuminBnd ^. FL.bindingExpr
  saltExp  = _benchSaltBnd ^. FL.bindingExpr

  pruningFor PruningNone       = id
  pruningFor PruningNonMax     = Pruning.pruneNonMaximal
  pruningFor PruningDuplicates = Pruning.pruneDuplicates

benchForEach :: Show a => [a] -> (a -> [Benchmark]) -> [Benchmark]
benchForEach xs f = map go xs where
  go x = bgroup (show x) (f x)

mkBenchmarks :: [BenchmarkEnv] -> [Benchmark]
mkBenchmarks envs =
  flip map envs $ \benv -> bgroup (view benchName benv) $
    benchForEach [minBound..maxBound] $ \strategy ->
      benchForEach [minBound..maxBound] $ \pruning ->
        benchForEach [minBound..maxBound] $ \lang ->
          map (mkBenchmark strategy pruning lang) envs

bfsProxy :: Proxy Logic.Logic
bfsProxy = Proxy

dfsProxy :: Proxy (Search.UnFair Logic.Logic)
dfsProxy = Proxy

benchmarkCumin :: (Search.MonadSearch n, Search.Observable n)
    => Proxy n -> DC.Eval n (DC.Value n) -> DC.PruningF n DC.Value -> Core.StepIndex
    -> CuMin.Module -> Benchmarkable
benchmarkCumin _ action pruning stepIdx modul =
  whnf (List.find (not . containsBottomCuMin) . Search.observeAll)
    $ DC.runEval action modul stepIdx pruning

benchmarkSalt :: (Search.MonadSearch n, Search.Observable n)
    => Proxy n -> DS.EvalExp n (DS.Value n) -> DS.PruningF n DS.Value -> Core.StepIndex
    -> SaLT.Module -> Benchmarkable
benchmarkSalt _ action pruning stepIdx modul =
      whnf (List.find (not . containsBottomSalt) . Search.observeAll . ensureSet)
        $ DS.runEval action modul stepIdx pruning
  where
    ensureSet (DS.VSet vs _) = vs
    ensureSet _ = error "result not a set"
