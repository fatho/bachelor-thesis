{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
module Denotational.Test.Benchmark where

import qualified FunLogic.Core                         as FL
import qualified FunLogic.Semantics.Denotational       as Core
import qualified FunLogic.Semantics.PartialOrder       as PO
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

isTotalSalt :: DS.Value n -> Bool
isTotalSalt (DS.VBot _)        = False
isTotalSalt (DS.VFun _ _)      = True
isTotalSalt (DS.VNat _)        = True
isTotalSalt (DS.VSet _ _)      = True
isTotalSalt (DS.VCon _ args _) = all isTotalSalt args

isTotalCuMin :: DC.Value n -> Bool
isTotalCuMin (DC.VBot _)        = False
isTotalCuMin (DC.VFun _ _)      = True
isTotalCuMin (DC.VNat _)        = True
isTotalCuMin (DC.VCon _ args _) = all isTotalCuMin args

firstTotalCuMin :: (Search.Observable n) => n (DC.Value n) -> Maybe (DC.Value n)
firstTotalCuMin = List.find isTotalCuMin . Search.observeAll

firstTotalSalt :: (Search.Observable n) => n (DS.Value n) -> Maybe (DS.Value n)
firstTotalSalt = List.find isTotalSalt . Search.observeAll

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
  let testModSalt = C2S.cuminToSalt False testModCuminPrelude
  -- check if the resulting SaLT program is indeed correct
  either (fail . show . PP.plain . PP.pretty) (const $ return ())
    $ SaLT.evalTC' (SaLT.checkModule testModSalt)

  bindings <- either fail return $ Common.testBindings "bench" testModCuminPrelude testModSalt

  defaultMain $ mkBenchmarks $ map (mkEnv testModCuminPrelude testModSalt) bindings

mkEnv :: CuMin.Module -> SaLT.Module -> (FL.BindingName, CuMin.Binding, SaLT.Binding) -> BenchmarkEnv
mkEnv cuminMod saltMod (name, cuminBnd, saltBnd) = BenchmarkEnv cuminMod saltMod name cuminBnd saltBnd

mkBenchmarks :: [BenchmarkEnv] -> [Benchmark]
mkBenchmarks envs =
  [ bgroup "DFS" $ mkBenchmarksForSearch envs id id dfsProxy
  , bgroup "BFS" $ mkBenchmarksForSearch envs id id bfsProxy
  , bgroup "IterDFS" $ mkBenchmarksForSearch envs DC.iterDeep DS.iterDeep dfsProxy
  ]

mkBenchmarksForSearch :: (Search.MonadSearch n) => [BenchmarkEnv]
    -> (DC.Eval n (DC.Value n) -> DC.Eval n (DC.Value n))
    -> (DS.EvalExp n (DS.Value n) -> DS.EvalExp n (DS.Value n))
    -> Proxy n -> [Benchmark]
mkBenchmarksForSearch envs tcumin tsalt proxy =
  [ bgroup "NoPruning" $ []
  ]

bfsProxy :: Proxy Logic.Logic
bfsProxy = Proxy

dfsProxy :: Proxy (Search.UnFair Logic.Logic)
dfsProxy = Proxy

evalCumin :: (Search.MonadSearch n) => Proxy n -> DC.Eval n (DC.Value n) -> CuMin.Module
    -> Core.StepIndex -> DC.PruningF n DC.Value -> n (DC.Value n)
evalCumin _ = DC.runEval

benchmarkCumin :: String -> Core.StepIndex -> Proxy n -> BenchmarkEnv -> Benchmark
benchmarkCumin = undefined
