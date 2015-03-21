{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
module Denotational.Test.Equiv where

import           Control.Lens
import           Control.Monad
import qualified Data.List                             as List
import           Test.Hspec
import qualified Text.PrettyPrint.ANSI.Leijen          as PP

import           FunLogic.Core                         as FL
import           FunLogic.Semantics.Denotational       as DF
import qualified FunLogic.Semantics.PartialOrder       as PO
import qualified FunLogic.Semantics.Search             as Search
import           Language.CuMin                        as CuMin
import           Language.CuMin.Semantics.Denotational as DC
import qualified Language.CuminToSalt                  as C2S
import qualified Language.CuminToSalt.Util             as C2S
import           Language.SaLT                         as SaLT
import           Language.SaLT.Semantics.Denotational  as DS

import qualified Denotational.Test.Common              as Common

expectSet :: (Search.MonadSearch n, Search.Observable n) => DS.Value n -> IO [DS.Value n]
expectSet (DS.VSet vs _) = return $ Search.observeAll vs
expectSet _ = expectationFailure "Set value expected" >> return undefined

cuminToSaltVal :: Monad n => DC.Value n -> DS.Value n
cuminToSaltVal (DC.VCon c args tys) = DS.VCon c (map cuminToSaltVal args) (map C2S.cTypeToSType tys)
cuminToSaltVal (DC.VBot str) = DS.VBot str
cuminToSaltVal (DC.VNat n) = DS.VNat n
cuminToSaltVal (DC.VFun _ u) = DS.VFun undefined u

cuminSaltEquiv :: CuMin.Module -> SaLT.Module -> CuMin.Exp -> SaLT.Exp -> DF.StepIndex -> Expectation
cuminSaltEquiv cmod smod cexp sexp step = do
  cvalsD <- Common.expectEval cexp cmod step Common.dfsProxy
  cvalsB <- Common.expectEval cexp cmod step Common.bfsProxy
  svalsD <- Common.expectEval sexp smod step Common.dfsProxy >>= expectSet
  svalsB <- Common.expectEval sexp smod step Common.bfsProxy >>= expectSet
  svalsD `shouldBe` map cuminToSaltVal cvalsD
  svalsB `shouldBe` map cuminToSaltVal cvalsB
  case mapM Common.castValue cvalsB of
    Nothing -> fail "function value returned"
    Just cvalsD' -> PO.partiallyEqual cvalsD cvalsD' `shouldBe` True

testModCumin :: CuMin.Module
testModCumin = $(CuMin.moduleFromFileWithPrelude CuMin.preludeModule "files/EquivTests.cumin")

-- | Performs the equivalence tests.
spec :: Spec
spec = do
  testModCuminPrelude <- either (fail . show) return $ CuMin.importUnqualified testModCumin CuMin.preludeModule
  let testModSalt = C2S.cuminToSalt False testModCuminPrelude
  -- check if the resulting SaLT program is indeed correct
  either (fail . show . PP.plain . PP.pretty) (const $ return ())
    $ SaLT.evalTC' (SaLT.checkModule testModSalt)

  bindings <- either fail return $ Common.testBindings "eqTest" testModCuminPrelude testModSalt

  describe "Equivalence tests" $ forM_ bindings $ \(name, cuminBnd, saltBnd) -> it name $
    cuminSaltEquiv testModCuminPrelude testModSalt
        (cuminBnd ^. FL.bindingExpr) (saltBnd ^. FL.bindingExpr) (DF.StepNatural 5)
