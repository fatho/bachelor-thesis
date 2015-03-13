{-# LANGUAGE LambdaCase #-}
module Denotational.Test.Equiv where

import           Control.Applicative
import           Control.Lens
import qualified Data.List                             as List
import           Data.Proxy
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

-- | Performs the equivalence tests.
spec :: Spec
spec = do
  testModCuMin <- runIO $ fmap snd <$> CuMin.loadAndCheckCuMin CuMin.preludeModule "files/EquivTests.cumin" >>= \case
      Left err -> fail $ show $ PP.plain err
      Right mod' -> return mod'
  let testModSalt = C2S.cuminToSalt False testModCuMin
  -- check if the resulting SaLT program is indeed correct
  either (fail . show . PP.plain . PP.pretty) (const $ return ())
    $ SaLT.evalTC' (SaLT.checkModule testModSalt)

  describe "Equivalence tests" $
    forOf_ (FL.modBinds . traverse . FL.bindingsByName (List.isPrefixOf "eqTest")) testModCuMin $ \cuminBnd -> do
      let name = cuminBnd ^. FL.bindingName
      it name $ case testModSalt ^. FL.modBinds . at name of
        Nothing -> expectationFailure $ "SaLT translation does not contain " ++ name
        Just saltBnd
          | not $ null $ cuminBnd ^. CuMin.bindingArgs -> expectationFailure "equivalence test must not have arguments"
          | otherwise -> cuminSaltEquiv testModCuMin testModSalt
                (cuminBnd ^. FL.bindingExpr) (saltBnd ^. FL.bindingExpr) (DF.StepNatural 5)
