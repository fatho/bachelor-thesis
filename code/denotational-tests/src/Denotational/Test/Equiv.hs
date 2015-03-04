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
import qualified FunLogic.Semantics.Search             as Search
import           Language.CuMin                        as CuMin
import           Language.CuMin.Semantics.Denotational as DC
import qualified Language.CuminToSalt.Translation      as C2S
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

cuminSaltEquiv :: (Search.MonadSearch n, Search.Observable n) => Proxy n -> DF.StepIndex -> CuMin.Module -> SaLT.Module -> CuMin.Exp -> SaLT.Exp -> Expectation
cuminSaltEquiv ev step cmod smod cexp sexp = do
  cvals <- Common.expectEval cexp cmod step ev
  svals <- Common.expectEval sexp smod step ev >>= expectSet
  svals `shouldBe` map cuminToSaltVal cvals

spec :: Spec
spec = do
  testModCuMin <- runIO $ fmap snd <$> CuMin.loadAndCheckCuMin CuMin.preludeModule "files/EquivTests.cumin" >>= \case
      Left err -> fail $ show $ PP.plain err
      Right mod' -> return mod'
  let testModSalt = C2S.cuminToSalt testModCuMin

  describe "Equivalence tests" $
    forOf_ (FL.modBinds . traverse . FL.bindingsByName (List.isPrefixOf "eqTest")) testModCuMin $ \cuminBnd -> do
      let name = cuminBnd ^. FL.bindingName
      it name $ case testModSalt ^. FL.modBinds . at name of
        Nothing -> expectationFailure $ "SaLT translation does not contain " ++ name
        Just saltBnd
          | not $ null $ cuminBnd ^. CuMin.bindingArgs -> expectationFailure "equivalence test must not have arguments"
          | otherwise -> cuminSaltEquiv Common.dfsProxy (DF.StepNatural 5) testModCuMin testModSalt
                (cuminBnd ^. FL.bindingExpr) (saltBnd ^. FL.bindingExpr)
