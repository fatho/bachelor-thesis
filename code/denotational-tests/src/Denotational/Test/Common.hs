{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilies           #-}
module Denotational.Test.Common where

import           Control.Applicative
import           Control.Exception                (evaluate)
import           Control.Lens
import           Control.Monad
import qualified Control.Monad.Logic              as Logic
import           Control.Monad.Trans.Either
import qualified Data.List                        as List
import           Data.Proxy
import qualified Data.Set                         as Set
import           Test.Hspec
import           Test.QuickCheck
import qualified Text.PrettyPrint.ANSI.Leijen     as PP

import qualified Language.CuminToSalt.Translation as C2S
import qualified Language.CuminToSalt.Util        as C2S

import qualified FunLogic.Core.AST                as FL
import qualified FunLogic.Core.ModBuilder         as FL

import qualified FunLogic.Semantics.Denotational  as Core
import qualified FunLogic.Semantics.PartialOrder  as PO
import qualified FunLogic.Semantics.Search        as Search

import qualified Language.CuMin                   as CuMin

import qualified Language.SaLT                    as SaLT

docStr :: PP.Doc -> String
docStr = flip PP.displayS "" . PP.renderPretty 0.9 80 . PP.plain

-- | Proxy for choosing a DFS monad
dfsProxy :: Proxy (Search.UnFair Logic.Logic)
dfsProxy = Proxy

-- | Proxy for choosing a BFS monad
bfsProxy :: Proxy Logic.Logic
bfsProxy = Proxy

-- | Class to express expectations requiring an expression to be typeable.
class ExpectTypeable exp bnd ty | exp -> bnd, exp -> ty where
  expectTypeable :: exp -> FL.CoreModule bnd -> IO ty

-- | Class to express expectations requiring the evaluation of an expression.
class ExpectEvaluation exp bnd | exp -> bnd where
  -- | Return type of the evaluation. Needed to differentiate between CuMin and SaLT, since the former always returns
  -- sets whereas the latter does not.
  type Ret exp (n :: * -> *) :: *
  -- | Expect the evaluation of the expression (this includes that it passes the type checker) under a given
  -- monad, in a module with some initial step index.
  expectEval :: (Search.MonadSearch n, Search.Observable n) => exp -> FL.CoreModule bnd -> Core.StepIndex -> Proxy n -> IO (Ret exp n)

instance ExpectTypeable CuMin.Exp CuMin.Binding CuMin.Type where
  expectTypeable expr modContext =
    case CuMin.evalTC' $ do
      CuMin.includeBuiltIns
      CuMin.unsafeIncludeModule modContext
      CuMin.checkExp expr
    of
      Left msg -> do
        expectationFailure $ show $ PP.plain $ PP.pretty msg
        return undefined
      Right ty -> return ty

instance ExpectTypeable SaLT.Exp SaLT.Binding SaLT.Type where
  expectTypeable expr modContext =
    case SaLT.evalTC' $ do
      SaLT.includeBuiltIns
      SaLT.unsafeIncludeModule modContext
      SaLT.checkExp expr
    of
      Left msg -> do
        expectationFailure $ show $ PP.plain $ PP.pretty msg
        return undefined
      Right ty -> return ty

instance ExpectEvaluation CuMin.Exp CuMin.Binding where
  type Ret CuMin.Exp n = [CuMin.Value n]
  expectEval expr modContext idx _ = Search.observeAll <$> cuminEvalGeneral expr modContext idx

instance ExpectEvaluation SaLT.Exp SaLT.Binding where
  type Ret SaLT.Exp n = SaLT.Value n
  expectEval expr modContext idx _ =  saltEvalGeneral expr modContext idx

cuminEvalGeneral :: (Search.MonadSearch n) => CuMin.Exp -> CuMin.Module -> Core.StepIndex -> IO (n (CuMin.Value n))
cuminEvalGeneral expr modContext idx = do
  let pexpr = CuMin.postProcessExp Set.empty expr
  void $ expectTypeable pexpr modContext
  return $ CuMin.runEval (CuMin.eval pexpr) modContext idx

saltEvalGeneral :: (Search.MonadSearch n) => SaLT.Exp -> SaLT.Module -> Core.StepIndex -> IO (SaLT.Value n)
saltEvalGeneral expr modContext idx = do
  let pexpr = SaLT.postProcessExp Set.empty expr
  void $ expectTypeable pexpr modContext
  return $ SaLT.runEval (SaLT.eval pexpr) modContext idx

