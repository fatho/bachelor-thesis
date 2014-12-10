{-# LANGUAGE TemplateHaskell, MonadComprehensions, ConstraintKinds #-}
module Denotational.CuMin.Interpreter where

import qualified Data.Map             as M
import Data.Maybe

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Reader

import           Control.Lens

import           Data.Traversable as T
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           FunLogic.Core.AST
import           Language.CuMin.AST   as CuMin

-- type POSet a = [a]

-- | Encapsulates the Alternative and MonadPlus constraints to be prepared
-- for the upcoming Applicative/Monad hierarchy in GHC 7.10
type NonDeterministic m = (Alternative m, MonadPlus m)

data Value
  = VCon Name [Value]          -- ^ ADT constructor
  | VNat Integer               -- ^ natural numbers
  | VFun (Value -> Value)      -- ^ closure
  | VBot                       -- ^ bottom

instance Pretty Value where
  pretty (VCon con args) = text con <> encloseSep lparen rparen comma (map pretty args)
  pretty (VNat i)        = integer i
  pretty (VFun _)        = text "<closure>"
  pretty (VBot)          = text "_|_"

data EvalEnv m
  = EvalEnv
  { _termEnv   :: M.Map Name (m Value)
  , _typeEnv   :: M.Map Name Value
  , _moduleEnv :: CuMin.Module
  , _stepIdx   :: Int
  }

type Eval m = Reader (EvalEnv m)

makeLenses ''EvalEnv

-- | Converts list to an arbitrary non-deterministic monad.
each :: NonDeterministic m => [a] -> m a
each = foldr (mplus . return) mzero


-- | Evaluates a CuMin expression using the denotational term semantics.
-- This function assumes that the expression and the module used as environment
-- in the Eval monad have passed the type checker before feeding them to the evaluator.
eval :: NonDeterministic m => CuMin.Exp -> Eval m (m Value)
eval (EVar var) = view $ termEnv.at var.to fromJust
eval (ELet var bnd body) = undefined
eval (ELetFree var ty body) = undefined
eval (EFailed _) = return $ return VBot
eval (EFun fun tyargs) = do
  (Binding _ args body (TyDecl tyvars _ _) _) <- view $ moduleEnv.modBinds.at fun.to fromJust
  -- build nested functions

  undefined -- TODO: lookup function in module
eval (EApp fun arg) = do
  fval <- eval fun
  aval <- eval arg
  return [f a | VFun f <- fval, a <- aval]

eval (ELit lit) = case lit of
  -- returning just the maximal element (i) of the set { _|_, i }
  LNat i -> return $ return (VNat i)

eval (EPrim PrimEq [x,y]) = undefined
eval (EPrim PrimAdd [x,y]) = undefined
-- TODO: Add future prim-ops to evaluator at this point

eval (ECon con tyargs) = undefined -- TODO: lookup constructor in moduloe
eval (ECase scrut alts) = undefined
