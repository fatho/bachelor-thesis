{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MonadComprehensions       #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
module Language.CuMin.Semantics.Denotational
  ( -- * CuMin value type
    Value (..), boolValue
  -- * CuMin interpreter
  , Eval, eval, Core.runEval, Core.anything
  -- * step indices
  , Core.Infinity (..)
  , Core.StepIndex (..)
  ) where

import           Control.Applicative
import           Control.Lens                    hiding (each)
import           Control.Monad
import           Control.Monad.Reader
import qualified Data.List                       as List
import qualified Data.Map                        as M
import           Data.Maybe
import qualified Text.PrettyPrint.ANSI.Leijen    as PP

import qualified FunLogic.Semantics.Denotational as Core

import qualified Language.CuMin.AST              as CuMin
import qualified Language.CuMin.TypeChecker      as CuMin

import qualified Debug.Trace                     as Debug

-- | A CuMin value, parameterized over a non-deterministic Monad n.
data Value n
  = VCon CuMin.DataConName [Value n]
  -- ^ ADT constructor
  | VNat Integer
  -- ^ natural number
  | VFun (Value n -> n (Value n))
  -- ^ function
  | VBot String
  -- ^ bottom with an annotation, which is ignored during computation but displayed in the result

-- | Wraps a bool in a Value.
boolValue :: Bool -> Value n
boolValue False = VCon "False" []
boolValue True = VCon "True" []

instance Core.Value Value where
  naturalValue = VNat
  bottomValue = VBot
  dataValue = VCon

instance PP.Pretty (Value n) where
  pretty (VCon con []) = PP.text con
  pretty (VCon con args) = PP.text con PP.<> PP.encloseSep PP.lparen PP.rparen PP.comma (map PP.pretty args)
  pretty (VNat i)        = PP.integer i
  pretty (VFun _)        = PP.text "<closure>"
  pretty (VBot ann)      = PP.text "\x22A5"
    PP.<> if null ann then PP.empty else PP.enclose PP.langle PP.rangle $ PP.text ann -- "_|_"

type EvalEnv = Core.EvalEnv CuMin.Binding Value

-- | The evaluation monad is just a reader monad with the above environment.
type Eval idx n = ReaderT (EvalEnv idx n) n

-- | Evaluates a CuMin expression using the denotational term semantics.
-- This function assumes that the expression and the module used as environment
-- in the Eval monad have passed the type checker before feeding them to the evaluator.
eval :: (Core.StepIndex idx, Core.NonDeterministic n) => CuMin.Exp -> Eval idx n (Value n)
eval (CuMin.EVar var) = view (Core.termEnv . at var) >>= \case
  Just val -> return val
  Nothing -> error "local variable not declared"
eval (CuMin.ELet var bnd body) = eval bnd >>= \val -> Core.bindVar var val (eval body)
eval (CuMin.ELetFree var ty body) = Core.anything ty >>= \val -> Core.bindVar var val (eval body)
eval (CuMin.EFailed _) = return $ VBot "explicit failure"
eval (CuMin.EFun fun tyargs) = do
  curStepIdx <- view Core.stepIdx
  if Core.isZero curStepIdx
    then return $ VBot $ "maximum number of steps exceeded when calling " ++ fun
    else do
      (CuMin.Binding _ args body (CuMin.TyDecl tyvars _ _) _) <- view $ Core.moduleEnv . CuMin.modBinds . at fun . to fromJust
      curEnv <- ask
      let tyEnv = fmap (flip runReaderT curEnv . Core.anything) $ M.fromList $ zip tyvars tyargs
      let f name rst vars = return $ VFun $ \val -> rst (M.insert name val vars)
          g vars = runReaderT (Core.decrementStep $ Core.bindVars vars $ Core.bindTyVars tyEnv $ eval body) curEnv
      lift $ foldr f g args M.empty
eval (CuMin.EApp fun arg) =
  join $ liftM2 primApp (eval fun) (eval arg)

eval (CuMin.ELit (CuMin.LNat nat)) = return $ Core.naturalValue nat

eval (CuMin.EPrim CuMin.PrimEq [ex,ey]) =
  liftM2 primEq (eval ex) (eval ey)
eval (CuMin.EPrim CuMin.PrimAdd [ex,ey]) =
  liftM2 primAdd (eval ex) (eval ey)
eval (CuMin.EPrim _ _) = error "illegal primitive operation call"
-- REMARK: Add future prim-ops to evaluator at this point

eval (CuMin.ECon con tyargs) = do
  tydecl <- fromMaybe (error "unknown type constructor") <$> view (Core.constrEnv . at con)
  case CuMin.instantiate' tyargs tydecl :: Either (CuMin.TCErr CuMin.CuMinErrCtx) CuMin.Type of
    Left err -> error $ show tyargs ++ "\n" ++ show tydecl ++ "\ntype error when instantiating constructor: "
      ++ show (PP.plain $ PP.pretty err)
    Right inst ->
      let f _ rst dxs = VFun $ \x -> return $ rst (dxs . (x:))
          g _     dxs = VCon con (dxs [])
      in return $ CuMin.foldFunctionType f g inst id
eval (CuMin.ECase scrut alts) = do
  scrutVal <- eval scrut
  patternMatch scrutVal alts

-- | Matches the given value against the list of case alternatives and evaluates it.
patternMatch :: (Core.StepIndex idx, Core.NonDeterministic n) => Value n -> [CuMin.Alt] -> Eval idx n (Value n)
patternMatch (VBot x) _ = return $ VBot x
patternMatch (VNat _) _ = error "cannot pattern match on Nat"
patternMatch (VFun _) _ = error "cannot pattern match on functions"
patternMatch con@(VCon cname args) alts = case List.find (matches cname) alts of
  Nothing -> return $ VBot "incomplete pattern match"
  -- catch all pattern: bind scrutinee to name
  Just (CuMin.Alt (CuMin.PVar v) body) -> Core.bindVar v con $ eval body
  -- constructor pattern: bind arguments to names
  Just (CuMin.Alt (CuMin.PCon _ vs) body)
    | length vs == length args -> Core.bindVars (M.fromList $ zip vs args) $ eval body
    | otherwise -> error "number constructor arguments does not match the pattern"

-- | Checks if a pattern matches a constructor
matches :: CuMin.DataConName -> CuMin.Alt -> Bool
matches _ (CuMin.Alt (CuMin.PVar _) _) = True
matches cname (CuMin.Alt (CuMin.PCon pname _) _) = cname == pname

-- | Primitive equality operator which is built-in for naturals.
primEq :: Value n -> Value n -> Value n
primEq (VNat n) (VNat m) = boolValue $ n == m
primEq (VBot n) (VNat _) = VBot n
primEq (VNat _) (VBot n) = VBot n
primEq (VBot n) (VBot _) = VBot n
primEq _ _ = error "primEq: wrong type"

-- | Primitive addition which is built-in for naturals.
primAdd :: Value n -> Value n -> Value n
primAdd (VNat n) (VNat m) = VNat $ n + m
primAdd (VBot n) (VNat _) = VBot n
primAdd (VNat _) (VBot n) = VBot n
primAdd (VBot n) (VBot _) = VBot n
primAdd _ _ = error "primAdd: wrong type"

-- | Function application lifted to values.
primApp :: Core.NonDeterministic n => Value n -> Value n -> Eval idx n (Value n)
primApp (VFun f) a = lift $ f a
primApp (VBot n) _ = return $ VBot n
primApp _ _ = error "application of non-function type"
