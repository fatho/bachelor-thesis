{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MonadComprehensions       #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TemplateHaskell           #-}
module Language.SaLT.Semantics.Denotational
  ( -- * SaLT value type
    Value (..), boolValue
  -- * SaLT interpreter
  , EvalExp, eval, runEval, unknown, mapValueSet
  -- * step indices
  , Core.Infinity (..)
  , Core.StepIndex (..)
  ) where

import           Control.Applicative
import           Control.Lens                    hiding (each)
import           Control.Monad.Reader
import qualified Data.Foldable                   as F
import qualified Data.List                       as List
import qualified Data.Map                        as M
import           Data.Maybe
import           Data.Monoid
import           Data.Unique
import qualified System.IO.Unsafe                as UIO
import qualified Text.PrettyPrint.ANSI.Leijen    as PP

import qualified FunLogic.Semantics.Denotational as Core
import qualified FunLogic.Semantics.PartialOrder as PO

import qualified Language.SaLT.AST               as SaLT

-- | A SaLT value, parameterized over a non-deterministic Monad n.
data Value n
  = VCon SaLT.DataConName [Value n]
  -- ^ ADT constructor
  | VNat Integer
  -- ^ natural number
  | VFun (Value n -> Value n) !Unique
  -- ^ function
  | VBot String
  -- ^ bottom with an annotation, which is ignored during computation but displayed in the result
  | VSet (n (Value n)) !Unique
  -- ^ explicit set

makePrisms ''Value

-- | Transforms the underlying set of the value. Transformations are needed in both directions because of VFun.
mapValueSet :: (Functor m, Functor n) => (forall a. m a -> n a) -> (forall a. n a -> m a) -> Value n -> Value m
mapValueSet g f (VCon c xs)  = VCon c (map (mapValueSet g f) xs)
mapValueSet g f (VFun fun u) = VFun (mapValueSet g f . fun . mapValueSet f g) u
mapValueSet g f (VSet vs u)  = VSet (mapValueSet g f <$> f vs) u
mapValueSet _ _ (VNat n)     = VNat n
mapValueSet _ _ (VBot msg)   = VBot msg

-- | Wraps a bool in a Value.
boolValue :: Bool -> Value n
boolValue False = VCon "False" []
boolValue True = VCon "True" []

instance Core.Value Value where
  naturalValue = VNat
  bottomValue = VBot
  dataValue = VCon

-- | Equality w.r.t. to the partial order.
instance Eq (Value n) where
  (VNat n)    == (VNat m)    = n == m
  (VBot _)    == (VBot _)    = True
  (VFun _ u1) == (VFun _ u2) = u1 == u2
  (VCon c xs) == (VCon d ys) = c == d && xs == ys
  _           == _           = False

-- | Partial order of values w.r.t. to definedness.
instance PO.PartialOrd (Value n) where
  -- _|_ is the minimal element
  (VBot _) `leq` _ = True
  -- two naturals are only compatible if they're equal
  (VNat n) `leq` (VNat m) = n == m
  -- same as above
  (VFun _ u1) `leq` (VFun _ u2) = u1 == u2
  (VSet _ u1) `leq` (VSet _ u2) = u1 == u2
  (VCon c xs) `leq` (VCon d ys) = c == d && and (zipWith PO.leq xs ys)
  _           `leq`           _ = False

-- | Arbitrary total order for Values to be used more efficiently in sets.
instance Ord (Value n) where
  (VNat n)    `compare` (VNat m)    = n `compare` m
  (VBot _)    `compare` (VBot _)    = EQ
  (VFun _ u1) `compare` (VFun _ u2) = u1 `compare` u2
  (VCon c xs) `compare` (VCon d ys) = c `compare` d <> xs `compare`ys
  (VSet _ u1) `compare` (VSet _ u2) = u1 `compare` u2
  x           `compare` y           = compare (rank x) (rank y) where
    rank :: Value n -> Int
    rank (VCon _ _) = 0
    rank (VNat _)   = 1
    rank (VFun _ _) = 2
    rank (VBot _)   = 3
    rank (VSet _ _) = 4

instance F.Foldable n => PP.Pretty (Value n) where
  pretty val@(VCon con args) = case valueToList val of
    Nothing
      | null args -> PP.text con
      | otherwise -> PP.text con PP.<> PP.encloseSep PP.lparen PP.rparen PP.comma (map PP.pretty args)
    Just list -> PP.prettyList list
  pretty (VNat i)        = PP.integer i
  pretty (VFun _ uid)    = PP.text "<closure:" PP.<> PP.int (hashUnique uid) PP.<> PP.text ">"
  pretty (VBot ann)      = PP.text "\x22A5"
    PP.<> if null ann then PP.empty else PP.enclose PP.langle PP.rangle $ PP.text ann -- "_|_"
  pretty (VSet vs _)    = PP.encloseSep PP.lbrace PP.rbrace PP.comma
                             (F.foldr (\val xs -> PP.pretty val : xs) [] vs)

-- | If the value is acutally a list, return this list
valueToList :: Value n -> Maybe [Value n]
valueToList (VCon "Nil" []) = Just []
valueToList (VCon "Cons" [x,xs]) = (x:) <$> valueToList xs
valueToList _ = Nothing

type EvalEnv = Core.EvalEnv SaLT.Binding Value

-- | Evaluation monad with explicit non-determinism via VSet (Value)
type EvalExp idx n = ReaderT (EvalEnv idx n) Identity

-- | Run Eval computations.
runEval :: EvalExp idx n a -> SaLT.Module -> idx -> a
runEval action context stepMax = runReader action env where
  env = Core.EvalEnv M.empty M.empty context cns stepMax
  cns = context ^. SaLT.modADTs . traverse . to SaLT.adtConstructorTypes

-- | Returns all possible inhabitants of a type as a set.
unknown :: (Core.StepIndex idx, Core.NonDeterministic n) => SaLT.Type -> EvalExp idx n (Value n)
unknown = captureNonDet . Core.anything

-- | Takes a non-deterministic evaluation and transforms it into an evaluation with explicit non-determinism.
captureNonDet :: Applicative n => ReaderT e n (Value n) -> Reader e (Value n)
captureNonDet = mapReaderT (Identity . mkSet)

-- | Evaluates a SaLT expression using the denotational term semantics.
-- This function assumes that the expression and the module used as environment
-- in the Eval monad have passed the type checker before feeding them to the evaluator.
eval :: (Core.StepIndex idx, Core.NonDeterministic n) => SaLT.Exp -> EvalExp idx n (Value n)
eval (SaLT.EVar var) = view (Core.termEnv . at var) >>= \case
  Just val -> return val
  Nothing  -> error "local variable not declared"
eval (SaLT.EPrim prim args) = mapM eval args >>= evalPrim prim
eval (SaLT.ELit (SaLT.LNat n)) = return $ Core.naturalValue n
eval (SaLT.ESet valE) = mkSetSingleton <$> eval valE
eval (SaLT.EFailed _) = return $ VBot "explicit failure"
eval (SaLT.EUnknown ty) = unknown ty
eval (SaLT.EApp funE argE) = primApp <$> eval funE <*> eval argE
eval (SaLT.EFun fun tyargs) = do
  curStepIdx <- view Core.stepIdx
  if Core.isZero curStepIdx
    then return $ VBot $ "maximum number of steps exceeded when calling " ++ fun
    else do
      (SaLT.Binding _ body (SaLT.TyDecl tyvars _ _) _) <- view $ Core.moduleEnv . SaLT.modBinds . at fun . to fromJust
      -- evaluate type environment
      curEnv <- ask
      let tyEnv = fmap (flip runReaderT curEnv . Core.anything) $ M.fromList $ zip tyvars tyargs
      -- evaluate body
      Core.bindTyVars tyEnv $ eval body
eval (SaLT.ELam argName _ body) = do
  curEnv <- ask
  return $ mkFun $ \v -> flip runReader curEnv $ Core.bindVar argName v (eval body)
eval (SaLT.ECon con _) = do
  (SaLT.TyDecl _ _ rawType) <- fromMaybe (error "unknown type constructor") <$> view (Core.constrEnv . at con)
  let f _ rst dxs = mkFun $ \x -> rst (dxs . (x:))
      g _     dxs = VCon con (dxs [])
  return $ SaLT.foldFunctionType f g rawType id
eval (SaLT.ECase scrut alts) = do
  scrutVal <- eval scrut
  patternMatch scrutVal alts

-- | Creates a new function value with a unique ID.
-- Uses unsafePerformIO internally.
mkFun :: (Value n -> Value n) -> Value n
mkFun f = UIO.unsafePerformIO $ VFun f <$> newUnique

-- | Constructs a singleton set value.
mkSet :: Applicative n => n (Value n) -> Value n
mkSet vs = UIO.unsafePerformIO $ VSet vs <$> newUnique

-- | Constructs a singleton set value.
mkSetSingleton :: Applicative n => Value n -> Value n
mkSetSingleton = mkSet . pure

-- | Matches the given value against the list of case alternatives and evaluates it.
patternMatch :: (Core.StepIndex idx, Core.NonDeterministic n) => Value n -> [SaLT.Alt] -> EvalExp idx n (Value n)
patternMatch (VBot x)   _ = return $ VBot x
patternMatch (VNat _)   _ = error "cannot pattern match on Nat"
patternMatch (VFun _ _) _ = error "cannot pattern match on functions"
patternMatch (VSet _ _) _ = error "cannot pattern match on sets"
patternMatch con@(VCon cname args) alts = case List.find (matches cname) alts of
  Nothing -> return $ VBot "incomplete pattern match"
  -- catch all pattern: bind scrutinee to name
  Just (SaLT.Alt (SaLT.PVar v) body) -> Core.bindVar v con $ eval body
  -- constructor pattern: bind arguments to names
  Just (SaLT.Alt (SaLT.PCon _ vs) body)
    | length vs == length args -> Core.bindVars (M.fromList $ zip vs args) $ eval body
    | otherwise -> error "number constructor arguments does not match the pattern"

-- | Checks if a pattern matches a constructor
matches :: SaLT.DataConName -> SaLT.Alt -> Bool
matches _ (SaLT.Alt (SaLT.PVar _) _) = True
matches cname (SaLT.Alt (SaLT.PCon pname _) _) = cname == pname

evalPrim :: (Core.NonDeterministic n) => SaLT.PrimOp -> [Value n] -> EvalExp idx n (Value n)
evalPrim prim [x,y] = return $ primOp prim x y
evalPrim _ _        = error "evalPrim: invalid number of arguments for primitive operation"

primOp :: (Core.NonDeterministic n) => SaLT.PrimOp -> Value n -> Value n -> Value n
primOp SaLT.PrimAdd  = primAdd
primOp SaLT.PrimEq   = primEq
primOp SaLT.PrimBind = primBind

-- | Primitve monadic bind on sets.
primBind :: (Core.NonDeterministic n) => Value n -> Value n -> Value n
primBind (VSet vs _) (VFun f _) = mkSet $ vs >>= \val -> case f val of
  VSet rs _ -> rs
  VBot _    -> mzero
  _         -> error ">>= : type error"
primBind _ _ = error ">>= : wrong arguments"

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
primApp :: Core.NonDeterministic n => Value n -> Value n -> Value n
primApp (VFun f _) a = f a
primApp (VBot n) _ = VBot n
primApp _ _ = error "application of non-function type"
