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
    Value (..), boolValue, prettyValue, mkSet
  -- * SaLT interpreter
  , EvalExp, eval, runEval, unknown, mapValueSet
  , EvalEnv, Core.stepIdx, Core.termEnv, Core.typeEnv, Core.moduleEnv, Core.constrEnv
  -- * step indices
  , Core.StepIndex (..), Core.isZero, Core.decrement
  -- * further core types
  , Search.MonadSearch
  , Core.PruningF
  ) where

import           Control.Applicative
import           Control.Arrow                   ((&&&))
import           Control.Lens                    hiding (each)
import           Control.Monad.Reader
import qualified Data.List                       as List
import qualified Data.Map                        as M
import           Data.Maybe
import           Data.Monoid
import           Data.Unique
import qualified System.IO.Unsafe                as UIO
import qualified Text.PrettyPrint.ANSI.Leijen    as PP

import qualified FunLogic.Semantics.Denotational as Core
import qualified FunLogic.Semantics.PartialOrder as PO
import qualified FunLogic.Semantics.Pruning      as Pruning
import qualified FunLogic.Semantics.Search       as Search

import qualified FunLogic.Core                   as FL
import qualified Language.SaLT                   as SaLT

-- | A SaLT value, parameterized over a non-deterministic Monad n.
data Value n
  = VCon SaLT.DataConName [Value n] [SaLT.Type]
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
mapValueSet g f (VCon c xs ty) = VCon c (map (mapValueSet g f) xs) ty
mapValueSet g f (VFun fun u)   = VFun (mapValueSet g f . fun . mapValueSet f g) u
mapValueSet g f (VSet vs u)    = VSet (mapValueSet g f <$> f vs) u
mapValueSet _ _ (VNat n)       = VNat n
mapValueSet _ _ (VBot msg)     = VBot msg

-- | Wraps a bool in a Value.
boolValue :: Bool -> Value n
boolValue False = VCon "False" [] []
boolValue True = VCon "True" [] []

instance Core.Value Value where
  naturalValue = VNat
  bottomValue = VBot
  dataValue = VCon

-- | Equality w.r.t. to the partial order.
instance Eq (Value n) where
  (VNat n)    == (VNat m)    = n == m
  (VBot _)    == (VBot _)    = True
  (VFun _ u1) == (VFun _ u2) = u1 == u2
  (VCon c xs _) == (VCon d ys _) = c == d && xs == ys
  _           == _           = False

-- | Partial order of values w.r.t. to definedness.
instance PO.PartialOrd (Value n) where
  -- _|_ is the minimal element
  (VBot _) `leq` _ = True
  -- two naturals are only compatible if they're equal
  (VNat n) `leq` (VNat m) = n == m
  -- same as above
  (VFun _ u1)   `leq` (VFun _ u2)   = u1 == u2
  (VSet _ u1)   `leq` (VSet _ u2)   = u1 == u2
  (VCon c xs _) `leq` (VCon d ys _) = c == d && and (zipWith PO.leq xs ys)
  _             `leq`           _   = False

-- | Arbitrary total order for Values to be used more efficiently in sets.
instance Ord (Value n) where
  (VNat n)      `compare` (VNat m)      = n `compare` m
  (VBot _)      `compare` (VBot _)      = EQ
  (VFun _ u1)   `compare` (VFun _ u2)   = u1 `compare` u2
  (VCon c xs _) `compare` (VCon d ys _) = c `compare` d <> xs `compare`ys
  (VSet _ u1)   `compare` (VSet _ u2)   = u1 `compare` u2
  x             `compare` y             = compare (rank x) (rank y) where
    rank :: Value n -> Int
    rank (VCon _ _ _) = 0
    rank (VNat _)   = 1
    rank (VFun _ _) = 2
    rank (VBot _)   = 3
    rank (VSet _ _) = 4

instance PP.Pretty (Value n) where
  pretty = prettyValue False

instance Show (Value n) where
  show = show . PP.plain . prettyValue False

-- | Pretty-prints a value. The bool parameter controls whether type instantiations should be displayed or not.
prettyValue :: Bool -> Value n -> PP.Doc
prettyValue showTypeInst val = case val of
    VCon name args inst
      | null args -> PP.text name PP.<> typeAnnot inst
      | otherwise -> case valueToList val of
          Nothing -> PP.text name PP.<> typeAnnot inst
                        PP.<> PP.encloseSep PP.lparen PP.rparen PP.comma (map PP.pretty args)
          Just list -> PP.prettyList list PP.<> typeAnnot inst
    VNat i -> PP.integer i
    VFun _ uid -> PP.text "<closure:" PP.<> PP.int (hashUnique uid) PP.<> PP.text ">"
    VSet _ uid -> PP.text "<set:" PP.<> PP.int (hashUnique uid) PP.<> PP.text ">"
    VBot ann -> PP.text "\x22A5" -- "_|_"
      PP.<> cond (showTypeInst && not (null ann)) (PP.enclose PP.langle PP.rangle $ PP.text ann)
  where
    cond c doc = if c then doc else PP.empty
    typeAnnot [] = PP.empty
    typeAnnot xs
      | not (null xs) && showTypeInst = PP.encloseSep (PP.text "<:") (PP.text ":>") PP.comma (map FL.prettyType xs)
      | otherwise = PP.empty

-- | If the value is acutally a list, return this list
valueToList :: Value n -> Maybe [Value n]
valueToList (VCon "Nil" [] _) = Just []
valueToList (VCon "Cons" [x,xs] _) = (x:) <$> valueToList xs
valueToList _ = Nothing

type EvalEnv = Core.EvalEnv SaLT.Binding Value

-- | Evaluation monad with explicit non-determinism via 'VSet' (Value)
type EvalExp n = ReaderT (EvalEnv n) Identity

-- | Run Eval computations.
runEval :: EvalExp n a -> SaLT.Module -> Core.StepIndex -> Core.PruningF n Value -> a
runEval action context stepMax prune = runReader action env where
  env = Core.EvalEnv M.empty M.empty context cns stepMax prune
  cns = context ^. SaLT.modADTs . traverse . to SaLT.adtConstructorTypes

-- | Returns all possible inhabitants of a type as a set.
unknown :: (Search.MonadSearch n) => SaLT.Type -> EvalExp n (Value n)
unknown = captureNonDet . Core.anything

-- | Returns the least element of a given type.
-- For a sets, this is the singleton set containing the least element of the element type,
-- for every other data type, this is the explicit _|_ element.
bottomOf :: Applicative n => SaLT.Type -> Value n
bottomOf (SaLT.TCon "Set" [ty]) = mkSetSingleton $ bottomOf ty
bottomOf _                      = VBot "failed"

-- | Takes a non-deterministic evaluation and transforms it into an evaluation with explicit non-determinism.
captureNonDet :: Applicative n => ReaderT e n (Value n) -> Reader e (Value n)
captureNonDet = mapReaderT (Identity . mkSet)

-- | Evaluates a SaLT expression using the denotational term semantics.
-- This function assumes that the expression and the module used as environment
-- in the Eval monad have passed the type checker before feeding them to the evaluator.
eval :: (Search.MonadSearch n) => SaLT.Exp -> EvalExp n (Value n)
-- there is no non-determinism in the following cases:
------------------------------------------------------
eval (SaLT.EVar var) = fromMaybe (error "local variable not declared") <$> view (Core.termEnv . at var)
eval (SaLT.ELit (SaLT.LNat n)) = return $ Core.naturalValue n
eval (SaLT.ESet valE) = mkSetSingleton <$> eval valE
eval (SaLT.EFailed ty) = return $ bottomOf ty
eval (SaLT.EUnknown ty) = unknown ty
eval (SaLT.EPrim prim args) = mapM eval args >>= evalPrim prim
eval (SaLT.EApp funE argE) = liftM2 primApp (eval funE) (eval argE)
eval (SaLT.ECase scrut alts) = do
  scrutVal <- eval scrut
  patternMatch scrutVal alts
eval (SaLT.EFun fun tyargs) = do
  curStepIdx <- view Core.stepIdx
  if Core.isZero curStepIdx
    then return $  VBot $ "maximum number of steps exceeded when calling " ++ fun
    else do
      (SaLT.Binding _ body (SaLT.TyDecl tyvars _ _) _) <- view $ Core.moduleEnv . SaLT.modBinds . at fun . to fromJust
      -- evaluate type environment
      curEnv <- ask
      let tyEnv = fmap (flip runReaderT curEnv . Core.anything &&& id) $ M.fromList $ zip tyvars tyargs
      -- evaluate body
      Core.decrementStep $ Core.bindTyVars tyEnv $ eval body
eval (SaLT.ECon con tys) = do
  (SaLT.TyDecl _ _ rawType) <- fromMaybe (error "unknown type constructor") <$> view (Core.constrEnv . at con)
  tyEnv <- view Core.typeEnv
  let tySubst v = views (at v) (maybe (FL.TVar v) snd) tyEnv
  let tyInst = map (FL.foldType FL.TCon tySubst) tys
  let f _ rst dxs = mkFun $ \x -> rst (dxs . (x:))
      g _     dxs = VCon con (dxs []) tyInst
  return $ SaLT.foldFunctionType f g rawType id
eval (SaLT.ELam argName _ body) = do
  curEnv <- ask
  return $ mkFun $ \v -> flip runReader curEnv $ Core.bindVar argName v (eval body)

-- | Creates a new function value with a unique ID.
-- Uses unsafePerformIO internally.
mkFun :: (Value n -> Value n) -> Value n
mkFun f = UIO.unsafePerformIO $ VFun f <$> newUnique

-- | Constructs a singleton set value.
-- Uses unsafePerformIO internally.
mkSet :: Applicative n => n (Value n) -> Value n
mkSet vs = UIO.unsafePerformIO $ VSet vs <$> newUnique

-- | Constructs a singleton set value.
-- Uses unsafePerformIO internally.
mkSetSingleton :: Applicative n => Value n -> Value n
mkSetSingleton = mkSet . pure

-- | Matches the given value against the list of case alternatives and evaluates it.
patternMatch :: (Search.MonadSearch n) => Value n -> [SaLT.Alt] -> EvalExp n (Value n)
patternMatch (VBot x)   _ = return $ VBot x
patternMatch (VNat _)   _ = error "cannot pattern match on Nat"
patternMatch (VFun _ _) _ = error "cannot pattern match on functions"
patternMatch (VSet _ _) _ = error "cannot pattern match on sets"
patternMatch con@(VCon cname args _) alts = case List.find (matches cname) alts of
  Nothing -> error "incomplete pattern match"
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

evalPrim :: (Search.MonadSearch n) => SaLT.PrimOp -> [Value n] -> EvalExp n (Value n)
evalPrim SaLT.PrimAdd  [x,y] = return $ primAdd x y
evalPrim SaLT.PrimEq   [x,y] = return $ primEq x y
evalPrim SaLT.PrimBind [x,y] = do
  prune <- view Core.pruningImpl
  return $ primBind prune x y
evalPrim _ _        = error "evalPrim: invalid number of arguments for primitive operation"

-- | Primitve monadic bind on sets. Uses fair conjunction.
primBind :: (Search.MonadSearch n) => Core.PruningF n Value -> Value n -> Value n -> Value n
primBind prune (VSet vs _) (VFun f _) = mkSet $ prune $ vs Search.>>+ \val -> case f val of
  VSet rs _ -> rs
  VBot v    -> return $ VBot v
  _         -> error ">>= : type error 1"
primBind _ _ (VBot s) = mkSet $ return $ VBot s
primBind _ (VBot s) (VFun f _) = mkSet $ case f $ VBot s of
  VSet rs _ -> rs
  VBot v    -> return $ VBot v
  _         -> error ">>= : type error 2"
primBind _ _ _ = error ">>= : wrong arguments"

-- | Primitive equality operator which is built-in for naturals.
primEq :: Value n -> Value n -> Value n
primEq x y = either VBot boolValue $ primEq' x y

primEq' :: Value n -> Value n -> Either String Bool
primEq' (VNat n) (VNat m) = Right $ n == m
primEq' (VBot n) _        = Left n
primEq' _        (VBot n) = Left n
primEq' (VCon c1 xs _) (VCon c2 ys _)
  | c1 == c2  = Core.listEqM primEq' xs ys
  | otherwise = Right False
primEq' _ _ = error "primEq: wrong type"

-- | Primitive addition which is built-in for naturals.
primAdd :: Value n -> Value n -> Value n
primAdd (VNat n) (VNat m) = VNat $ n + m
primAdd (VBot n) (VNat _) = VBot n
primAdd (VNat _) (VBot n) = VBot n
primAdd (VBot n) (VBot _) = VBot n
primAdd _ _ = error "primAdd: wrong type"

-- | Function application lifted to values.
primApp :: Search.MonadSearch n => Value n -> Value n -> Value n
primApp (VFun f _) a = f a
primApp (VBot n) _ = VBot n
primApp _ _ = error "application of non-function type"
