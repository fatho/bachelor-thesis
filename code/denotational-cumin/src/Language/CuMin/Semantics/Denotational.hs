{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MonadComprehensions       #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
module Language.CuMin.Semantics.Denotational
  ( -- * CuMin value type
    Value (..), boolValue, prettyValue
  -- * CuMin interpreter
  , Eval, eval, Core.runEval, Core.anything
  -- * step indices
  , Core.StepIndex (..)
  -- * further core types
  , Core.NonDeterministic
  ) where

import           Control.Applicative
import           Control.Lens                    hiding (each)
import qualified Control.Monad.Logic             as Logic
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

import qualified FunLogic.Core.Pretty            as FL
import qualified Language.CuMin.AST              as CuMin

-- | A CuMin value, parameterized over a non-deterministic Monad n.
data Value n
  = VCon CuMin.DataConName [Value n] [CuMin.Type]
  -- ^ ADT constructor
  | VNat Integer
  -- ^ natural number
  | VFun (Value n -> n (Value n)) !Unique
  -- ^ function
  | VBot String
  -- ^ bottom with an annotation, which is ignored during computation but displayed in the result

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
  (VNat n)      == (VNat m)      = n == m
  (VBot _)      == (VBot _)      = True
  (VFun _ u1)   == (VFun _ u2)   = u1 == u2
  (VCon c xs _) == (VCon d ys _) = c == d && xs == ys
  _             == _             = False

-- | Partial order of values w.r.t. to definedness.
instance PO.PartialOrd (Value n) where
  (VBot _)      `leq` _             = True
  (VNat n)      `leq` (VNat m)      = n == m
  (VFun _ u1)   `leq` (VFun _ u2)   = u1 == u2
  (VCon c xs _) `leq` (VCon d ys _) = c == d && and (zipWith PO.leq xs ys)
  _             `leq`            _  = False

-- | Arbitrary total order for Values to be used more efficiently in sets.
instance Ord (Value n) where
  (VNat n)      `compare` (VNat m)      = n `compare` m
  (VBot _)      `compare` (VBot _)      = EQ
  (VFun _ u1)   `compare` (VFun _ u2)   = u1 `compare` u2
  (VCon c xs _) `compare` (VCon d ys _) = c `compare` d <> xs `compare`ys
  x             `compare` y             = compare (rank x) (rank y) where
    rank :: Value n -> Int
    rank (VCon {})  = 0
    rank (VNat _)   = 1
    rank (VFun _ _) = 2
    rank (VBot _)   = 3

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
    VBot ann -> PP.text "_|_" -- "_|_" \x22A5
      PP.<> cond (showTypeInst && not (null ann)) (PP.enclose PP.langle PP.rangle $ PP.text ann)
  where
    cond c doc = if c then doc else PP.empty
    typeAnnot [] = PP.empty
    typeAnnot xs
      | not (null xs) && showTypeInst = PP.encloseSep (PP.text "<:") (PP.text ":>") PP.comma (map FL.prettyType xs)
      | otherwise = PP.empty

-- | If the value is actually a list, return this list
valueToList :: Value n -> Maybe [Value n]
valueToList (VCon "Nil" [] _) = Just []
valueToList (VCon "Cons" [x,xs] _) = (x:) <$> valueToList xs
valueToList _ = Nothing

type EvalEnv = Core.EvalEnv CuMin.Binding Value

-- | The evaluation monad is just a reader monad with the above environment.
type Eval n = ReaderT (EvalEnv n) n

prune :: (Search.MonadSearch n, PO.PartialOrd a) => Eval n a -> Eval n a
prune = Pruning.pruneNonMaximalN 20

-- * This specializations brought a slight performance gain, as those types are the only ones used by the REPL.
{-# SPECIALIZE Core.anything :: CuMin.Type -> Eval Logic.Logic (Value Logic.Logic) #-}
{-# SPECIALIZE Core.anything :: CuMin.Type -> Eval (Search.UnFair Logic.Logic) (Value (Search.UnFair Logic.Logic)) #-}
{-# SPECIALIZE eval :: CuMin.Exp -> Eval Logic.Logic (Value Logic.Logic) #-}
{-# SPECIALIZE eval :: CuMin.Exp -> Eval (Search.UnFair Logic.Logic) (Value (Search.UnFair Logic.Logic)) #-}

-- | Evaluates a CuMin expression using the denotational term semantics.
-- This function assumes that the expression and the module used as environment
-- in the Eval monad have passed the type checker before feeding them to the evaluator.
eval :: (Core.NonDeterministic n) => CuMin.Exp -> Eval n (Value n)
-- there is no non-determinism in the following cases:
------------------------------------------------------
eval (CuMin.EVar var) = fromMaybe (error "local variable not declared") <$> view (Core.termEnv . at var)
eval (CuMin.EFailed _) = return $ VBot "explicit failure"
eval (CuMin.ELit (CuMin.LNat nat)) = return $ Core.naturalValue nat
eval (CuMin.EFun fun tyargs) = do
  curStepIdx <- view Core.stepIdx
  if Core.isZero curStepIdx
    then return $ VBot $ "maximum number of steps exceeded when calling " ++ fun
    else do
      -- find function binding
      (CuMin.Binding _ args body (CuMin.TyDecl tyvars _ _) _)
        <- view $ Core.moduleEnv . CuMin.modBinds . at fun . to (fromMaybe $ error $ "function " ++ fun ++ " does not exist")
      -- extract environment use inside of the function value
      curEnv <- ask
      -- construct type environment for function evaluation
      let tyEnv = fmap (flip runReaderT curEnv . Core.anything) $ M.fromList $ zip tyvars tyargs
      -- build nested lambda expression
      let mkLam name rst vars = return $! mkFun $ \val -> rst (M.insert name val vars)
          mkEval vars = runReaderT (Core.decrementStep $! Core.bindVars vars $! Core.bindTyVars tyEnv $! eval body) curEnv
      lift $! List.foldr mkLam mkEval args M.empty
eval (CuMin.ECon con tyargs) = do
  (CuMin.TyDecl _ _ rawType) <- fromMaybe (error "unknown type constructor") <$> view (Core.constrEnv . at con)
  let mkLam _ rst dxs = mkFun $ \x -> return $ rst (dxs . (x:))
      mkCon _     dxs = VCon con (dxs []) tyargs
  return $! CuMin.foldFunctionType mkLam mkCon rawType id

-- the following cases need fair choice:
------------------------------------------------------
-- let (free) needs a fair choice of the bound value
eval (CuMin.ELet var bnd body) = prune $ eval bnd Search.>>+ \val -> Core.bindVar var val (eval body)
eval (CuMin.ELetFree var ty body) = prune $ Core.anything ty Search.>>+ \val -> Core.bindVar var val (eval body)
-- fair choice of caller and argument
eval (CuMin.EApp funE argE) = prune $
  Search.fairBind2 primApp (eval funE) (eval argE)
-- fair choice of prim arguments
eval (CuMin.EPrim CuMin.PrimEq [ex,ey]) = prune $
  Search.liftFairM2 primEq (eval ex) (eval ey)
eval (CuMin.EPrim CuMin.PrimAdd [ex,ey]) = prune $
  Search.liftFairM2 primAdd (eval ex) (eval ey)
-- REMARK: Add future prim-ops to evaluator at this point
eval (CuMin.EPrim _ _) = error "illegal primitive operation call"
-- fair choice of scrutinee
eval (CuMin.ECase scrut alts) = prune $
  eval scrut Search.>>+ \scrutVal -> patternMatch scrutVal alts

-- | Creates a new function value with a unique ID.
-- Uses unsafePerformIO internally.
mkFun :: (Value n -> n (Value n)) -> Value n
mkFun f = UIO.unsafePerformIO $ VFun f <$> newUnique

-- | Matches the given value against the list of case alternatives and evaluates it.
patternMatch :: (Core.NonDeterministic n) => Value n -> [CuMin.Alt] -> Eval n (Value n)
patternMatch (VBot x)   _ = return $ VBot x
patternMatch (VNat _)   _ = error "cannot pattern match on Nat"
patternMatch (VFun _ _) _ = error "cannot pattern match on functions"
patternMatch con@(VCon cname args _) alts = case List.find (matches cname) alts of
  Nothing -> return $ VBot "incomplete pattern match"
  -- catch all pattern: bind scrutinee to name
  Just (CuMin.Alt (CuMin.PVar v) body) -> Core.bindVar v con $ eval body
  -- constructor pattern: bind arguments to names
  Just (CuMin.Alt (CuMin.PCon _ vs) body)
    | length vs == length args -> Core.bindVars (M.fromList $ zip vs args) $ eval body
    | otherwise -> error "number constructor arguments does not match the pattern"

-- | Checks if a pattern matches a constructor
matches :: CuMin.DataConName -> CuMin.Alt -> Bool
matches _     (CuMin.Alt (CuMin.PVar _) _) = True
matches cname (CuMin.Alt (CuMin.PCon pname _) _) = cname == pname

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
primApp :: Core.NonDeterministic n => Value n -> Value n -> Eval n (Value n)
primApp (VFun f _) a = lift $ f a
primApp (VBot n) _ = return $ VBot n
primApp _ _ = error "application of non-function type"
