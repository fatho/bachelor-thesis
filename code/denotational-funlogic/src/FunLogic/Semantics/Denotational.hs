{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MonadComprehensions       #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}
module FunLogic.Semantics.Denotational
  (
  -- * Abstractions
    Search.MonadSearch
  , Value (..)
  , StepIndex (..)
  , PruningF
  , decrement, isZero
  -- * Interpreter Environment
  , EvalEnv (..)
  , termEnv
  , typeEnv
  , moduleEnv
  , constrEnv
  , stepIdx
  , pruningImpl
  -- * Interpreter Interface
  , runEval
  , iterDeep
  , decrementStep
  , anything, anyConstructor, anyNatural
  , bindVar, bindVars, bindTyVars
  , listEqM
  ) where

import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Control.Monad.Reader
import qualified Data.HashSet                 as HS
import qualified Data.Map                     as M
import           Data.Maybe
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified FunLogic.Core.AST            as FL
import qualified FunLogic.Semantics.Search    as Search

-- | Type class to be implemented by the specific value type.
class Value (v :: (* -> *) -> *) where
  -- | Wraps a natural number into a value.
  naturalValue :: Integer -> v n
  -- | Bottom value _|_ with an optional message why the bottom value occured.
  bottomValue  :: String -> v n
  -- | Creates an ADT value with the given constructor name, arguments and type instantiations.
  dataValue    :: FL.DataConName -> [v n] -> [FL.Type] -> v n

-- | The step index for the interpreter. Either a natural number which, when repeatedly decremented, eventually
-- reaches zero; or infinity, which, when decremented, yields infinity again.
data StepIndex
  = StepNatural Integer
  -- ^ Integer step index.
  | StepInfinity
  -- ^ Infinity step index.
  deriving (Show, Eq, Ord)

makePrisms ''StepIndex

-- | Decrements step index by one, if it's a natural number.
decrement :: StepIndex -> StepIndex
decrement = _StepNatural %~ max 0 . subtract 1

-- | Checks, if the step index has reached zero.
isZero :: StepIndex -> Bool
isZero = (== StepNatural 0)

instance PP.Pretty StepIndex where
  pretty (StepNatural n) = PP.integer n
  pretty (StepInfinity)  = PP.text "infinity"


-- | Environment needed during evaluation
data EvalEnv bnd val nd
  = EvalEnv
  { _termEnv   :: M.Map FL.VarName (val nd)
  -- ^ the mapping from variable names to values \sigma
  , _typeEnv   :: M.Map FL.TVName (StepIndex -> nd (val nd), FL.Type)
  -- ^ the mapping from type variables to sets of value \theta
  , _moduleEnv :: FL.CoreModule bnd
  -- ^ the module providing a context for evaluating the expression
  , _constrEnv :: M.Map FL.DataConName FL.TyDecl
  -- ^ a map of data constructors with their respective types, derived from _moduleEnv.
  , _stepIdx   :: StepIndex
  -- ^ the current step index
  , _pruningImpl :: PruningF nd val
  -- ^ the pruning function
  }

-- | The evaluation monad is just a reader monad with the above environment.
type Eval bnd val n = ReaderT (EvalEnv bnd val n) n

-- | Type of a pruning function taking a non-deterministic computation and returning a computation of the same type.
type PruningF n val = n (val n) -> n (val n)

makeLenses ''EvalEnv

-- | Run Eval computations.
runEval :: Eval bnd val n a -> FL.CoreModule bnd -> StepIndex -> PruningF n val -> n a
runEval action context stepMax prune = runReaderT action env where
  env = EvalEnv M.empty M.empty context cns stepMax prune
  cns = context ^. FL.modADTs . traverse . to FL.adtConstructorTypes

-- | Performs iterative deepening search on a non-deterministic evaluation.
iterDeep :: MonadPlus m => Eval bnd val m (val m) -> Eval bnd val m (val m)
iterDeep action = view stepIdx >>= go 1 where
  go idx stop
   | isZero stop = mzero
   | otherwise   = local (stepIdx .~ StepNatural idx) action `mplus` go (idx + 1) (decrement stop)

-- | Decrements the step index by one in the action passed as argument
decrementStep :: (MonadReader (EvalEnv bnd val n) m) => m a -> m a
decrementStep = local (stepIdx %~ decrement)

-- | Applies variable substitution to a type
applyTySubst :: (FL.TVName -> FL.Type) -> FL.Type -> FL.Type
applyTySubst f (FL.TVar tv) = f tv
applyTySubst f (FL.TCon n xs) = FL.TCon n $ map (applyTySubst f) xs

-- | Generates all possible inhabitants of the given type up to the step index provided by the environment.
anything :: (Value val, Search.MonadSearch n) => FL.Type -> Eval bnd val n (val n)
{-# INLINABLE anything #-}
anything = anything' HS.empty

-- | Generates all possible inhabitants of the given type up to the step index provided by the environment.
-- This function checks for left-recursion in algebraic data types and inserts bottom values appropriately to
-- allow termination.
anything' :: (Value val, Search.MonadSearch n) => HS.HashSet FL.TyConName -> FL.Type -> Eval bnd val n (val n)
{-# INLINABLE anything' #-}
anything' _  (FL.TVar tv)         = do
  si <- view stepIdx
  gen <- views (typeEnv.at tv) (maybe (error "free type variable") fst)
  lift $ gen si
anything' _  (FL.TFun _ _)        = error "free variables cannot have a function type"
anything' _  (FL.TNat)            = fmap naturalValue anyNatural
anything' vs (FL.TCon tycon args) = view stepIdx >>= \case
  n | isZero n -> return $ bottomValue "anything: maximum number of steps exceeded"
    | otherwise -> do
      -- read ADT constructors and generate variable substitution
      adt <- fromMaybe (error "ADT not found") <$> view (moduleEnv . FL.modADTs . at tycon)
      let subst = M.fromList $ zip (adt ^. FL.adtTyArgs) args
      let (con1:conRest) = adt ^. FL.adtConstr
      let vs' = HS.insert tycon vs
      -- { _|_ } `union` 1st constr. `union` 2nd constr. `union` ...
      -- fair choice out of many constructor alternatives
      (guard (tycon `HS.member` vs) >> return (bottomValue "anything"))
        `mplus` (anyConstructor vs' args subst con1
            `Search.branch` Search.branchMany [ anyConstructor vs args subst constr | constr <- conRest ] )

-- | Generates all inhabitants of the given constructor.
anyConstructor :: (Value val, Search.MonadSearch n) => HS.HashSet FL.TyConName -> [FL.Type] -> M.Map FL.TVName FL.Type -> FL.ConDecl -> Eval bnd val n (val n)
{-# INLINABLE anyConstructor #-}
anyConstructor visited ty subst (FL.ConDecl name args) = do
  let instantiateTyVars = applyTySubst $ \tv -> fromMaybe (FL.TVar tv) (subst^.at tv)
  -- evaluates all constructor arguments in an interleaved fashion
  anyargs <- Search.mapFairM (decrementStep . anything' visited . instantiateTyVars) args
  return $ dataValue name anyargs ty

{- NOTE: This variant is slower than the one below and does not provide any benefits.
-- | Generate naturals up to 'stepIdx' bits.
anyNatural :: (Search.MonadSearch n) => Eval bnd val n Integer
{-# INLINABLE anyNatural #-}
anyNatural = pure 0 <|> go 1 where
  go n = view stepIdx >>= \idx -> do
    guard (not $ isZero idx)
    -- provide a fair disjunction of bitwise-successors
    pure n <|> Search.branch
      (decrementStep $ go $ 2*n)
      (decrementStep $ go $ 2*n + 1)
-}

-- | Generate naturals up to 'stepIdx' bits.
anyNatural :: (Search.MonadSearch n) => Eval bnd val n Integer
{-# INLINABLE anyNatural #-}
anyNatural = view stepIdx >>= \case
  StepNatural n -> msum $ fmap pure [0..2^n-1]
  StepInfinity  -> msum $ fmap pure [0..]

-- | Evaluate the body with new variable bindings in the term environment
bindVar :: (MonadReader (EvalEnv bnd val n) m, Monad n) => FL.VarName -> val n -> m a -> m a
bindVar var val = local (termEnv %~ M.insert var val)

-- | Evaluate the body with new variable bindings in the term environment
bindVars :: (MonadReader (EvalEnv bnd val n) m, Monad n) => M.Map FL.VarName (val n) -> m a -> m a
bindVars vars = local (termEnv %~ M.union vars)

-- | Evaluate the body with new type variable bindings in the type environment
bindTyVars :: (MonadReader (EvalEnv bnd val n) m, Monad n) => M.Map FL.TVName (StepIndex -> n (val n), FL.Type) -> m a -> m a
bindTyVars tyvars = local (typeEnv %~ M.union tyvars)

-- | Monadic list equality test. Uses by CuMin and SaLT specific equality tests.
listEqM :: Monad m => (v -> v -> m Bool) -> [v] -> [v] -> m Bool
listEqM peq (x : xs) (y : ys) = peq x y >>= \case
  True ->  listEqM peq xs ys
  False -> return False
listEqM _ []       []         = return True
listEqM _ _        _          = error "Argument lists have different length"
