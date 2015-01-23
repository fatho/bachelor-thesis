{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MonadComprehensions       #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}
module FunLogic.Semantics.Denotational
  (
  -- * Abstractions
    NonDeterministic
  , Value (..)
  , Infinity (..)
  , StepIndex (..)
  -- * Interpreter Environment
  , EvalEnv (..)
  , termEnv
  , typeEnv
  , moduleEnv
  , constrEnv
  , stepIdx
  -- * Interpreter Interface
  , runEval
  , decrementStep
  , each
  , anything, anyConstructor, anyNatural
  , bindVar, bindVars, bindTyVars
  ) where

import           Control.Applicative
import           Control.Lens         hiding (each)
import           Control.Monad
import           Control.Monad.Reader
import qualified Data.Map             as M
import           Data.Maybe

import qualified FunLogic.Core.AST    as FL

-- | Encapsulates the Alternative and MonadPlus constraints to be prepared
-- for the upcoming Applicative/Monad hierarchy in GHC 7.10
type NonDeterministic m = (Alternative m, MonadPlus m)

-- | Type class to be implemented by the specific value type.
class Value (v :: (* -> *) -> *) where
  -- | Wraps a natural number into a value.
  naturalValue :: Integer -> v n
  -- | Bottom value _|_ with an optional message why the bottom value occured.
  bottomValue  :: String -> v n
  -- | Creates an ADT value with the given constructor name and arguments.
  dataValue    :: FL.DataConName -> [v n] -> v n

-- | Infinity data type used for indefinite recursions in the interpreter.
data Infinity = Infinity deriving (Eq, Ord, Enum, Bounded, Show, Read)

-- | The step index for the interpreter needs to support decrementing and checking for zero.
class StepIndex a where
  decrement :: a -> a
  isZero    :: a -> Bool

instance StepIndex Integer where
  decrement = max 0 . subtract 1
  isZero    = (== 0)

instance StepIndex Infinity where
  decrement = id
  isZero    = const False

-- | Environment needed during evaluation
data EvalEnv bnd val idx nd
  = EvalEnv
  { _termEnv   :: M.Map FL.VarName (val nd)
  -- ^ the mapping from variable names to values \sigma
  , _typeEnv   :: M.Map FL.TVName (nd (val nd))
  -- ^ the mapping from type variables to sets of value \theta
  , _moduleEnv :: FL.CoreModule bnd
  -- ^ the module providing a context for evaluating the expression
  , _constrEnv :: M.Map FL.DataConName FL.TyDecl
  -- ^ a map of data constructors with their respective types, derived from _moduleEnv.
  , _stepIdx   :: idx
  -- ^ the current step index
  }

-- | The evaluation monad is just a reader monad with the above environment.
type Eval bnd val idx n = ReaderT (EvalEnv bnd val idx n) n

-- | Required context for the Eval type parameters.
type EvalContext bnd val idx n = (FL.IsBinding bnd, Value val, StepIndex idx, NonDeterministic n)

makeLenses ''EvalEnv

-- | Run Eval computations.
runEval :: Eval bnd val idx n a -> FL.CoreModule bnd -> idx -> n a
runEval action context stepMax = runReaderT action env where
  env = EvalEnv M.empty M.empty context cns stepMax
  cns = context ^. FL.modADTs . traverse . to FL.adtConstructorTypes

-- | Decrements the step index by one in the action passed as argument
decrementStep :: (StepIndex idx, Monad n) => Eval bnd val idx n a -> Eval bnd val idx n a
decrementStep = local (stepIdx %~ decrement)

-- | Converts list to an arbitrary non-determiniTstic monad.
each :: NonDeterministic m => [a] -> m a
each = foldr (mplus . return) mzero

-- | Applies variable substitution to a type
applyTySubst :: (FL.TVName -> FL.Type) -> FL.Type -> FL.Type
applyTySubst f (FL.TVar tv) = f tv
applyTySubst f (FL.TCon n xs) = FL.TCon n $ map (applyTySubst f) xs

-- | Generates all possible inhabitants of the given type up to the step index provided by the environment.
anything :: (EvalContext bnd val idx n) => FL.Type -> Eval bnd val idx n (val n)
anything (FL.TVar tv) = view (typeEnv.at tv) >>= lift . fromMaybe (error "free type variable")
anything (FL.TFun _ _) = error "free variables cannot have a function type"
anything (FL.TNat) = fmap naturalValue anyNatural
anything (FL.TCon tycon args) = view stepIdx >>= \case
  n | isZero n -> return $ bottomValue "anything: maximum number of steps exceeded"
    | otherwise -> do
      -- read ADT constructors and generate variable substitution
      adt <- fromMaybe (error "ADT not found") <$> view (moduleEnv . FL.modADTs . at tycon)
      let subst = M.fromList $ zip (adt ^. FL.adtTyArgs) args
      -- { _|_ } `union` 1st constr. `union` 2nd constr. `union` ...
      return (bottomValue "anything")  `mplus`
        msum [ anyConstructor subst constr | constr <- adt ^. FL.adtConstr ]

-- | Generates all inhabitants of the given constructor.
anyConstructor :: (EvalContext bnd val idx n) => M.Map FL.TVName FL.Type -> FL.ConDecl -> Eval bnd val idx n (val n)
anyConstructor subst (FL.ConDecl name args) = do
  let instantiateTyVars = applyTySubst $ \tv -> fromMaybe (FL.TVar tv) (subst^.at tv)
  anyargs <- mapM (decrementStep . anything . instantiateTyVars) args
  return $ dataValue name anyargs

-- | Generate naturals up to 'stepIdx' bits.
anyNatural :: (StepIndex idx, NonDeterministic n) => Eval bnd val idx n Integer
anyNatural = pure 0 <|> go 1 where
  go n = view stepIdx >>= \idx -> do
    guard (not $ isZero idx)
    pure n
      <|> decrementStep (go $ 2*n)
      <|> decrementStep (go $ 2*n + 1)

-- | Evaluate the body with new variable bindings in the term environment
bindVar :: (MonadReader (EvalEnv bnd val idx n) m, Monad n) => FL.VarName -> val n -> m a -> m a
bindVar var val = local (termEnv %~ M.insert var val)

-- | Evaluate the body with new variable bindings in the term environment
bindVars :: (MonadReader (EvalEnv bnd val idx n) m, Monad n) => M.Map FL.VarName (val n) -> m a -> m a
bindVars vars = local (termEnv %~ M.union vars)

-- | Evaluate the body with new type variable bindings in the type environment
bindTyVars :: (MonadReader (EvalEnv bnd val idx n) m, Monad n) => M.Map FL.TVName (n (val n)) -> m a -> m a
bindTyVars tyvars = local (typeEnv %~ M.union tyvars)
