{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
module FunLogic.Semantics.Search where

import           Control.Applicative
import           Control.Monad
import qualified Control.Monad.Logic  as Logic
import           Control.Monad.Reader

-- | Monads supporting non-deterministic fair search.
-- This custom search class is needed, because the 'MonadLogic' instance of 'ReaderT' does not respect the overriden
-- implementations of 'interleave' and '>>-' in the base monad.
class (Alternative m, MonadPlus m) => MonadSearch m where
  -- | "Peek" at one result at a time.
  peek :: m a -> m (Maybe (a, m a))
  -- | Fair disjunction between two branches
  branch :: m a -> m a -> m a
  -- | Fair conjunction.
  (>>?)  :: m a -> (a -> m b) -> m b

instance Monad m => MonadSearch (Logic.LogicT m) where
  peek   = Logic.msplit
  branch = Logic.interleave
  (>>?)  = (Logic.>>-)

instance MonadSearch m => MonadSearch (ReaderT s m) where
  peek rm = ReaderT $ \e -> do
    r <- peek $ runReaderT rm e
    case r of
      Nothing -> return Nothing
      Just (a, m) -> return (Just (a, lift m))

  branch ma mb = ReaderT $ \r ->
    runReaderT ma r `branch` runReaderT mb r

  ma >>? f = ReaderT $ \s ->
    runReaderT ma s >>? \a -> runReaderT (f a) s


-- | A class of non-deterministic monads with observable results.
class Observable m where
  -- | Observe all results in a (lazy, if possible) list.
  observeAll :: m a -> [a]

  -- | Observes the first 'n' results.
  observeMany :: Int -> m a -> [a]
  observeMany n = take n . observeAll

  -- | Observes one result.
  observe :: m a -> a
  observe = head . observeAll

instance Observable Logic.Logic where
  observe     = Logic.observe
  observeAll  = Logic.observeAll
  observeMany = Logic.observeMany

instance Observable [] where
  observe     = head
  observeMany = take
  observeAll  = id

-- | A monad-wrapper that overrides the 'MonadSearch' instance with the combinators of 'MonadPlus', i.e. 'mplus' and
-- 'mzero', which - in most cases - are implemented as a depth-first/unfair search.
newtype UnFair m a = UnFair { fair :: m a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus)

instance MonadTrans UnFair where
  lift = UnFair

instance (Alternative m, MonadPlus m, MonadSearch m) => MonadSearch (UnFair m) where
  peek rm = UnFair $ peek (fair rm) >>= \case
    Nothing -> return Nothing
    Just (a, m) -> return (Just (a, lift m))
  branch = mplus
  (>>?) = (>>=)

instance Observable m => Observable (UnFair m) where
  observe       = observe . fair
  observeAll    = observeAll . fair
  observeMany n = observeMany n . fair

-- | Like 'mapM', but with fair conjunction
mapFairM :: MonadSearch m => (a -> m b) -> [a] -> m [b]
mapFairM f = go where
  go []     = return []
  go (x:xs) = f x >>? \b -> (b:) `liftM` go xs

-- | Like 'msum', but with fair disjunction.
branchMany :: MonadSearch m => [m a] -> m a
branchMany = foldr branch mzero

-- | Like 'liftM', but with fair conjunction.
liftFairM2 :: MonadSearch m => (a -> b -> c) -> m a -> m b -> m c
liftFairM2 f = fairBind2 (\a b -> return $ f a b)

-- | A fair bind over two monadic values.
fairBind2 :: MonadSearch m => (a -> b -> m c) -> m a -> m b -> m c
fairBind2 f ma mb = ma >>? \a -> mb >>? \b -> f a b
