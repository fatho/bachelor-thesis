{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
module Control.Monad.Logic.Class.Extended where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad
import qualified Control.Monad.Logic as Logic
import Control.Monad.Logic.Class

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

-- | Takes any monad with a 'MonadLogic' instance, but replaces its 'interleave' and '>>-' implementation
-- by 'mplus' and '>>=', thus using the default MonadPlus behavior (which in many cases is depth-first search)
-- even when using those 'MonadLogic' combinators.
newtype UnFair m a = UnFair { fair :: m a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus)

instance MonadLogic m => MonadLogic (UnFair m) where
  msplit = UnFair . (liftM.liftM) (second UnFair) . msplit . fair
  interleave = mplus
  (>>-) = (>>=)

instance Observable m => Observable (UnFair m) where
  observe       = observe . fair
  observeAll    = observeAll . fair
  observeMany n = observeMany n . fair

-- | 'Logic' with DFS instead of BFS.
type UnFairLogic = UnFair Logic.Logic

-- | Like 'mapM', but with fair conjunction
mapFairM :: MonadLogic m => (a -> m b) -> [a] -> m [b]
mapFairM f = go where
  go []     = return []
  go (x:xs) = f x >>- \b -> (b:) `liftM` go xs

-- | Like 'msum', but with fair disjunction.
interleaveMany :: MonadLogic m => [m a] -> m a
interleaveMany = foldr interleave mzero

-- | Like 'liftM', but with fair conjunction.
liftFairM2 :: MonadLogic m => (a -> b -> c) -> m a -> m b -> m c
liftFairM2 f = fairBind2 (\a b -> return $ f a b)

-- | A fair bind over two monadic values.
fairBind2 :: MonadLogic m => (a -> b -> m c) -> m a -> m b -> m c
fairBind2 f ma mb = ma >>- \a -> mb >>- \b -> f a b
