{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Control.Monad.Logic.Class.Extended where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad
import Control.Monad.Logic.Class

-- | Takes any monad with a 'MonadLogic' instance, but replaces its 'interleave' and '>>-' implementation
-- by 'mplus' and '>>=', thus using the default MonadPlus behavior (which in many cases is depth-first search)
-- even when using those 'MonadLogic' combinators.
newtype UnFair m a = UnFair { fair :: m a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus)

instance MonadLogic m => MonadLogic (UnFair m) where
  msplit = UnFair . (liftM.liftM) (second UnFair) . msplit . fair
  interleave = mplus
  (>>-) = (>>=)

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
