{-# LANGUAGE LambdaCase #-}
module FunLogic.Semantics.Pruning where

import           Control.Applicative
import           Control.Monad
import qualified Data.Set as S

import qualified FunLogic.Semantics.PartialOrder as PO
import qualified FunLogic.Semantics.Search       as Search

-- | Removes duplicate values from a monadic computation.
pruneDuplicates :: (Ord a, Search.MonadSearch m) => m a -> m a
pruneDuplicates = go S.empty where
  go vals comp = Search.peek comp >>= \case
    Nothing -> mzero
    Just (v,rest)
      | v `S.member` vals -> go vals rest
      | otherwise         -> return v <|> go (S.insert v vals) rest

-- | Removes a value from the monadic computation, if a larger value has already been returned.
pruneNonMaximal :: (PO.PartialOrd a, Search.MonadSearch m) => m a -> m a
{-# INLINABLE pruneNonMaximal #-}
pruneNonMaximal = pruneNonMaximal' id

-- | Removes a value from the monadic computation, if a larger value has already been returned.
-- Only the 'N' most recent maximal values are considered.
pruneNonMaximalN :: (PO.PartialOrd a, Search.MonadSearch m) => Int -> m a -> m a
{-# INLINABLE pruneNonMaximalN #-}
pruneNonMaximalN n = pruneNonMaximal' (take n)

-- | Removes a value from the monadic computation, if a larger value has already been returned.
-- This functions allows to transform the internal representation of the list of maximal elements
-- and to always return elements matching a specific predicate.
pruneNonMaximal' :: (PO.PartialOrd a, Search.MonadSearch m) => ([a] -> [a]) -> m a -> m a
{-# INLINABLE pruneNonMaximal' #-}
pruneNonMaximal' process = go [] where
  -- | Maintains a list of maximal elements encountered so far. It maintains the invariant, that each element in this
  -- list is incomparable to every other element.
  go maxvals comp = Search.peek comp >>= \case
    Nothing -> mzero
    Just (v,rest) -> case check maxvals v of
      Nothing -> go maxvals rest
      Just maxvals' -> return v <|> go maxvals' rest

  -- | Checks if there is a larger or equal element in the list.
  -- If it's not, all elements that are less than the given value are removed.
  --
  check xs v = (v:) <$> process <$> check' xs v

  check' [] _       = Just []
  check' (x:xs) v
    | v `PO.leq` x = Nothing
    | x `PO.lt`  v = check' xs v
    | otherwise    = (x:) <$> check' xs v
