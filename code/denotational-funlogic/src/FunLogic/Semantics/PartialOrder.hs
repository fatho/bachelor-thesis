module FunLogic.Semantics.PartialOrder where

-- | Defines a partial order.
class Eq a => PartialOrd a where
  -- | A reflexive, antisymmetric, and transitive binary relation.
  leq :: a -> a -> Bool
  leq x y = x `lt` y || x == y
  -- | An irreflexive, antisymmetric, and transitive binary relation.
  lt :: a -> a -> Bool
  lt x y = x `leq` y && x /= y

-- | Checks whether two elements are compatible (i.e. if x <= y or y <= x)
compatible :: PartialOrd a => a -> a -> Bool
compatible x y = x `leq` y || y `leq` x

-- | Returns the lesser of both elements, if they are compatible.
partialMin :: PartialOrd a => a -> a -> Maybe a
partialMin x y
  | x `leq` y = Just x
  | y `leq` x = Just y
  | otherwise = Nothing

-- | Returns the greater of both element, if they are compatible.
partialMax :: PartialOrd a => a -> a -> Maybe a
partialMax x y
  | x `leq` y = Just y
  | y `leq` x = Just x
  | otherwise = Nothing

-- | Two elements are incompatible iff neither x <= y nor y <= x.
incompatible :: PartialOrd a => a -> a -> Bool
incompatible x y = not $ compatible x y
