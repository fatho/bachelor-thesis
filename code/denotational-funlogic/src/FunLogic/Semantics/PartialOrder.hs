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

-- | Two elements are incompatible iff neither x <= y nor y <= x.
incompatible :: PartialOrd a => a -> a -> Bool
incompatible x y = not $ compatible x y