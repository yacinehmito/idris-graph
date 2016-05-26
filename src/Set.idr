module Set

import public Data.AVL.Set

export
Ord a => Semigroup (Set a) where
  (<+>) = union

export
Ord a => Monoid (Set a) where
  neutral = empty

