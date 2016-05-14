module DictStub

import Data.SortedMap as M

%access export

-- A stub of Haskell's `IntMap` API but with arbitrary keys.
-- The implementation may be highly inefficient.

DictStub : Type -> Type -> Type
DictStub k v = SortedMap k v

empty : Ord k => DictStub k v
empty = M.empty

||| Insert k new key/value pair in the map.
||| If the key is already present in the map, the associated value
||| is replaced with the supplied value
insert : k -> v -> DictStub k v -> DictStub k v
insert = M.insert

||| Insert with a combining function. `insertWith f key value mp` will
||| insert the pair `(key, value)` into `mp` if `key` does not exist in the
||| map. If the key does exist, the function will insert f new_value
||| old_value
insertWith : (v -> v -> v) -> k -> v -> DictStub k v -> DictStub k v
insertWith f key value mp
  = case M.lookup key mp of
         Nothing => M.insert key value mp
         (Just old_value) => M.insert key (f value old_value) mp

||| Number of elements in the map
size : DictStub k v -> Nat
size = length . M.toList

||| Convert the map to a list of key/pairs. Subject to list fusion
toList : DictStub k v -> List (k, v)
toList = M.toList

||| Lookup the value at a key in the map
lookup : k -> DictStub k v -> Maybe v
lookup = M.lookup

||| Delete a key and its value from the map. When the key is not a member
||| of the map, the original map is returned.
delete : k -> DictStub k v -> DictStub k v
delete = M.delete

selectViewWithk : Ord k => Ordering -> DictStub k v -> Maybe ((k, v), DictStub k v)
selectViewWithk ordering mp
  = case M.toList mp of
         [] => Nothing
         (x :: xs) => let selected = foldr select x xs in
                          Just (selected, M.delete (fst selected) mp)
  where
    select : Ord k => (k, v) -> (k, v) -> (k, v)
    select elem@(key, value) acc@(skey, svalue)
     = if (compare skey key) == ordering then acc else elem

||| Retrieves the maximal (key, value) pair of the map, and the map
||| stripped of that element, or `Nothing` if passed an empty map.
maxViewWithk : Ord k => DictStub k v -> Maybe ((k, v), DictStub k v)
maxViewWithk = selectViewWithk GT

||| Retrives the minimal (key, value) pair of the map, and the map
||| stripped of that element, or `Nothing` if passed and empty map
minViewWithk : Ord k => DictStub k v -> Maybe ((k, v), DictStub k v)
minViewWithk = selectViewWithk LT

||| Return all keys of the map in ascending order. Subject to list fusion.
keys : DictStub k v -> List k
keys = map fst . M.toList

||| Map a function over all values in the map.
mapWithKey : Ord k => (k -> v1 -> v2) -> DictStub k v1 -> DictStub k v2
mapWithKey f = M.fromList . map (\(key, value) => (key, f key value)) . M.toList


||| Map a function over all values in the map.
map : Ord k => (v1 -> v2) -> DictStub k v1 -> DictStub k v2
map f = mapWithKey (\key, value => f value)

||| Build a map from a list of key/value pairs.
fromList : Ord k => List (k, v) -> DictStub k v
fromList = M.fromList

||| Build a map from a list of key/value pairs with a combining function.
fromListWith : Ord k => (v -> v -> v) -> List (k, v) -> DictStub k v
fromListWith f = foldr proc Data.SortedMap.empty where
  proc : (k, v) -> DictStub k v -> DictStub k v
  proc (key, value) = insertWith f key value


||| Adjust a value at a specific key. If the key is not a member of the map,
||| the original map is returned.
adjust : (v -> v) -> k -> DictStub k v -> DictStub k v
adjust f key mp
  = case M.lookup key mp of
         Nothing => mp
         (Just value) => M.insert key (f value) mp


||| Is the map empty?
null : DictStub a b -> Bool
null mp = case M.toList mp of
               [] => True
               _ => False

