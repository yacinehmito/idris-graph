module BitsSet

import Data.Bits

-- bitsFromInt : Int -> Bits64
-- bitsFromInt = cast

-- intFromBits : Bits64 -> Int 
-- intFromBits = cast

Prefix : Type
Prefix = Bits64

Mask : Type
Mask = Bits64

BitMap : Type
BitMap = Bits64

Key : Type
Key = Bits64

data Mask' : Nat -> Type where
  MkMask : (bits : Bits64) -> Mask

-- Invariant: Nil is never found as a child of Bin.
-- Invariant: The Mask is a power of 2.  It is the largest bit position at which
--            two elements of the set differ.
-- Invariant: Prefix is the common high-order bits that all elements share to
--            the left of the Mask bit.
-- Invariant: In Bin prefix mask left right, left consists of the elements that
--            don't have the mask bit set; right is all the elements that do.
-- Invariant: The Prefix is zero for all but the last 5 (on 32 bit arches) or 6
--            bits (on 64 bit arches). The values of the map represented by a tip
--            are the prefix plus the indices of the set bits in the bit map.
-- A number stored in a set is stored as
-- * Prefix (all but last 5-6 bits) and
-- * BitMap (last 5-6 bits stored as a bitmask)
--   Last 5-6 bits are called a Suffix.

data BitsSet : Type where
  Bin : Prefix -> Mask -> (l : BitsSet) -> (r : BitsSet) -> BitsSet
  Tip : Prefix -> (bm : BitMap) -> BitsSet
  Nil : BitsSet
%name BitsSet bset

empty : BitsSet
empty = Nil

isEmpty : BitsSet -> Bool
isEmpty Nil = True
isEmpty _   = False

-- prefixOf : Int -> Prefix
-- prefixOf x = x & prefixBitMask

-- singleton : Key -> BitsSet
-- singleton x = Tip (prefixOf x) (bitmapOf x)
infixl 9 &
(&) : Bits64 -> Bits64 -> Bits64
(&) = and' {n = 3}

(-) : Bits64 -> Bits64 -> Bits64
(-) x y = prim__subB64 x y

bitcount : Int -> Bits64 -> Int
bitcount a 0 = a
bitcount a x = bitcount (a + 1) (x & (x - 1))

size : BitsSet -> Int
size (Bin _ _ l r) = size l + size r
size (Tip _ bm)    = bitcount 0 bm
size Nil           = 0


