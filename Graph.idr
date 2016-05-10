module Graph

import Data.Vect

-- TODO:
-- * Put types in the interface (if sensible)
-- * Get rid of Decomp/MContext by provinding proofs instead
-- * Node should be a black box
-- * Use a record for Context

Node : Type
Node = Int

LNode : Type -> Type
LNode a = (Node, a)

Edge : Type
Edge = (Node, Node)

LEdge : Type -> Type
LEdge b = (Node, Node, b)

Path : Type
Path = List Node

Adj : Type -> Type
Adj b = List (b, Node)

GraphType : Type
GraphType = (size : Nat) -> Type -> Type -> Type

Context : Type -> Type -> Type
Context a b = (Adj b, Node, a, Adj b)

MContext : Type -> Type -> Type
MContext a b = Maybe (Context a b)

Decomp : GraphType -> Nat -> Type -> Type -> Type
Decomp gr n a b = (MContext a b, gr n a b)

GDecomp : GraphType -> Nat -> Type -> Type -> Type
GDecomp gr n a b = (Context a b, gr n a b)

-- TODO choose right fixity
infixr 10 &

interface Graph (gr : GraphType) where
  -- ([lpi, pi], node, l, [lsi, si]) : Context a b
  -- pre: node not in g, pi in g, si in g
  -- post: node in g, context in g, size S n
  -- so, if n = Z, we must have ([], node, l, [])
  -- then you just need to make sure that you insert node in the right order
  -- Provided we index the nodes in order, we can reduce to:
  -- pre: node = n, pi <= n, si <= n
  -- post: size S n
  -- Do we even need node at this point? You'd need to remember
  -- the order of insertion anyway
  (&) : Context a b -> gr n a b -> gr (S n) a b
  empty : gr Z a b
  isEmpty : gr n a b -> Bool -- Just there to allow type erasure
  match : Node -> gr (S n) a b -> Decomp gr n a b
  mkGraph : Vect n (LNode a) -> List (LEdge b) -> gr n a b
  labNodes : gr n a b -> Vect n (LNode a)
  matchAny : gr (S n) a b -> Decomp gr n a b -- TODO: Should be GDecomp
  matchAny g with (labNodes g)
    | ((node, _) :: _) = match node g
  noNodes : gr n a b -> Nat -- Just there to allow type erasure
  noNodes = length . labNodes
  nodes : gr n a b -> Vect n Node -- TODO: put this outside (but how?)
  ufold : (Context a b -> acc -> acc) -> acc -> gr n a b -> acc -- TODO: move that too
  nodeRange : gr (S n) a b -> (Node, Node)
  nodeRange g = let vs = nodes g in (foldl1 min vs, foldl1 max vs)
  labEdges : gr n a b -> List (LEdge b)
  labEdges = ufold (\(_, node, _, s), acc =>
             (map (\(label, target) => (node, target, label)) s) ++ acc) Nil






