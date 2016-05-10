module Graph

import Data.Vect

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

Context : Type -> Type -> Type
Context a b = (Adj b, Node, a, Adj b)

MContext : Type -> Type -> Type
MContext a b = Maybe (Context a b)

GraphType : Type
GraphType = Nat -> Type -> Type -> Type

Decomp : GraphType -> Nat -> Type -> Type -> Type
Decomp gr n a b = (MContext a b, gr n a b)

GDecomp : GraphType -> Nat -> Type -> Type -> Type
GDecomp gr n a b = (Context a b, gr n a b)


interface Graph (gr : GraphType) where
  empty : gr Z a b
  isEmpty : gr n a b -> Bool
  match : Node -> gr (S n) a b -> Decomp gr n a b
  mkGraph : Vect n (LNode a) -> List (LEdge b) -> gr n a b
  labNodes : gr n a b -> Vect n (LNode a)
  matchAny : gr (S n) a b -> Decomp gr n a b -- TODO: Should be GDecomp
  matchAny g with (labNodes g)
    | ((node, _) :: _) = match node g
  noNodes : gr n a b -> Nat
  noNodes = length . labNodes
  nodes : gr n a b -> Vect n Node -- TODO: put this outside (but how?)
  nodeRange : gr (S n) a b -> (Node, Node)
  nodeRange g = let vs = nodes g in (minimum vs, maximum vs)


