module Graph

%access public export

NodeID : Type
NodeID = Int

%name NodeID node

LNode : Type -> Type
LNode a = (NodeID, a)

%name LNode lnode

Edge : Type
Edge = (NodeID, NodeID)

%name Edge edge

LEdge : Type -> Type
LEdge b = (NodeID, NodeID, b)

%name LEdge ledge

Path : Type
Path = List NodeID

%name Path path

Adj : Type -> Type
Adj b = List (b, NodeID)

%name Adj adj

GraphType : Type
GraphType = Type -> Type -> Type

Context : Type -> Type -> Type
Context a b = (Adj b, NodeID, a, Adj b)

%name Context ctxt

MContext : Type -> Type -> Type
MContext a b = Maybe (Context a b)

%name MContext mctxt

Decomp : GraphType -> Type -> Type -> Type
Decomp gr a b = (MContext a b, gr a b)

%name Decomp decomp

GDecomp : GraphType -> Type -> Type -> Type
GDecomp gr a b = (Context a b, gr a b)

%name GDecomp gdecomp

-- TODO choose right fixity
infixr 10 &


interface Graph (gr : GraphType) where
  (&) : Context a b -> gr a b -> gr a b
  empty : gr a b
  isEmpty : gr a b -> Bool -- Just there to allow type erasure
  match : NodeID -> gr a b -> Decomp gr a b
  mkGraph : List (LNode a) -> List (LEdge b) -> gr a b
  labNodes : gr a b -> List (LNode a)
  matchAny : gr a b -> GDecomp gr a b 
  matchAny g
    = case labNodes g of
           [] => ?empty_graph
           (n, _) :: _ => let (Just ctxt, g') = match n g in (ctxt, g')
  noNodes : gr a b -> Nat
  noNodes = length . labNodes
  nodes : gr a b -> List NodeID -- TODO: put this outside (but how?)
  nodes = map fst . labNodes
  ufold : (Context a b -> ty_acc -> ty_acc) -> ty_acc -> gr a b -> ty_acc -- TODO: move that too
  ufold f acc g
    = if isEmpty g
         then acc
         else let (ctxt, g') = matchAny g in f ctxt (ufold f acc g')
  nodeRange : gr a b -> (NodeID, NodeID)
  nodeRange g = let vs = nodes g in (foldl1 min vs, foldl1 max vs)
  labEdges : gr a b -> List (LEdge b)
  labEdges = ufold (\(_, node, _, s), acc =>
             (map (\(label, target) => (node, target, label)) s) ++ acc) Nil

insEdge : Graph gr => LEdge b -> gr a b -> gr a b
insEdge (source, target, l) graph
  = let (mcxt, graph') = match source graph
        (pr, _, la, su) = fromMaybe ?error mcxt in
    (pr, source, la, (l, target) :: su) & graph'

insEdges : Graph gr => List (LEdge b) -> gr a b -> gr a b
insEdges edges graph = foldl (flip insEdge) graph edges
