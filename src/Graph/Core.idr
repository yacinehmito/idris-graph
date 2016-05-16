module Graph

import Graph.DictStub as D

-- %default total

-- --------------------------------------------------------------------- [Types]
public export
NodeID : Type
NodeID = Int
%name NodeID node

public export
LNode : Type -> Type
LNode a = (NodeID, a)
%name LNode lnode

public export
Edge : Type
Edge = (NodeID, NodeID)
%name Edge edge

public export
LEdge : Type -> Type
LEdge b = (NodeID, NodeID, b)
%name LEdge ledge

public export
Path : Type
Path = List NodeID
%name Path path

public export
Adj : Type -> Type
Adj b = List (b, NodeID)
%name Adj adj

public export
Context : Type -> Type -> Type
Context a b = (Adj b, NodeID, a, Adj b)
%name Context ctxt

public export
MContext : Type -> Type -> Type
MContext a b = Maybe (Context a b)
%name MContext mctxt

NodeMap : Type -> Type
NodeMap = DictStub NodeID

Context' : Type -> Type -> Type
Context' a b = (NodeMap (List b), a, NodeMap (List b))

GraphData : Type -> Type -> Type
GraphData a b = NodeMap (Context' a b)
%name GraphData qdata

export
data Graph a b = MkGraph (GraphData a b)

%name Graph q, q1, q2

public export
Decomp : Type -> Type -> Type
Decomp a b = (MContext a b, Graph a b)
%name Decomp decomp

public export
GDecomp : Type -> Type -> Type
GDecomp a b = (Context a b, Graph a b)
%name GDecomp gdecomp

-- ------------------------------------------------------------------- [Helpers]
addLists : List a -> List a -> List a
addLists [x] ys = x :: ys
addLists xs [y] = y :: xs
addLists xs ys = xs ++ ys

addSucc : GraphData a b -> NodeID -> List (b, NodeID) -> GraphData a b
addSucc qdata _ [] = qdata
addSucc qdata node ((l, node') :: rest) = addSucc qdata' node rest
  where
    qdata' = adjust f node' qdata
    f : Context' a b -> Context' a b
    f (preds, l', succs) = (preds, l', insertWith addLists node [l] succs)

addPred : GraphData a b -> NodeID -> List (b, NodeID) -> GraphData a b
addPred qdata _ [] = qdata
addPred qdata node ((l, node') :: rest) = addPred qdata' node rest
  where
    qdata' = adjust f node' qdata
    f : Context' a b -> Context' a b
    f (preds, l', succs) = (insertWith addLists node [l] preds, l', succs)

fromAdj : Adj b -> NodeMap (List b)
fromAdj = fromListWith addLists . map (\(content, node) => (node, [content]))

toAdj : NodeMap (List b) -> Adj b
toAdj = concatMap expand . toList
  where
    expand : (NodeID, List b) -> List (b, NodeID)
    expand (node, ls) = map ((flip MkPair) node) ls

clearSucc : GraphData a b -> NodeID -> List NodeID -> GraphData a b
clearSucc qdata _ [] = qdata
clearSucc qdata node (p :: rest) = clearSucc qdata' node rest
  where
    qdata' = adjust f p qdata
    f : Context' a b -> Context' a b
    f (preds, l, succs) = (preds, l, delete node succs)

clearPred : GraphData a b -> NodeID -> List NodeID -> GraphData a b
clearPred qdata _ [] = qdata
clearPred qdata node (p :: rest) = clearSucc qdata' node rest
  where
    qdata' = adjust f p qdata
    f : Context' a b -> Context' a b
    f (preds, l, succs) = (delete node preds, l, succs)


-- ---------------------------------------------------------------- [Operations]

infixr 10 & -- TODO choose right fixity

emptyData : GraphData a b
emptyData = D.empty {k = NodeID} {v = Context' a b}

emptyMap : NodeMap (List b)
emptyMap = D.empty {k = NodeID} {v = List b}

export
empty : Graph a b
empty = MkGraph emptyData

export
isEmpty : Graph a b -> Bool
isEmpty (MkGraph c) = case toList c of
                            [] => True
                            _ => False

export
embed : Context a b -> Graph a b -> Graph a b
embed (preds, node, content, succs) (MkGraph qdata)
  = let qdata1 = insert node (fromAdj preds, content, fromAdj succs) qdata
        qdata2 = addSucc qdata1 node preds
        qdata3 = addPred qdata2 node succs in
    MkGraph qdata3

export
(&) : Context a b -> Graph a b -> Graph a b
(&) = embed

-- TODO can we statically verify that we match against a node that's in the graph?
export
match : NodeID -> Graph a b -> Decomp a b
match node q@(MkGraph qdata)
  = case D.lookup node qdata of
         Nothing => (Nothing, q)
         Just (preds, content, succs)
           => let qdata1 = delete node qdata
                  preds' = delete node preds
                  succs' = delete node succs
                  qdata2 = clearPred qdata1 node (keys succs')
                  qdata3 = clearSucc qdata2 node (keys preds')
              in (Just (toAdj preds', node, content, toAdj succs), MkGraph qdata3)

-- TODO get rid of ?error by making sure that match always succeed
-- The Edge must find a way to tell that its source (and maybe target)
-- do belong to the graph
insEdge : LEdge b -> Graph a b -> Graph a b
insEdge (source, target, l) graph
  = let (mcxt, graph') = match source graph
        (pr, _, la, su) = fromMaybe ?error mcxt in
    (pr, source, la, (l, target) :: su) & graph'

insEdges : List (LEdge b) -> Graph a b -> Graph a b
insEdges edges graph = foldl (flip insEdge) graph edges

export
mkGraph : List (LNode a) -> List (LEdge b) -> Graph a b
mkGraph nodes edges = insEdges edges (MkGraph (fromList (
                        map (\(node, content) => (node, emptyMap, content, emptyMap)) nodes)))

export
labNodes : Graph a b -> List (LNode a)
labNodes (MkGraph qdata) = [ (node, content) | (node, (_, content, _)) <- toList qdata ]

-- TODO find a way to make sure that you never match on an empty graph
export
matchAny : Graph a b -> GDecomp a b 
matchAny g
  = case labNodes g of
         [] => ?empty_graph
         (n, _) :: _ => let (Just ctxt, g') = match n g in (ctxt, g')

export
ufold : (Context a b -> ty_acc -> ty_acc) -> ty_acc -> Graph a b -> ty_acc
ufold f acc g
  = if isEmpty g
       then acc
       else let (ctxt, g') = matchAny g in f ctxt (ufold f acc g')

