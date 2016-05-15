module Quiver

import DictStub as D
import Graph

%access public export

NodeMap : Type -> Type
NodeMap = DictStub NodeID

Context' : Type -> Type -> Type
Context' a b = (NodeMap (List b), a, NodeMap (List b))

QuiverData : Type -> Type -> Type
QuiverData a b = NodeMap (Context' a b)

emptyData : QuiverData a b
emptyData = D.empty {k = NodeID} {v = Context' a b}

emptyMap : NodeMap (List b)
emptyMap = D.empty {k = NodeID} {v = List b}

%name QuiverData qdata

data Quiver a b = MkQuiver (QuiverData a b)

%name Quiver q, q1, q2

addLists : List a -> List a -> List a
addLists [x] ys = x :: ys
addLists xs [y] = y :: xs
addLists xs ys = xs ++ ys

addSucc : QuiverData a b -> NodeID -> List (b, NodeID) -> QuiverData a b
addSucc qdata _ [] = qdata
addSucc qdata node ((l, node') :: rest) = addSucc qdata' node rest
  where
    qdata' = adjust f node' qdata
    f : Context' a b -> Context' a b
    f (preds, l', succs) = (preds, l', insertWith addLists node [l] succs)

addPred : QuiverData a b -> NodeID -> List (b, NodeID) -> QuiverData a b
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

clearSucc : QuiverData a b -> NodeID -> List NodeID -> QuiverData a b
clearSucc qdata _ [] = qdata
clearSucc qdata node (p :: rest) = clearSucc qdata' node rest
  where
    qdata' = adjust f p qdata
    f : Context' a b -> Context' a b
    f (preds, l, succs) = (preds, l, delete node succs)

clearPred : QuiverData a b -> NodeID -> List NodeID -> QuiverData a b
clearPred qdata _ [] = qdata
clearPred qdata node (p :: rest) = clearSucc qdata' node rest
  where
    qdata' = adjust f p qdata
    f : Context' a b -> Context' a b
    f (preds, l, succs) = (delete node preds, l, succs)

Graph Quiver where
  empty = MkQuiver emptyData
  isEmpty (MkQuiver c) = case toList c of
                              [] => True
                              _ => False
  match node q@(MkQuiver qdata)
    = case D.lookup node qdata of
           Nothing => (Nothing, q)
           Just (preds, content, succs)
             => let qdata1 = delete node qdata
                    preds' = delete node preds
                    succs' = delete node succs
                    qdata2 = clearPred qdata1 node (keys succs')
                    qdata3 = clearSucc qdata2 node (keys preds')
                in (Just (toAdj preds', node, content, toAdj succs), MkQuiver qdata3)

  (&) (preds, node, content, succs) (MkQuiver qdata)
    = let qdata1 = insert node (fromAdj preds, content, fromAdj succs) qdata
          qdata2 = addSucc qdata1 node preds
          qdata3 = addPred qdata2 node succs in
      MkQuiver qdata3
  mkGraph nodes edges = insEdges edges (MkQuiver (fromList (
                          map (\(node, content) => (node, emptyMap, content, emptyMap)) nodes)))
  labNodes (MkQuiver qdata) = [ (node, content) | (node, (_, content, _)) <- toList qdata ]

test : Quiver String String
test = ([("a", 0)], 1, "World", [("loop", 1)]) & ([], 0, "Hello", []) & (MkQuiver emptyData)

