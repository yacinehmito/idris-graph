module Graph.API

import Graph.Core

%access export

noNodes : Graph a b -> Nat
noNodes = length . labNodes

-- Not very useful, labNodes is enough
nodes : Graph a b -> List NodeID
nodes = map fst . labNodes

-- Same as nodes, labEdges is enough
-- edges

nodeRange : Graph a b -> (NodeID, NodeID)
nodeRange g = let vs = nodes g in (foldl1 min vs, foldl1 max vs)

labEdges : Graph a b -> List (LEdge b)
labEdges = ufold (\(p, node, _, s), acc =>
             (map (\(label, target) => (node, target, label)) s) ++
             (map (\(label, source) => (source, node, label)) p) ++
             acc) []

namespace Edge
  content : LEdge b -> b
  content (_, _, ec) = ec

namespace Node
  content : LNode b -> b
  content (_, nc) = nc

gmap : (Context a b -> Context c d) -> Graph a b -> Graph c d
gmap f = ufold (\c, g => (f c) & g) empty

nmap : (a -> c) -> Graph a b -> Graph c b
nmap f = gmap (\(ps, node, content, ss) => (ps, node, f content, ss))

private
map1 : (b -> c) -> List (b, Int) -> List (c, Int)
map1 f = map (\(content, node) => (f content, node))

emap : (b -> c) -> Graph a b -> Graph a c
emap f = gmap (\(ps, n, nc, ss) => (map1 f ps, n, nc, map1 f ss))

nemap : (a -> c) -> (b -> d) -> Graph a b -> Graph c d
nemap fn fe = gmap (\(ps, n, nc, ss) => (map1 fe ps, n, fn nc, map1 fe ss))

