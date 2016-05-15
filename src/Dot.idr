module Dot

import Graph

-- %default total

export
data Kind = Undirected | Directed

data Attribute : Type where
  Color : String -> Attribute
  Label : String -> Attribute

data EdgeDef : (kind : Kind) -> Type where
  SimpleEdge : (target : String) -> (source : String) -> EdgeDef kind
  (::) : String -> EdgeDef kind -> EdgeDef kind

data Statement : (kind : Kind) -> Type where
  Node : String -> List Attribute -> Statement kind
  Edge : EdgeDef kind -> List Attribute -> Statement kind

export
record Dot (kind : Kind) where
  constructor MkDot
  strict : Bool
  id : Maybe String
  body : List (Statement kind)

Show Kind where
  show Undirected = "graph"
  show Directed = "digraph"

Show Attribute where
  show (Color col) = "color=" ++ col
  show (Label lab) = "label=" ++ lab

edgeConnector : Kind -> String
edgeConnector Undirected = "--"
edgeConnector Directed = "->"

Show (EdgeDef kind) where
  show (SimpleEdge target source) = unwords [source, edgeConnector kind, target]
  show (target :: def) = unwords [show def, edgeConnector kind, target]

appendAttrs : List Attribute -> String -> String
appendAttrs [] str = str
appendAttrs attrs str = str ++ (" [" ++ tags ++ "]") where
  tags = unwords (map show attrs)

Show (Statement kind) where
  show (Node node attrs) = appendAttrs attrs (node)
  show (Edge def attrs) = appendAttrs attrs (show def)

showDeclaration : Dot kind -> String
showDeclaration dot = unwords . putStrict . putKind . putId $ [] where
  putKind : List String -> List String
  putKind ws = (show kind) :: ws
  putId : List String -> List String
  putId ws = case id dot of
                  Nothing => ws
                  Just identifier => identifier :: ws
  putStrict : List String -> List String
  putStrict ws = if strict dot then "strict" :: ws else ws

showBody : Dot kind -> String
showBody dot = unlines (map show (body dot))

export
Show (Dot kind) where
  show dot = showDeclaration dot ++ " {\n" ++ showBody dot ++ "\n}"

test : Dot Directed
test = MkDot True (Just "yo") [
  Node "a" [],
  Node "b" [],
  Edge (SimpleEdge "a" "b") []
  ]

fromGraph : (Show a, Show b) => Graph a b -> Dot Directed
fromGraph graph = MkDot False Nothing (nodes ++ edges) where
  nodes : List (Statement Directed)
  nodes = map (\(id, l) => Node (show id) [Label (show l)]) (labNodes graph)
  edges : List (Statement Directed)
  edges = map f (labEdges graph) where
    f : Show b => (Int, Int, b) -> Statement Directed
    f (source, target, l)
      = Edge (SimpleEdge (show source) (show target)) [Label (show l)]

export
graphToDot : (Show a, Show b) => Graph a b -> String
graphToDot = show . fromGraph


