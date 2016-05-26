module NewGraph

import Data.AVL.Tree
import Data.AVL.Set
import Data.AVL.Dict

interface Graph (g : Type -> Type -> Type) where
  empty : g a b


record VertexData vTy eTy where
  constructor MkVertexData
  preds : Dict vTy eTy
  succs : Dict vTy eTy

record GraphData vTy eTy where
  constructor MkGraphData
  dict : Dict vTy (VertexData vTy eTy)

implementation Graph GraphData where
  empty : Graph a b
  empty = MkGraphData empty

