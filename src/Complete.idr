module Complete

import Graph

data Complete : Graph a b -> Type where
  MkComplete : (graph : Graph a b) -> Complete graph


