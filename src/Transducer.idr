module Transducer

import Data.Vect
import Set
import Graph as G

%access public export

record TransLabel (n : Nat) (m : Nat) where
  constructor MkTransLabel
  input : Fin n
  output : Fin m

Show (Fin n) where
  show = show . finToNat

Show (TransLabel n m) where
  show (MkTransLabel input output)
    = "\"" ++ show input ++ " : " ++ show output ++ "\""

data Transducer : (stt : Type) -> Vect ipl ipt -> Vect opl opt -> Type where
  MkTransducer : (ipa : Vect ipl ipt) -> -- Input alphabet, length `ipl`, type `ipt`
                 (opa : Vect opl opt) -> -- Output alphabet, length `opl`, type `opt`
                 Graph stt (TransLabel ipl opl) ->
                 Transducer stt ipa opa

isSeq : List (Fin n) -> Bool
isSeq = isSeq' FZ where
  isSeq' : Fin (S k) -> List (Fin k) -> Bool
  isSeq' _ [] = True
  isSeq' x (y :: ys) = x == (weaken y) && (isSeq' (FS x) (map weaken ys))

mkTransducer : (ipa : Vect ipl ipt) ->
               (opa : Vect opl opt) ->
               Graph stt (TransLabel ipl opl) ->
               Maybe (Transducer stt ipa opa)
mkTransducer ipa opa g
  = if all (isSeq .
            sort .
            (map (input . Edge.label)) .
            (out g)) (nodes g)
       then Just (MkTransducer ipa opa g)
       else Nothing

empty : (ipa : Vect ipl ipt) -> (opa : Vect opl opt) -> Transducer stt ipa opa
empty ipa opa = MkTransducer ipa opa empty

groupByInput : List (LEdge (TransLabel ipl opl)) ->
               Vect ipl (List (LEdge (TransLabel ipl opl)))
groupByInput 
  = let bin = replicate _ [] in
    foldr (\ledge => updateAt (input (label ledge)) ((::) ledge)) bin

groupByOutput : List (LEdge (TransLabel ipl opl)) ->
                Vect opl (List (LEdge (TransLabel ipl opl)))
groupByOutput
  = let bin = replicate _ [] in
    foldr (\ledge => updateAt (output (label ledge)) ((::) ledge)) bin

reorder : Ord a => (a, a) -> (a, a)
reorder (x1, x2) = if x1 > x2 then (x2, x1) else (x1, x2)

ambiguities : Transducer stt ipa opa -> Set (NodeID, NodeID)
ambiguities (MkTransducer _ _ g)
  = concat (map (formPairs . groupByInput) (groupByOutput . labEdges $ g)) where
    -- Each element of the vector is a list of edges sharing the same input
    -- All edges share the same output
    formPairs : Vect n (List (LEdge (TransLabel ipl' opl'))) -> Set (NodeID, NodeID)
    formPairs [] = empty
    formPairs (ledges :: rest)
      = union
          (fromList [reorder (q1, q2) | q1 <- map target ledges,
                                q2 <- map target (concat rest)])
          (formPairs rest)

propagate : Transducer stt ipa opa -> (NodeID, NodeID) -> Set (NodeID, NodeID)
propagate (MkTransducer _ _ g) (q1, q2)
  = concat (zipWith formPairs (listOutput q1) (listOutput q2)) where
    listOutput : NodeID -> Vect opl (List (LEdge (TransLabel ipl opl)))
    listOutput node = groupByOutput (out g node)
    formPairs : List (LEdge (TransLabel ipl' opl')) ->
                List (LEdge (TransLabel ipl' opl')) ->
                Set (NodeID, NodeID)
    formPairs l1 l2 = fromList [reorder (q1, q2) | q1 <- map target l1, q2 <- map target l2]

isInvertible : Transducer stt ipa opa -> Bool
isInvertible t =  ?qef
-- For each state, group it by producing

graph : Transducer stt ipa {ipl} opa {opl} -> Graph stt (TransLabel ipl opl)
graph (MkTransducer _ _ g) = g

transdu : Transducer String [0, 1] ["a", "b"]
transdu = maybe (empty [0, 1] ["a", "b"]) id (mkTransducer [0, 1] ["a", "b"] g) where
  g : Graph String (TransLabel 2 2)
  g = ([(MkTransLabel 1 0, 1)], 2, "q2", [(MkTransLabel 1 1, 2), (MkTransLabel 0 1, 1)]) 
       & ([], 1, "q1", [(MkTransLabel 0 0, 1)]) 
       & empty

