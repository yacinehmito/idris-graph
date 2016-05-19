module Transducer

import Data.Vect
import Graph

%access public export

record TransLabel (n : Nat) (m : Nat) where
  constructor MkTransLabel
  input : Fin (S n)
  output : Fin (S m)

Show (Fin n) where
  show = show . finToNat

Show (TransLabel n m) where
  show (MkTransLabel input output)
    = "\"" ++ show input ++ " : " ++ show output ++ "\""

data Transducer : (state_lab : Type) ->
                  (input_alph : Vect n input_ty) ->
                  (output_alph : Vect m output_ty) ->
                  Type where
  MkTransducer : Graph state_lab (TransLabel n m) ->
                 Transducer state_lab input_alph output_alph

isSeq : List (Fin (S k)) -> Bool
isSeq = isSeq' FZ where
  isSeq' : Fin (S k) -> List (Fin (S k)) -> Bool
  isSeq' FZ [FZ] = True
  isSeq' (FS r) (x :: xs) = (x == (FS r)) && (isSeq' (weaken r) xs)
  isSeq' _ _ = False

-- mkTransducer : (input_alph : Vect n input_ty) ->
--                (output_alph : Vect m output_ty) ->
--                (graph : Graph state_lab (TransLabel n m)) ->
--                Maybe (Transducer state_lab input_alph output_alph)
-- mkTransducer input_alph output_alph graph
--   = if all (isSeq .
--             reverse .
--             sort .
--             (map (input . Edge.content)) .
--             (out graph)) (nodes graph)
--        then Just (MkTransducer graph)
--        else Nothing

transdu : Graph String (TransLabel 2 2)
transdu =   ([(MkTransLabel 1 0, 1)], 2, "q2", [(MkTransLabel 1 1, 2), (MkTransLabel 0 1, 1)]) 
       & ([], 1, "q1", [(MkTransLabel 0 0, 1)]) 
       & Graph.empty

-- trueTransdu : Maybe (Transducer String [0, 1] ["a", "b"])
-- trueTransdu = mkTransducer [0, 1] ["a", "b"] transdu

