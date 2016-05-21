module Transducer

import Data.Vect
import Graph
import Dot

%access public export

record TransLabel (n : Nat) (m : Nat) where
  constructor MkTransLabel
  input : Fin (S n)
  output : Fin (S m)

record TransLabel2 (input_alph : Vect n input_ty)
                   (output_alph : Vect m output_ty) where
  constructor MkTransLabel2
  input : Fin (S n)
  output : Fin (S m)


Show (Fin n) where
  show = show . finToNat

implementation Show (TransLabel2 input_alph output_alph) where
  show (MkTransLabel2 input output) = "a"
    -- = "\"" ++ show input ++ " : " ++ show output ++ "\""

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
  isSeq' f (x :: xs) = (f == x) && (isSeq' (FS f) (map weaken xs))
  isSeq' f Nil = True

mkTransducer : (input_alph : Vect n input_ty) ->
               (output_alph : Vect m output_ty) ->
               (graph : Graph state_lab (TransLabel n m)) ->
               Maybe (Transducer state_lab input_alph output_alph)
mkTransducer input_alph output_alph graph
  = if all (isSeq .
            sort .
            (map (input . Edge.content)) .
            (out graph)) (nodes graph)
       then Just (MkTransducer graph)
       else Nothing

transdu : Graph String (TransLabel 2 2)
transdu =   ([(MkTransLabel 1 0, 1)], 2, "q2", [(MkTransLabel 1 1, 2), (MkTransLabel 0 1, 1)]) 
       & ([], 1, "q1", [(MkTransLabel 0 0, 1)]) 
       & empty

trueTransdu : Maybe (Transducer String [0, 1] ["a", "b"])
trueTransdu = mkTransducer [0, 1] ["a", "b"] transdu

