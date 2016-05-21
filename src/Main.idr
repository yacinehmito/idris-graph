module Main

import Graph
import Transducer
import Dot

test : Graph String String
test = ([("a", 0)], 1, "World", [("loop", 1)]) & ([], 0, "Hello", []) & empty

main : IO ()
main = putStrLn . graphToDot $ transdu
