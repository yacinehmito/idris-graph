module Main

import Graph

test : Graph String String
test = ([("a", 0)], 1, "World", [("loop", 1)]) & ([], 0, "Hello", []) & empty

main : IO ()
main = putStrLn . graphToDot $ test
