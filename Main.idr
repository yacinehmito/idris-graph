module Main

import Quiver
import Graph

main : IO ()
main = do
  putStrLn "Hello world"
  putStrLn . show $ labNodes test
