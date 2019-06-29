import IO.Primitive as Prim
open import Data.Unit
open import IO

module Main where

main : Prim.IO ⊤
main = run (putStrLn "Hello, world!")
