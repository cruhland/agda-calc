open import Agda.Builtin.IO
open import BasicIO
open import Data.String
open import Data.Unit

module Main where

main : IO ⊤
main = do
  line <- getLine
  putStrLn (line ++ line)
