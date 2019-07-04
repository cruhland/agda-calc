open import Agda.Builtin.IO
open import BasicIO
open import Data.String
open import Data.Unit

module Main where

process : String → String
process line = line ++ " " ++ line

{-# NON_TERMINATING #-}
main : IO ⊤
main = do
  putStr "> "
  hFlush stdout
  line <- getLine
  putStr "= "
  putStrLn (process line)
  main
