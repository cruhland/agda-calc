open import Agda.Builtin.IO
open import BasicIO
open import BasicString
open import Data.Maybe
open import Data.Nat
open import Data.String
open import Data.Unit

module Main where

process : String → Maybe String
process line with strip line
... | stripped with length stripped
... | zero = nothing
... | suc _ = just ("= " ++ stripped ++ " " ++ stripped)

{-# NON_TERMINATING #-}
main : IO ⊤
main = do
  putStr "> "
  hFlush stdout
  line ← getLine
  maybe′ putStrLn (return tt) (process line)
  main
