open import Agda.Builtin.IO
open import BasicIO
open import Bin
open import Data.Char
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat
open import Data.String
open import Data.Unit
open import Parsing

module Main where

process : String → Maybe String
process line =
  Maybe.map (λ trimmed → "= " ++ toString (convert (parseNumber trimmed)))
      (trim line)

{-# NON_TERMINATING #-}
main : IO ⊤
main = do
  putStr "> "
  hFlush stdout
  line ← getLine
  maybe′ putStrLn (return tt) (process line)
  main
