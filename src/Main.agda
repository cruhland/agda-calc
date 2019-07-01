import IO.Primitive as Prim
open import Codata.Musical.Colist
open import Codata.Musical.Costring
open import Codata.Musical.Notation
open import Data.Unit
open import Function
open import IO

module Main where

-- TODO: https://stackoverflow.com/a/21811537
process : Costring → ∞ (IO ⊤)
process input = ♯ (♯ putStr "\n> " >> ♯ putStr∞ input)

main : Prim.IO ⊤
main = run do
  input <- ♯ getContents
  process input
