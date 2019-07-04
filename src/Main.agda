open import Agda.Builtin.IO
open import BasicIO
open import BasicString
open import Data.Bool
open import Data.Char
open import Data.List
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat
open import Data.String renaming (length to strLength; _++_ to _str++_)
open import Data.Unit

module Main where

trim : String → Maybe String
trim line with strip line
... | stripped with strLength stripped
... | zero = nothing
... | suc _ = just stripped

parseNumber : String → ℕ
parseNumber text = strLength text

record Bin⁺ : Set where
  constructor mkBin⁺
  field
    digits : List Bool

bin⁺One : Bin⁺
bin⁺One = mkBin⁺ []

record Bin : Set where
  constructor mkBin
  field
    value : Maybe Bin⁺

binZero : Bin
binZero = mkBin nothing

inc⁺ : Bin⁺ → Bin⁺
inc⁺ (mkBin⁺ digits) = mkBin⁺ (incDigits digits)
  where
    incDigits : List Bool → List Bool
    incDigits [] = false ∷ []
    incDigits (false ∷ bs) = true ∷ bs
    incDigits (true ∷ bs) = false ∷ incDigits bs

convert⁺Suc : ℕ → Bin⁺
convert⁺Suc zero = bin⁺One
convert⁺Suc (suc n) = inc⁺ (convert⁺Suc n)

convert : ℕ → Bin
convert zero = mkBin nothing
convert (suc n) = mkBin (just (convert⁺Suc n))

boolBit : Bool → Char
boolBit false = '0'
boolBit true = '1'

toString : Bin → String
toString (mkBin (just (mkBin⁺ digits))) =
  fromList (map boolBit (true ∷ reverse digits))
toString (mkBin nothing) = "0"

process : String → Maybe String
process line =
  Maybe.map (λ trimmed → "= " str++ toString (convert (parseNumber trimmed)))
      (trim line)

{-# NON_TERMINATING #-}
main : IO ⊤
main = do
  putStr "> "
  hFlush stdout
  line ← getLine
  maybe′ putStrLn (return tt) (process line)
  main
