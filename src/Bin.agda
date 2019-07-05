open import Data.Bool
open import Data.Char
open import Data.List as List
open import Data.Maybe
open import Data.Nat
open import Data.String

module Bin where

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
  fromList (List.map boolBit (true ∷ reverse digits))
toString (mkBin nothing) = "0"
