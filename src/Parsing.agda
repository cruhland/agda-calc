open import Agda.Builtin.TrustMe
open import BasicString
open import Data.Bool
open import Data.Char
open import Data.Char.Properties
open import Data.Fin using (Fin)
open import Data.List
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Data.String as String
open import Data.Unit using (⊤; tt)
open import Function
open import Relation.Nullary
open import Relation.Nullary.Product

module Parsing where

trim : String → Maybe String
trim line with strip line
... | stripped with String.length stripped
... | zero = nothing
... | suc _ = just stripped

placeValue : List ℕ → ℕ → ℕ
placeValue [] magnitude = 0
placeValue (d ∷ ds) magnitude =
  magnitude * (d ∸ toNat '0') + placeValue ds (10 * magnitude)

AsciiDigit : ℕ → Set
AsciiDigit c = (toNat '0' ≤ c) × (c ≤ toNat '9')

asciiDigit? : ∀ c → Dec (AsciiDigit c)
asciiDigit? c = (toNat '0' ≤? c) ×-dec (c ≤? toNat '9')

parseNumber : String → ℕ
parseNumber text =
  placeValue (reverse (takeWhile asciiDigit? (map toNat (toList text)))) 1
