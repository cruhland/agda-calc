open import BasicString
open import Data.Bool
open import Data.Char
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.String as String
open import Data.Unit
open import Function
open import Relation.Nullary

module Parsing where

trim : String → Maybe String
trim line with strip line
... | stripped with String.length stripped
... | zero = nothing
... | suc _ = just stripped

placeValue : List Char → ℕ → ℕ
placeValue [] magnitude = 0
placeValue (d ∷ ds) magnitude =
  magnitude * (toNat d ∸ toNat '0') + placeValue ds (10 * magnitude)

isDigitPred : ∀ c → Dec (T (isDigit c))
isDigitPred c with isDigit c
isDigitPred c | false = no id
isDigitPred c | true = yes tt

parseNumber : String → ℕ
parseNumber text = placeValue (reverse (takeWhile isDigitPred (toList text))) 1
