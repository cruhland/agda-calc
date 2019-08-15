open import Agda.Builtin.TrustMe
open import BasicString
open import Data.Char
open import Data.Char.Properties
open import Data.Empty
open import Data.Fin using (Fin)
open import Data.List
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_)
open import Data.String as String hiding (length)
open import Data.Unit using (⊤; tt)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Product

module Parsing where

-- noproof: definition
ℕChar : Set
ℕChar = ℕ

-- noproof: definition
Digit : Set
Digit = ℕ

-- noproof: definition
AsciiDigit : ℕChar → Set
AsciiDigit c = (toℕ '0' ≤ c) × (c ≤ toℕ '9')

-- self-certifying
asciiDigit? : ∀ c → Dec (AsciiDigit c)
asciiDigit? c = (toℕ '0' ≤? c) ×-dec (c ≤? toℕ '9')

maybeAsciiDigit : ℕChar → Maybe Digit
maybeAsciiDigit c with asciiDigit? c
maybeAsciiDigit c | yes _ = just (c ∸ toℕ '0')
maybeAsciiDigit c | no _ = nothing

placeValue : List Digit → ℕ
placeValue ds = foldr (λ d n → d + n * 10) 0 ds

parseNumber : List ℕChar → ℕ
parseNumber chars = placeValue (reverse (mapMaybe maybeAsciiDigit chars))

-- noproof: primitive
toChars : String → List ℕChar
toChars = map toℕ ∘ toList

-- noproof: primitive
trim : String → Maybe String
trim line with strip line
... | stripped with String.length stripped
... | zero = nothing
... | suc _ = just stripped

-- Properties

maybeAsciiDigitValid :
  mapMaybe maybeAsciiDigit (toChars "0123456789") ≡
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
maybeAsciiDigitValid = refl

maybeAsciiDigitInvalid :
  ∀ nc → ¬ AsciiDigit nc → maybeAsciiDigit nc ≡ nothing
maybeAsciiDigitInvalid nc ¬ad with asciiDigit? nc
maybeAsciiDigitInvalid nc ¬ad | yes ad = ⊥-elim (¬ad ad)
maybeAsciiDigitInvalid nc ¬ad | no _ = refl

placeValueEmpty : placeValue [] ≡ 0
placeValueEmpty = refl

placeValueSingleton : ∀ d → placeValue (d ∷ []) ≡ d
placeValueSingleton d = +-identityʳ d
