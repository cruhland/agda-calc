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

-- noproof: definition
ℕDigit : Digit → Set
ℕDigit = _≤ 9

-- self-certifying
ℕDigit? : ∀ d → Dec (ℕDigit d)
ℕDigit? = _≤? 9

maybeAsciiDigit : ℕChar → Maybe Digit
maybeAsciiDigit c with asciiDigit? c
maybeAsciiDigit c | yes _ = just (c ∸ toℕ '0')
maybeAsciiDigit c | no _ = nothing

appendDigit : Digit → ℕ → ℕ
appendDigit d n = d + n * 10

-- proofs pending
placeValue : List Digit → ℕ
placeValue ds = foldr appendDigit 0 ds

-- proof pending
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

maybeAsciiDigit→ℕDigit : ∀ c d → maybeAsciiDigit c ≡ just d → ℕDigit d
maybeAsciiDigit→ℕDigit c d eq with asciiDigit? c
maybeAsciiDigit→ℕDigit c .(c ∸ 48) refl | yes (48≤c , c≤57) = ∸-monoˡ-≤ 48 c≤57

maybeAsciiDigitInvalidˡ :
  ∀ nc → ¬ AsciiDigit nc → maybeAsciiDigit nc ≡ nothing
maybeAsciiDigitInvalidˡ nc ¬ad with asciiDigit? nc
maybeAsciiDigitInvalidˡ nc ¬ad | yes ad = ⊥-elim (¬ad ad)
maybeAsciiDigitInvalidˡ nc ¬ad | no _ = refl

maybeAsciiDigitInvalidʳ : ∀ nc → maybeAsciiDigit nc ≡ nothing → ¬ AsciiDigit nc
maybeAsciiDigitInvalidʳ nc eq with asciiDigit? nc
maybeAsciiDigitInvalidʳ nc eq | no ¬p = ¬p

placeValueEmpty : placeValue [] ≡ 0
placeValueEmpty = refl

placeValueSingleton : ∀ d → placeValue (d ∷ []) ≡ d
placeValueSingleton d = +-identityʳ d

data DecimalNumber⁺ : List Digit → Set where
  leadingDigit : ∀ d → d > 0 → DecimalNumber⁺ (d ∷ [])
  trailingDigit : ∀ d ds → DecimalNumber⁺ ds → DecimalNumber⁺ (d ∷ ds)

n≤n*c⁺ : ∀ {c} n → n ≤ n * suc c
n≤n*c⁺ {c} n with *-monoʳ-≤ n (s≤s (z≤n {c}))
... | p rewrite *-identityʳ n = p

open ≤-Reasoning renaming
  (begin_ to ≤-begin_; _∎ to _≤-∎; _≡⟨_⟩_ to _≤-≡⟨_⟩_; _≡⟨⟩_ to _≤-≡⟨⟩_)

appendDigit-≤ : ∀ d n → n ≤ appendDigit d n
appendDigit-≤ d n =
  ≤-begin
    n
  ≤⟨ n≤n*c⁺ n ⟩
    n * 10
  ≤⟨ +-monoˡ-≤ (n * 10) z≤n ⟩
    d + n * 10
  ≤-≡⟨⟩
    appendDigit d n
  ≤-∎

placeValue-≤ : ∀ d ds → DecimalNumber⁺ ds → placeValue ds ≤ placeValue (d ∷ ds)
placeValue-≤ d ds num = appendDigit-≤ d (placeValue ds)

placeValuePositive : ∀ ds → DecimalNumber⁺ ds → 1 ≤ placeValue ds
placeValuePositive .(d ∷ []) (leadingDigit d d>0) rewrite +-identityʳ d = d>0
placeValuePositive .(d ∷ ds) (trailingDigit d ds num)
  with placeValue ds | placeValuePositive ds num
... | pv | rec =
  ≤-begin
    1
  ≤⟨ rec ⟩
    pv
  ≤⟨ appendDigit-≤ d pv ⟩
    d + pv * 10
  ≤-∎

decimalNumber⁺-length : ∀ ds → DecimalNumber⁺ ds → 1 ≤ length ds
decimalNumber⁺-length .(d ∷ []) (leadingDigit d d>0) = s≤s z≤n
decimalNumber⁺-length .(d ∷ ds) (trailingDigit d ds num) = s≤s z≤n

open ≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡-∎)

^-split : ∀ b m n → m ≤ n → b ^ n ≡ b ^ m * b ^ (n ∸ m)
^-split b m n m≤n =
  ≡-begin
    b ^ n
  ≡⟨ sym $ cong (b ^_) (m+[n∸m]≡n m≤n) ⟩
    b ^ (m + (n ∸ m))
  ≡⟨ ^-distribˡ-+-* b m (n ∸ m) ⟩
    b ^ m * b ^ (n ∸ m)
  ≡-∎

placeValueLowerBound :
  ∀ ds → DecimalNumber⁺ ds → 10 ^ (length ds ∸ 1) ≤ placeValue ds
placeValueLowerBound .(d ∷ []) (leadingDigit d d>0) rewrite +-identityʳ d = d>0
placeValueLowerBound .(d ∷ ds) (trailingDigit d ds num) =
  ≤-begin
    10 ^ (length (d ∷ ds) ∸ 1)
  ≤-≡⟨⟩
    10 ^ length ds
  ≤-≡⟨ ^-split 10 1 (length ds) (decimalNumber⁺-length ds num) ⟩
    10 * 10 ^ (length ds ∸ 1)
  ≤⟨ *-monoʳ-≤ 10 (placeValueLowerBound ds num) ⟩
    10 * placeValue ds
  ≤-≡⟨ *-comm 10 (placeValue ds) ⟩
    placeValue ds * 10
  ≤⟨ +-monoˡ-≤ (placeValue ds * 10) z≤n ⟩
    d + placeValue ds * 10
  ≤-≡⟨⟩
    placeValue (d ∷ ds)
  ≤-∎
