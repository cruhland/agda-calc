open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

-- This is easier than using the IO functions in the standard library,
-- but it's technically not as type-safe. And it bypasses the
-- termination checker.
module BasicIO where

postulate
  return : ∀ {A : Set} → A → IO A
  _>>=_ : ∀ {A B : Set} → IO A → (A → IO B) → IO B
  getLine : IO String
  putStrLn : String → IO ⊤

{-# COMPILE GHC return = \_ -> return #-}
{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}

{-# FOREIGN GHC import qualified Data.Text.IO as TextIO #-}
{-# COMPILE GHC getLine = TextIO.getLine #-}
{-# COMPILE GHC putStrLn = TextIO.putStrLn #-}
