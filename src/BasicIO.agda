open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

-- This is easier than using the IO functions in the standard library,
-- but it's technically not as type-safe. And it bypasses the
-- termination checker.
module BasicIO where

postulate
  return : ∀ {A : Set} → A → IO A
  _>>_ : ∀ {A B : Set} → IO A → IO B → IO B
  _>>=_ : ∀ {A B : Set} → IO A → (A → IO B) → IO B

  getLine : IO String
  putStr : String → IO ⊤
  putStrLn : String → IO ⊤

  FileHandle : Set
  stdout : FileHandle
  hFlush : FileHandle → IO ⊤

{-# COMPILE GHC return = \_ -> return #-}
{-# COMPILE GHC _>>_ = \_ _ -> (>>) #-}
{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}

{-# FOREIGN GHC import qualified Data.Text.IO as TextIO #-}
{-# COMPILE GHC getLine = TextIO.getLine #-}
{-# COMPILE GHC putStr = TextIO.putStr #-}
{-# COMPILE GHC putStrLn = TextIO.putStrLn #-}

{-# FOREIGN GHC import qualified System.IO #-}
{-# COMPILE GHC FileHandle = type System.IO.Handle #-}
{-# COMPILE GHC stdout = System.IO.stdout #-}
{-# COMPILE GHC hFlush = System.IO.hFlush #-}
