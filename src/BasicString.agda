open import Data.String

module BasicString where

postulate
  strip : String → String

{-# FOREIGN GHC import qualified Data.Text #-}
{-# COMPILE GHC strip = Data.Text.strip #-}
