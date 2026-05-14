{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
module LookupTable (generateLUT) where

import Control.Applicative
import Control.Monad.Primitive
import Data.Word
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import GHC.Ptr
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

toWord8s :: Storable a => a -> IO [Word8]
toWord8s x = alloca $ \ptr -> do
  poke ptr x
  mapM (peekElemOff (castPtr ptr)) [0 .. sizeOf x - 1]

lookupTable :: (Bounded a, Enum a, Storable b) => (a -> b) -> Q Exp
lookupTable f = do
  word8ss <- runIO (mapM (toWord8s . f) [minBound .. maxBound])
  litE (stringPrimL (concat word8ss))

-- |
-- @generateLUT f@ generates an expression representing a memoized
-- version of @f@. The lookup table is generated at compile time and
-- stored directly in the final executable. The generated code is
-- unsafe if the 'Bounded' and 'Enum' instances are not law-abiding or
-- if the 'Storable' instance is crazy.
--
-- Due to the constraints of Template Haskell, the function to memoize
-- must be defined in a different module.
--
-- Example usage:
--
-- > module Foo where
-- >
-- > import Data.Word
-- > 
-- > fImpl :: Word8 -> Double
-- > fImpl w8 = fromIntegral w / 255
--
-- > module Bar where
-- >
-- > import Foo
-- >
-- > f :: Word8 -> Double
-- > f = $$(generateLUT fImpl)
generateLUT :: (Bounded a, Enum a, Storable b) => (a -> b) -> Q (TExp (a -> b))
generateLUT f =
  TExp <$> [| \a -> unsafeInlineIO (peekElemOff (Ptr $(lookupTable f)) (fromEnum a - fromEnum (minBound `asTypeOf` a))) |]
