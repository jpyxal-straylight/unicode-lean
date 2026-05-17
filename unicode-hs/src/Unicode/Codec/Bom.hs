{-|
Module      : Unicode.Codec.Bom
Description : Byte-Order-Mark detection across the five Unicode encodings.

Haskell port of @Unicode.Codec.Bom@ from unicode-lean.

@
UTF-8    : EF BB BF              (3 bytes)
UTF-16BE : FE FF                 (2 bytes)
UTF-16LE : FF FE                 (2 bytes)
UTF-32BE : 00 00 FE FF           (4 bytes)
UTF-32LE : FF FE 00 00           (4 bytes)
@

Order matters: UTF-32 BOMs share their leading bytes with UTF-16 BOMs,
so the 4-byte UTF-32 patterns must be checked BEFORE the 2-byte UTF-16
patterns. Specifically, @FF FE 00 00@ is a UTF-32LE BOM, not a UTF-16LE
BOM followed by two NUL bytes.

Constructor names match the Lean @BomKind.utf8@ / @BomKind.utf16BE@ etc.
(PascalCase is language-mandated in Haskell). Consume via qualified
import:

> import qualified Unicode.Codec.Bom as Bom
> case Bom.detect bs of
>   Just (Bom.Utf8, _) -> ...
-}
module Unicode.Codec.Bom
  ( BomKind (..)
  , bomLength
  , detect
  , strip
  ) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Word (Word8)

-- | The five Unicode encoding kinds distinguishable by their BOM.
data BomKind
  = Utf8
  | Utf16BE
  | Utf16LE
  | Utf32BE
  | Utf32LE
  deriving stock (Eq, Show, Ord, Enum, Bounded)

-- | The byte length of each BOM.
bomLength :: BomKind -> Int
bomLength Utf8    = 3
bomLength Utf16BE = 2
bomLength Utf16LE = 2
bomLength Utf32BE = 4
bomLength Utf32LE = 4

-- | Detect a leading BOM, returning the encoding kind and the number of
-- BOM bytes to skip. The 4-byte UTF-32 BOMs are tested before the 2-byte
-- UTF-16 BOMs because @FF FE 00 00@ is UTF-32LE, not UTF-16LE followed
-- by U+0000. Returns 'Nothing' if the input does not begin with any
-- recognised BOM.
detect :: ByteString -> Maybe (BomKind, Int)
detect bs
  | n >= 4
  , b0 == 0x00, b1 == 0x00, b2 == 0xFE, b3 == 0xFF = Just (Utf32BE, 4)
  | n >= 4
  , b0 == 0xFF, b1 == 0xFE, b2 == 0x00, b3 == 0x00 = Just (Utf32LE, 4)
  | n >= 3
  , b0 == 0xEF, b1 == 0xBB, b2 == 0xBF             = Just (Utf8, 3)
  | n >= 2
  , b0 == 0xFE, b1 == 0xFF                         = Just (Utf16BE, 2)
  | n >= 2
  , b0 == 0xFF, b1 == 0xFE                         = Just (Utf16LE, 2)
  | otherwise                                      = Nothing
  where
    !n = BS.length bs
    byteAt :: Int -> Word8
    byteAt i = if i < n then BS.index bs i else 0
    !b0 = byteAt 0
    !b1 = byteAt 1
    !b2 = byteAt 2
    !b3 = byteAt 3

-- | Strip the BOM from @bs@ if one is present, returning the remaining
-- content and the detected encoding. Returns @(Nothing, bs)@ (no BOM
-- stripped) if the input does not begin with a recognised BOM.
strip :: ByteString -> (Maybe BomKind, ByteString)
strip bs = case detect bs of
  Just (kind, k) -> (Just kind, BS.drop k bs)
  Nothing        -> (Nothing, bs)
