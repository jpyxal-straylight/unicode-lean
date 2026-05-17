{-|
Module      : Unicode.Codec.Utf16
Description : UTF-16 codec — Big-Endian and Little-Endian variants.

Haskell port of @Unicode.Codec.Utf16@ from unicode-lean.

Each scalar Unicode codepoint encodes to either 2 bytes (BMP) or 4 bytes
(supplementary planes via surrogate pair). The supplementary pair is
constructed as:

  X    = cp - 0x10000          -- 20-bit value
  high = 0xD800 + (X >> 10)    -- high surrogate, 0xD800..0xDBFF
  low  = 0xDC00 + (X & 0x3FF)  -- low  surrogate, 0xDC00..0xDFFF

The decoder rejects:

  * inputs whose length is not exactly 2 or 4
  * 2-byte sequences in the surrogate range U+D800..U+DFFF (lone surrogate)
  * 4-byte sequences not forming a valid (high, low) surrogate pair
-}
module Unicode.Codec.Utf16
  ( -- * Single-codepoint encoders
    encodeOneBE
  , encodeOneLE
    -- * Single-codepoint decoders
  , decodeOneBE
  , decodeOneLE
    -- * Sequence encoders
  , encodeBE
  , encodeLE
  ) where

import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

-- | Encode a scalar codepoint as 2 or 4 bytes in UTF-16 BE.
--
-- Assumes the codepoint is in the valid scalar range (0..0x10FFFF minus
-- surrogates). Out-of-range inputs produce bogus output; the decoder
-- rejects them.
encodeOneBE :: Int -> ByteString
encodeOneBE cp
  | cp < 0x10000 =
      BS.pack
        [ fromIntegral ((cp `shiftR` 8) .&. 0xFF)
        , fromIntegral (cp .&. 0xFF)
        ]
  | otherwise =
      let x    = cp - 0x10000
          high = 0xD800 + (x `shiftR` 10)
          low  = 0xDC00 + (x .&. 0x3FF)
      in BS.pack
           [ fromIntegral ((high `shiftR` 8) .&. 0xFF)
           , fromIntegral (high .&. 0xFF)
           , fromIntegral ((low `shiftR` 8) .&. 0xFF)
           , fromIntegral (low .&. 0xFF)
           ]

-- | Encode a scalar codepoint as 2 or 4 bytes in UTF-16 LE.
encodeOneLE :: Int -> ByteString
encodeOneLE cp
  | cp < 0x10000 =
      BS.pack
        [ fromIntegral (cp .&. 0xFF)
        , fromIntegral ((cp `shiftR` 8) .&. 0xFF)
        ]
  | otherwise =
      let x    = cp - 0x10000
          high = 0xD800 + (x `shiftR` 10)
          low  = 0xDC00 + (x .&. 0x3FF)
      in BS.pack
           [ fromIntegral (high .&. 0xFF)
           , fromIntegral ((high `shiftR` 8) .&. 0xFF)
           , fromIntegral (low .&. 0xFF)
           , fromIntegral ((low `shiftR` 8) .&. 0xFF)
           ]

-- | Decode a UTF-16 BE byte sequence as a single codepoint. Returns
-- 'Nothing' on length-mismatch, lone-surrogate, or invalid surrogate
-- pair. Accepts byte sequences of length exactly 2 (BMP) or 4
-- (supplementary-plane surrogate pair).
decodeOneBE :: ByteString -> Maybe Int
decodeOneBE bs = case BS.length bs of
  2 ->
    let b0 = fromIntegral (BS.index bs 0) :: Int
        b1 = fromIntegral (BS.index bs 1) :: Int
        u  = (b0 `shiftL` 8) .|. b1
    in if u >= 0xD800 && u <= 0xDFFF then Nothing else Just u
  4 ->
    let b0 = fromIntegral (BS.index bs 0) :: Int
        b1 = fromIntegral (BS.index bs 1) :: Int
        b2 = fromIntegral (BS.index bs 2) :: Int
        b3 = fromIntegral (BS.index bs 3) :: Int
        high = (b0 `shiftL` 8) .|. b1
        low  = (b2 `shiftL` 8) .|. b3
    in if high >= 0xD800 && high <= 0xDBFF && low >= 0xDC00 && low <= 0xDFFF
         then Just (0x10000 + ((high - 0xD800) `shiftL` 10) + (low - 0xDC00))
         else Nothing
  _ -> Nothing

-- | Decode a UTF-16 LE byte sequence as a single codepoint.
decodeOneLE :: ByteString -> Maybe Int
decodeOneLE bs = case BS.length bs of
  2 ->
    let b0 = fromIntegral (BS.index bs 0) :: Int
        b1 = fromIntegral (BS.index bs 1) :: Int
        u  = b0 .|. (b1 `shiftL` 8)
    in if u >= 0xD800 && u <= 0xDFFF then Nothing else Just u
  4 ->
    let b0 = fromIntegral (BS.index bs 0) :: Int
        b1 = fromIntegral (BS.index bs 1) :: Int
        b2 = fromIntegral (BS.index bs 2) :: Int
        b3 = fromIntegral (BS.index bs 3) :: Int
        high = b0 .|. (b1 `shiftL` 8)
        low  = b2 .|. (b3 `shiftL` 8)
    in if high >= 0xD800 && high <= 0xDBFF && low >= 0xDC00 && low <= 0xDFFF
         then Just (0x10000 + ((high - 0xD800) `shiftL` 10) + (low - 0xDC00))
         else Nothing
  _ -> Nothing

-- | Concatenate the UTF-16 BE encodings of a codepoint sequence.
encodeBE :: [Int] -> ByteString
encodeBE = BS.concat . map encodeOneBE

-- | Concatenate the UTF-16 LE encodings of a codepoint sequence.
encodeLE :: [Int] -> ByteString
encodeLE = BS.concat . map encodeOneLE
