{-|
Module      : Unicode.Codec.Utf32
Description : UTF-32 codec — Big-Endian and Little-Endian variants.

Haskell port of @Unicode.Codec.Utf32@ from unicode-lean.

Each scalar Unicode codepoint encodes to exactly 4 bytes; the invariant
is straight identity, no length-dependent escape sequences. The decoder
rejects:

  * inputs whose length is not exactly 4
  * 4-byte sequences encoding a surrogate codepoint U+D800..U+DFFF
  * 4-byte sequences encoding a value > U+10FFFF
-}
module Unicode.Codec.Utf32
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

-- | Encode a scalar codepoint as 4 bytes in big-endian order.
encodeOneBE :: Int -> ByteString
encodeOneBE cp =
  BS.pack
    [ fromIntegral ((cp `shiftR` 24) .&. 0xFF)
    , fromIntegral ((cp `shiftR` 16) .&. 0xFF)
    , fromIntegral ((cp `shiftR` 8) .&. 0xFF)
    , fromIntegral (cp .&. 0xFF)
    ]

-- | Encode a scalar codepoint as 4 bytes in little-endian order.
encodeOneLE :: Int -> ByteString
encodeOneLE cp =
  BS.pack
    [ fromIntegral (cp .&. 0xFF)
    , fromIntegral ((cp `shiftR` 8) .&. 0xFF)
    , fromIntegral ((cp `shiftR` 16) .&. 0xFF)
    , fromIntegral ((cp `shiftR` 24) .&. 0xFF)
    ]

-- | Decode 4 bytes as a big-endian UTF-32 codepoint. Returns 'Nothing'
-- when the length is not exactly 4, the value is a surrogate, or the
-- value exceeds U+10FFFF.
decodeOneBE :: ByteString -> Maybe Int
decodeOneBE bs
  | BS.length bs /= 4 = Nothing
  | otherwise =
      let b0 = fromIntegral (BS.index bs 0) :: Int
          b1 = fromIntegral (BS.index bs 1) :: Int
          b2 = fromIntegral (BS.index bs 2) :: Int
          b3 = fromIntegral (BS.index bs 3) :: Int
          cp = (b0 `shiftL` 24)
                 .|. (b1 `shiftL` 16)
                 .|. (b2 `shiftL` 8)
                 .|. b3
      in scalar cp

-- | Decode 4 bytes as a little-endian UTF-32 codepoint.
decodeOneLE :: ByteString -> Maybe Int
decodeOneLE bs
  | BS.length bs /= 4 = Nothing
  | otherwise =
      let b0 = fromIntegral (BS.index bs 0) :: Int
          b1 = fromIntegral (BS.index bs 1) :: Int
          b2 = fromIntegral (BS.index bs 2) :: Int
          b3 = fromIntegral (BS.index bs 3) :: Int
          cp = b0
                 .|. (b1 `shiftL` 8)
                 .|. (b2 `shiftL` 16)
                 .|. (b3 `shiftL` 24)
      in scalar cp

scalar :: Int -> Maybe Int
scalar cp
  | cp > 0x10FFFF                  = Nothing
  | cp >= 0xD800 && cp <= 0xDFFF   = Nothing
  | otherwise                      = Just cp

-- | Concatenate the UTF-32 BE encodings of a codepoint sequence.
encodeBE :: [Int] -> ByteString
encodeBE = BS.concat . map encodeOneBE

-- | Concatenate the UTF-32 LE encodings of a codepoint sequence.
encodeLE :: [Int] -> ByteString
encodeLE = BS.concat . map encodeOneLE
