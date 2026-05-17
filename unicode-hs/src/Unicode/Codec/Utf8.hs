{-|
Module      : Unicode.Codec.Utf8
Description : Strict UTF-8 codec — validator, decoder, and encoder.

Haskell port of @Unicode.Codec.Utf8@ + the codepoint bridge from
@Unicode.Normalization.Utf8Bridge@ in unicode-lean.

The validator rejects overlong encodings, surrogate codepoints
(U+D800..U+DFFF), codepoints beyond U+10FFFF, truncated multi-byte
sequences, invalid start bytes, and invalid continuation bytes. Strictness
matches RFC 3629 and is independent of any host-stdlib UTF-8 routine, so
the Lean reference and the Haskell port accept exactly the same byte
sequences.

Offset convention for 'firstInvalidUtf8Offset': the returned offset is the
index of the byte on which the state machine transitioned to reject. For
'OverlongEncoding' (detected on emission of a multi-byte sequence), the
offset is the START byte of the sequence, not the last byte consumed.
-}
module Unicode.Codec.Utf8
  ( -- * Decoder state
    Utf8State (..)
  , Utf8StepResult (..)
  , utf8DecodeStep
    -- * Validation
  , firstInvalidUtf8Offset
  , isValidUtf8
    -- * Codec
  , encodeCodepoint
  , encodeCodepoints
  , decodeToCodepoints
  ) where

import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Word (Word8)

import Unicode.Codec.Strict
  ( Utf8RejectKind
      ( CodepointBeyondMax
      , InvalidContinuationByte
      , InvalidStartByte
      , OverlongEncoding
      , SurrogateCodepoint
      , TruncatedSequence
      )
  )

-- ─────────────────────────────────────────────────────────────────────────
-- Decoder state
-- ─────────────────────────────────────────────────────────────────────────

-- | UTF-8 decoder state. @ExpectCont remaining accum minCp@ means we are
-- in the middle of a multi-byte sequence: @remaining@ continuation bytes
-- still needed, @accum@ holds the codepoint accumulated so far, and
-- @minCp@ is the smallest codepoint a sequence of this start-byte class
-- must decode to (used to reject overlong encodings).
data Utf8State
  = ExpectStart
  | ExpectCont !Int !Int !Int
  deriving stock (Eq, Show)

-- | A single decoder step produces either a new state, an emitted
-- codepoint with a new state, or a rejection.
data Utf8StepResult
  = Continue !Utf8State
  | Emit !Int !Utf8State
  | Reject !Utf8RejectKind
  deriving stock (Eq, Show)

-- ─────────────────────────────────────────────────────────────────────────
-- Decoder step
-- ─────────────────────────────────────────────────────────────────────────

-- | Process one byte of input given the current state.
--
-- Start-byte ranges (from RFC 3629):
--
-- * 0x00..0x7F — 1-byte ASCII, emit directly
-- * 0x80..0xBF — invalid as start byte (continuation bytes only)
-- * 0xC0..0xC1 — invalid (would encode overlong 2-byte sequences for ASCII)
-- * 0xC2..0xDF — 2-byte sequence start, minCp = 0x80
-- * 0xE0..0xEF — 3-byte sequence start, minCp = 0x800
-- * 0xF0..0xF4 — 4-byte sequence start, minCp = 0x10000
-- * 0xF5..0xFF — invalid (would encode codepoints > U+10FFFF)
--
-- Continuation bytes must be in 0x80..0xBF (high two bits = 10). On
-- emission: reject if decoded codepoint < @minCp@ (overlong), or in
-- 0xD800..0xDFFF (surrogate), or > 0x10FFFF (beyond max).
utf8DecodeStep :: Utf8State -> Word8 -> Utf8StepResult
utf8DecodeStep st b =
  let n :: Int
      n = fromIntegral b
  in case st of
       ExpectStart
         | n < 0x80  -> Emit n ExpectStart
         | n < 0xC2  -> Reject InvalidStartByte
         | n < 0xE0  -> Continue (ExpectCont 1 (n .&. 0x1F) 0x80)
         | n < 0xF0  -> Continue (ExpectCont 2 (n .&. 0x0F) 0x800)
         | n < 0xF5  -> Continue (ExpectCont 3 (n .&. 0x07) 0x10000)
         | otherwise -> Reject InvalidStartByte
       ExpectCont remaining accum minCp
         | n < 0x80 || n >= 0xC0 -> Reject InvalidContinuationByte
         | otherwise ->
             let next = (accum `shiftL` 6) .|. (n .&. 0x3F)
             in case remaining of
                  1
                    | next < minCp                       -> Reject OverlongEncoding
                    | next >= 0xD800 && next <= 0xDFFF   -> Reject SurrogateCodepoint
                    | next > 0x10FFFF                    -> Reject CodepointBeyondMax
                    | otherwise                          -> Emit next ExpectStart
                  m
                    | m <= 0                             -> Reject InvalidContinuationByte
                    | otherwise                          -> Continue (ExpectCont (m - 1) next minCp)

-- ─────────────────────────────────────────────────────────────────────────
-- Walker
-- ─────────────────────────────────────────────────────────────────────────

-- | Returns @Just (offset, kind)@ at the first byte where the UTF-8 state
-- machine transitions to a reject state, or 'Nothing' if the whole input
-- is valid UTF-8.
--
-- Offset for 'OverlongEncoding' is the START byte of the offending
-- sequence; for other reject kinds it is the byte that triggered the
-- rejection. Truncated sequences report offset = 'BS.length' bs.
firstInvalidUtf8Offset :: ByteString -> Maybe (Int, Utf8RejectKind)
firstInvalidUtf8Offset bs = go ExpectStart 0 0
  where
    !n = BS.length bs

    go :: Utf8State -> Int -> Int -> Maybe (Int, Utf8RejectKind)
    go st i seqStart
      | i >= n =
          case st of
            ExpectStart      -> Nothing
            ExpectCont {}    -> Just (i, TruncatedSequence)
      | otherwise =
          let b = BS.index bs i
          in case utf8DecodeStep st b of
               Continue next ->
                 let newSeqStart = case st of
                       ExpectStart   -> i
                       ExpectCont {} -> seqStart
                 in go next (i + 1) newSeqStart
               Emit _ next ->
                 go next (i + 1) (i + 1)
               Reject kind ->
                 case kind of
                   OverlongEncoding -> Just (seqStart, kind)
                   _                -> Just (i, kind)

-- | True iff every byte of @bs@ is part of a valid UTF-8 sequence per
-- RFC 3629 — equivalent to @'firstInvalidUtf8Offset' bs == 'Nothing'@.
isValidUtf8 :: ByteString -> Bool
isValidUtf8 bs = case firstInvalidUtf8Offset bs of
  Nothing -> True
  Just _  -> False

-- ─────────────────────────────────────────────────────────────────────────
-- Encoder
-- ─────────────────────────────────────────────────────────────────────────

-- | Encode a single codepoint as 1–4 UTF-8 bytes per UAX #44 §5.1.
--
-- Assumes @cp < 0x110000@; invalid codepoints above that range produce
-- bogus output. The pipeline never surfaces them because the decoder
-- rejects them.
encodeCodepoint :: Int -> ByteString
encodeCodepoint cp
  | cp < 0x80    =
      BS.pack [ fromIntegral cp ]
  | cp < 0x800   =
      BS.pack
        [ fromIntegral (0xC0 .|. (cp `shiftR` 6))
        , fromIntegral (0x80 .|. (cp .&. 0x3F))
        ]
  | cp < 0x10000 =
      BS.pack
        [ fromIntegral (0xE0 .|. (cp `shiftR` 12))
        , fromIntegral (0x80 .|. ((cp `shiftR` 6) .&. 0x3F))
        , fromIntegral (0x80 .|. (cp .&. 0x3F))
        ]
  | otherwise    =
      BS.pack
        [ fromIntegral (0xF0 .|. (cp `shiftR` 18))
        , fromIntegral (0x80 .|. ((cp `shiftR` 12) .&. 0x3F))
        , fromIntegral (0x80 .|. ((cp `shiftR` 6) .&. 0x3F))
        , fromIntegral (0x80 .|. (cp .&. 0x3F))
        ]

-- | Concatenate the UTF-8 encodings of a codepoint sequence.
encodeCodepoints :: [Int] -> ByteString
encodeCodepoints = BS.concat . map encodeCodepoint

-- | Decode a UTF-8 byte string to a codepoint list. Semantically
-- meaningful only when @'isValidUtf8' bs == True@; on malformed input
-- the walker yields the longest valid prefix and stops. Callers that
-- need failure propagation validate first via 'firstInvalidUtf8Offset'.
decodeToCodepoints :: ByteString -> [Int]
decodeToCodepoints bs = go ExpectStart 0 id
  where
    !n = BS.length bs

    go :: Utf8State -> Int -> ([Int] -> [Int]) -> [Int]
    go st i acc
      | i >= n    = acc []
      | otherwise =
          let b = BS.index bs i
          in case utf8DecodeStep st b of
               Continue next -> go next (i + 1) acc
               Emit cp next  -> go next (i + 1) (acc . (cp :))
               Reject _      -> acc []
