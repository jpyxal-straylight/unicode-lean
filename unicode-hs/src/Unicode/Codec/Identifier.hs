{-|
Module      : Unicode.Codec.Identifier
Description : Strict ASCII identifier predicate — @[a-zA-Z_][a-zA-Z0-9_]*@.

Haskell port of @Unicode.Codec.Identifier@ from unicode-lean.

  * First byte MUST be in @0x41..0x5A@ (A–Z), @0x61..0x7A@ (a–z), or @0x5F@ (_).
  * Subsequent bytes MUST be in the first-byte set OR @0x30..0x39@ (0–9).
  * Empty byte sequences are REJECTED.

This codec stays strict ASCII permanently. Callers needing Unicode
identifiers use a separate PRECIS identifier codec per RFC 8264 / 8265,
providing defense-in-depth: ASCII belt + PRECIS suspenders. The PRECIS
codec ships in a later phase once UCD-table-backed atoms come online.

The refinement type @IdentifierUtf8 (maxBytes :: Nat)@ matches the
Lean structure @IdentifierUtf8 (maxBytes : Nat)@: the size bound is
type-level, so @IdentifierUtf8 32@ and @IdentifierUtf8 64@ are distinct
types.
-}
module Unicode.Codec.Identifier
  ( -- * Byte-class predicates
    isIdentifierStartByte
  , isIdentifierContinueByte
    -- * Aggregate predicate
  , isValidIdentifierBytes
    -- * Walker
  , firstInvalidIdentifierContinueFrom
    -- * Refinement type
  , IdentifierUtf8
  , identifierUtf8OfBytes
  , identifierUtf8Bytes
  , identifierUtf8MaxBytes
  ) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Proxy (Proxy (Proxy))
import Data.Word (Word8)
import GHC.TypeLits (KnownNat, Nat, natVal)

-- | True iff @b@ may start an ASCII identifier: @A..Z@, @a..z@, or @_@.
isIdentifierStartByte :: Word8 -> Bool
isIdentifierStartByte b =
  (b >= 0x41 && b <= 0x5A)
    || (b >= 0x61 && b <= 0x7A)
    || b == 0x5F

-- | True iff @b@ may continue an ASCII identifier: start-byte set plus
-- @0..9@.
isIdentifierContinueByte :: Word8 -> Bool
isIdentifierContinueByte b =
  isIdentifierStartByte b
    || (b >= 0x30 && b <= 0x39)

-- | Walk the continuation positions of @bs@ starting at @i@, returning
-- the offset and value of the first byte that fails
-- 'isIdentifierContinueByte'. Returns 'Nothing' when every position
-- from @i@ onward is a valid continuation byte.
firstInvalidIdentifierContinueFrom :: ByteString -> Int -> Maybe (Int, Word8)
firstInvalidIdentifierContinueFrom bs = go
  where
    !n = BS.length bs

    go :: Int -> Maybe (Int, Word8)
    go i
      | i >= n                         = Nothing
      | isIdentifierContinueByte b     = go (i + 1)
      | otherwise                      = Just (i, b)
      where
        b = BS.index bs i

-- | ASCII-identifier predicate: non-empty, valid start byte at position
-- zero, and every subsequent byte a valid continuation byte.
isValidIdentifierBytes :: ByteString -> Bool
isValidIdentifierBytes bs
  | BS.null bs = False
  | otherwise  =
      isIdentifierStartByte (BS.index bs 0)
        && case firstInvalidIdentifierContinueFrom bs 1 of
             Nothing -> True
             Just _  -> False

-- | A byte sequence carrying its (type-level) size bound and
-- identifier-validity claim. Constructor is hidden;
-- 'identifierUtf8OfBytes' is the only entry point.
newtype IdentifierUtf8 (n :: Nat) = MkIdentifierUtf8 ByteString
  deriving stock (Eq, Show)

-- | Build an 'IdentifierUtf8' from a 'ByteString' under the type-level
-- size bound @n@. Returns 'Nothing' when either the bound or identifier
-- validity is violated. Callers specify @n@ via @TypeApplications@:
--
-- > case identifierUtf8OfBytes @16 someBytes of
-- >   Just ident -> ...
-- >   Nothing    -> ...
identifierUtf8OfBytes
  :: forall n
   . KnownNat n
  => ByteString -> Maybe (IdentifierUtf8 n)
identifierUtf8OfBytes bs
  | fromIntegral (BS.length bs) <= natVal (Proxy @n)
      && isValidIdentifierBytes bs =
      Just (MkIdentifierUtf8 bs)
  | otherwise = Nothing

-- | The underlying bytes of the identifier.
identifierUtf8Bytes :: IdentifierUtf8 n -> ByteString
identifierUtf8Bytes (MkIdentifierUtf8 bs) = bs

-- | The type-level size bound, reflected to 'Integer' at runtime.
identifierUtf8MaxBytes :: forall n. KnownNat n => IdentifierUtf8 n -> Integer
identifierUtf8MaxBytes _ = natVal (Proxy @n)
