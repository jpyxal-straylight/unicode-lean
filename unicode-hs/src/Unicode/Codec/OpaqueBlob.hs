{-|
Module      : Unicode.Codec.OpaqueBlob
Description : Opaque text predicate — structurally valid UTF-8, size-bounded.

Haskell port of @Unicode.Codec.OpaqueBlob@ from unicode-lean.

No character-class or codepoint filtering beyond UTF-8 validity.
Intended for callers who apply their own text hardening downstream;
hardened identifier and printable profiles layer on top of this
predicate (e.g. RFC 8264 IdentifierClass) and are exposed as separate
modules.

The Lean structure @Utf8Blob (maxBytes : Nat)@ is parameterised at the
type level on the size bound: @Utf8Blob 32@ and @Utf8Blob 64@ are
distinct types. The Haskell counterpart matches that via @DataKinds@ +
@KnownNat@ — every @Utf8Blob n@ is a separate type, and a value-level
size check at the smart-constructor boundary discharges @bytes.size <=
n@.

Three layers:

  * 'isUtf8Blob'          — Boolean validity predicate.
  * 'Utf8Blob'            — refinement type parameterised on the
                            type-level size bound, with hidden
                            constructor.
  * 'utf8BlobOfBytes'     — smart constructor; the bound is supplied via
                            @TypeApplications@.
-}
module Unicode.Codec.OpaqueBlob
  ( -- * Predicate
    isUtf8Blob
    -- * Refinement type
  , Utf8Blob
    -- * Construction + accessors
  , utf8BlobOfBytes
  , utf8BlobBytes
  , utf8BlobMaxBytes
  ) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Proxy (Proxy (Proxy))
import GHC.TypeLits (KnownNat, Nat, natVal)

import Unicode.Codec.Utf8 (isValidUtf8)

-- | Opaque-blob predicate: structurally valid UTF-8. Equivalent to
-- 'isValidUtf8' — exposed under this name so the "blob" framing (no
-- character-class hardening) is explicit at the call site.
isUtf8Blob :: ByteString -> Bool
isUtf8Blob = isValidUtf8

-- | A byte sequence carrying its (type-level) size bound and UTF-8
-- validity claim. Constructor is hidden; 'utf8BlobOfBytes' is the only
-- entry point.
newtype Utf8Blob (n :: Nat) = MkUtf8Blob ByteString
  deriving stock (Eq, Show)

-- | Build a 'Utf8Blob' from a 'ByteString' under the type-level size
-- bound @n@. Returns 'Nothing' when either the bound or UTF-8 validity
-- is violated. Callers specify @n@ via @TypeApplications@:
--
-- > case utf8BlobOfBytes @32 someBytes of
-- >   Just blob -> ...
-- >   Nothing   -> ...
utf8BlobOfBytes
  :: forall n
   . KnownNat n
  => ByteString -> Maybe (Utf8Blob n)
utf8BlobOfBytes bs
  | fromIntegral (BS.length bs) <= natVal (Proxy @n) && isUtf8Blob bs =
      Just (MkUtf8Blob bs)
  | otherwise = Nothing

-- | The underlying bytes of the blob.
utf8BlobBytes :: Utf8Blob n -> ByteString
utf8BlobBytes (MkUtf8Blob bs) = bs

-- | The type-level size bound, reflected to 'Integer' at runtime.
utf8BlobMaxBytes :: forall n. KnownNat n => Utf8Blob n -> Integer
utf8BlobMaxBytes _ = natVal (Proxy @n)
