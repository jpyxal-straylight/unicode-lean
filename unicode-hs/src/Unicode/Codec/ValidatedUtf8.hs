{-|
Module      : Unicode.Codec.ValidatedUtf8
Description : Refinement type for bytes validated as strict RFC 3629 UTF-8.

Haskell port of @Unicode.Codec.ValidatedUtf8@ from unicode-lean.

The validity claim is pinned at the module-boundary level: the only way
to construct a 'ValidatedUtf8' is via the smart constructor
'validateUtf8', which routes through the decoder state machine in
"Unicode.Codec.Utf8". The data constructor is not exported.

Rationale: the ingestion layer is security-critical. A plain
'ByteString' field on a codec output type carries no claim about its
UTF-8 validity — downstream consumers have to either re-validate or
trust that the producer validated (and hope the producer didn't
regress). 'ValidatedUtf8' makes the claim module-level, so a downstream
consumer that wants the raw bytes has to explicitly 'unwrap' — which
reads as "I am consuming the RFC 3629 claim here".

The Lean version carries the validity proof in a structure field; the
Haskell counterpart carries it as the unfakeable smart-constructor
discharge instead. Module-boundary opaqueness is the discipline.
-}
module Unicode.Codec.ValidatedUtf8
  ( -- * Refinement type
    ValidatedUtf8
    -- * Smart constructor
  , validateUtf8
    -- * Accessor
  , unwrap
  ) where

import Data.ByteString (ByteString)

import Unicode.Codec.Utf8 (isValidUtf8)

-- | A 'ByteString' that has been validated as strict RFC 3629 UTF-8.
-- The constructor is intentionally not exported; 'validateUtf8' is the
-- only blessed way to build a 'ValidatedUtf8'.
newtype ValidatedUtf8 = MkValidatedUtf8 ByteString
  deriving stock (Eq, Show, Ord)

-- | Validate a 'ByteString' and, on success, return a 'ValidatedUtf8'
-- carrying the RFC 3629 validity claim. Returns 'Nothing' when the
-- bytes fail the strict state machine (overlong, surrogate, > U+10FFFF,
-- invalid start/continuation, truncated).
--
-- The input bytes are shared by reference; no copy, no normalisation.
validateUtf8 :: ByteString -> Maybe ValidatedUtf8
validateUtf8 bs
  | isValidUtf8 bs = Just (MkValidatedUtf8 bs)
  | otherwise      = Nothing

-- | Consume the validity claim, returning the underlying 'ByteString'.
-- After this call the validity claim is no longer carried at the
-- module-boundary level — the caller owns the "these bytes are RFC 3629
-- valid" reasoning from here forward.
unwrap :: ValidatedUtf8 -> ByteString
unwrap (MkValidatedUtf8 bs) = bs
