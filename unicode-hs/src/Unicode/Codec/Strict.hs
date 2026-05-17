{-|
Module      : Unicode.Codec.Strict
Description : Shared rejection-cause enums for the strict text codecs.

Haskell port of @Unicode.Codec.Strict@ from unicode-lean. Phase 1 exports
only the UTF-8 reject-kind enum; the broader 'RejectReason' /
'StrictParseResult' / 'StrictBox' family lands when the table-free codecs
beyond UTF-8 are ported.
-}
module Unicode.Codec.Strict
  ( Utf8RejectKind (..)
  ) where

-- | Why the UTF-8 state machine transitioned to the reject state. Mirrors
-- the Lean inductive of the same name in @Unicode/Codec/Strict.lean@.
data Utf8RejectKind
  = InvalidStartByte
  | TruncatedSequence
  | OverlongEncoding
  | SurrogateCodepoint
  | CodepointBeyondMax
  | InvalidContinuationByte
  deriving stock (Eq, Show, Ord)
