"""Strict-UTF-8 reject taxonomy.

The six variants enumerate every category of byte sequence that a
strict RFC 3629 decoder rejects:

  * ``OverlongEncoding`` — a multi-byte sequence whose decoded
    codepoint is below the minimum for that sequence length.
  * ``SurrogateCodepoint`` — a sequence decoding to U+D800..U+DFFF,
    the UTF-16 surrogate range, which is not a valid scalar.
  * ``CodepointBeyondMax`` — a sequence decoding to a value above
    U+10FFFF, the Unicode scalar ceiling.
  * ``TruncatedSequence`` — the byte stream ends mid-codepoint.
  * ``InvalidStartByte`` — a byte that cannot begin any UTF-8
    codepoint (0x80..0xC1, 0xF5..0xFF).
  * ``InvalidContinuationByte`` — a byte appearing in a
    continuation position whose top two bits are not ``10``.
"""

from enum import Enum


class Utf8RejectKind(Enum):
    """Categorised cause of a strict-UTF-8 rejection."""

    OVERLONG_ENCODING = "OverlongEncoding"
    SURROGATE_CODEPOINT = "SurrogateCodepoint"
    CODEPOINT_BEYOND_MAX = "CodepointBeyondMax"
    TRUNCATED_SEQUENCE = "TruncatedSequence"
    INVALID_START_BYTE = "InvalidStartByte"
    INVALID_CONTINUATION_BYTE = "InvalidContinuationByte"


__all__ = ["Utf8RejectKind"]
