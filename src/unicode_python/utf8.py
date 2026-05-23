"""Strict UTF-8 codec — validator, decoder, and encoder.

The accepted byte set is exactly the strict RFC 3629 acceptance
language: it rejects overlong encodings, surrogate codepoints
(U+D800..U+DFFF), codepoints beyond U+10FFFF, truncated multi-byte
sequences, invalid start bytes, and invalid continuation bytes.
The codec does not delegate to Python's built-in ``bytes.decode``;
the accepted byte set is closed-form per the spec.

Offset convention for :func:`first_invalid_utf8_offset`: the
returned offset is the index of the byte on which the state
machine transitions to reject.  For ``OVERLONG_ENCODING``
(detected on emission of a multi-byte sequence) the offset is the
start byte of the sequence, not the last byte consumed.
"""

from dataclasses import dataclass
from typing import Tuple, Union

from .strict import Utf8RejectKind


# ─────────────────────────────────────────────────────────────────────
# Decoder state
# ─────────────────────────────────────────────────────────────────────


@dataclass(frozen=True, slots=True)
class ExpectStart:
    """Start-of-codepoint state."""


@dataclass(frozen=True, slots=True)
class ExpectCont:
    """Open-multi-byte-sequence state.

    Attributes
    ----------
    remaining : int
        Continuation bytes still needed to complete the sequence.
    accum : int
        Codepoint bits accumulated so far.
    min_cp : int
        Smallest codepoint a sequence of this start-byte class is
        allowed to decode to; sequences below it are overlong.
    """

    remaining: int
    accum: int
    min_cp: int


Utf8State = Union[ExpectStart, ExpectCont]


# ─────────────────────────────────────────────────────────────────────
# Decoder step result
# ─────────────────────────────────────────────────────────────────────


@dataclass(frozen=True, slots=True)
class Continue:
    """The decoder advances to a new state without emitting."""

    state: Utf8State


@dataclass(frozen=True, slots=True)
class Emit:
    """The decoder completes a codepoint and returns to a new state."""

    codepoint: int
    state: Utf8State


@dataclass(frozen=True, slots=True)
class Reject:
    """The decoder rejects with a categorised cause."""

    kind: Utf8RejectKind


Utf8StepResult = Union[Continue, Emit, Reject]


# ─────────────────────────────────────────────────────────────────────
# Decoder step
# ─────────────────────────────────────────────────────────────────────


def utf8_decode_step(state: Utf8State, byte: int) -> Utf8StepResult:
    """Process one byte given the current state.

    Start-byte ranges per RFC 3629:

      * 0x00..0x7F — 1-byte ASCII, emit directly
      * 0x80..0xBF — invalid as a start byte (continuation only)
      * 0xC0..0xC1 — invalid (overlong 2-byte for ASCII)
      * 0xC2..0xDF — 2-byte sequence, minimum codepoint 0x80
      * 0xE0..0xEF — 3-byte sequence, minimum codepoint 0x800
      * 0xF0..0xF4 — 4-byte sequence, minimum codepoint 0x10000
      * 0xF5..0xFF — invalid (would encode codepoints > U+10FFFF)

    Continuation bytes must lie in 0x80..0xBF (top two bits
    ``10``).  On emission the decoded codepoint must be at or above
    the sequence's ``min_cp`` (else ``OVERLONG_ENCODING``), outside
    the surrogate range U+D800..U+DFFF (else
    ``SURROGATE_CODEPOINT``), and at or below U+10FFFF (else
    ``CODEPOINT_BEYOND_MAX``).
    """
    n = byte & 0xFF
    if isinstance(state, ExpectStart):
        if n < 0x80:
            return Emit(n, ExpectStart())
        if n < 0xC2:
            return Reject(Utf8RejectKind.INVALID_START_BYTE)
        if n < 0xE0:
            return Continue(ExpectCont(1, n & 0x1F, 0x80))
        if n < 0xF0:
            return Continue(ExpectCont(2, n & 0x0F, 0x800))
        if n < 0xF5:
            return Continue(ExpectCont(3, n & 0x07, 0x10000))
        return Reject(Utf8RejectKind.INVALID_START_BYTE)
    # ExpectCont
    if n < 0x80 or n >= 0xC0:
        return Reject(Utf8RejectKind.INVALID_CONTINUATION_BYTE)
    nxt = (state.accum << 6) | (n & 0x3F)
    if state.remaining == 1:
        if nxt < state.min_cp:
            return Reject(Utf8RejectKind.OVERLONG_ENCODING)
        if 0xD800 <= nxt <= 0xDFFF:
            return Reject(Utf8RejectKind.SURROGATE_CODEPOINT)
        if nxt > 0x10FFFF:
            return Reject(Utf8RejectKind.CODEPOINT_BEYOND_MAX)
        return Emit(nxt, ExpectStart())
    return Continue(ExpectCont(state.remaining - 1, nxt, state.min_cp))


# ─────────────────────────────────────────────────────────────────────
# Walker
# ─────────────────────────────────────────────────────────────────────


def first_invalid_utf8_offset(
    data: bytes,
) -> Tuple[int, Utf8RejectKind] | None:
    """First reject offset, or ``None`` when the input is valid UTF-8.

    For ``OVERLONG_ENCODING`` the offset is the start byte of the
    offending sequence — the only reject category whose failure is
    decided at sequence end rather than at the byte transition that
    triggered detection.  Every other reject kind reports the byte
    that caused the rejection.  ``TRUNCATED_SEQUENCE`` reports an
    offset equal to ``len(data)``.
    """
    state: Utf8State = ExpectStart()
    seq_start = 0
    for i, b in enumerate(data):
        if isinstance(state, ExpectStart):
            seq_start = i
        result = utf8_decode_step(state, b)
        if isinstance(result, Continue):
            state = result.state
        elif isinstance(result, Emit):
            state = result.state
        else:
            if result.kind is Utf8RejectKind.OVERLONG_ENCODING:
                return (seq_start, result.kind)
            return (i, result.kind)
    if isinstance(state, ExpectCont):
        return (len(data), Utf8RejectKind.TRUNCATED_SEQUENCE)
    return None


def is_valid_utf8(data: bytes) -> bool:
    """Whole-input validity predicate: every byte participates in
    a valid RFC 3629 sequence."""
    return first_invalid_utf8_offset(data) is None


# ─────────────────────────────────────────────────────────────────────
# Encoder
# ─────────────────────────────────────────────────────────────────────


def encode_codepoint(cp: int) -> bytes:
    """Encode a single codepoint as a 1–4 byte UTF-8 sequence per
    UAX #44 §5.1.

    The function trusts its input: codepoints at or above 0x110000
    produce bogus output.  Callers feeding values from a UTF-8
    decode are safe by construction — the decoder rejects
    out-of-range values.  Callers synthesising codepoints from
    other sources should guard with a range check before encoding.
    """
    if cp < 0x80:
        return bytes([cp])
    if cp < 0x800:
        return bytes([0xC0 | (cp >> 6), 0x80 | (cp & 0x3F)])
    if cp < 0x10000:
        return bytes(
            [
                0xE0 | (cp >> 12),
                0x80 | ((cp >> 6) & 0x3F),
                0x80 | (cp & 0x3F),
            ]
        )
    return bytes(
        [
            0xF0 | (cp >> 18),
            0x80 | ((cp >> 12) & 0x3F),
            0x80 | ((cp >> 6) & 0x3F),
            0x80 | (cp & 0x3F),
        ]
    )


def encode_codepoints(cps: list[int]) -> bytes:
    """Concatenate the UTF-8 encodings of a codepoint sequence."""
    return b"".join(encode_codepoint(cp) for cp in cps)


def decode_to_codepoints(data: bytes) -> list[int]:
    """Decode a UTF-8 byte string to a codepoint list.  Semantically
    meaningful only when the input is valid UTF-8; on malformed
    input the walker yields the longest valid prefix and stops.
    Callers that need explicit failure propagation should validate
    first via :func:`first_invalid_utf8_offset`.
    """
    out: list[int] = []
    state: Utf8State = ExpectStart()
    for b in data:
        result = utf8_decode_step(state, b)
        if isinstance(result, Continue):
            state = result.state
        elif isinstance(result, Emit):
            out.append(result.codepoint)
            state = result.state
        else:
            return out
    return out


__all__ = [
    "Continue",
    "Emit",
    "ExpectCont",
    "ExpectStart",
    "Reject",
    "Utf8State",
    "Utf8StepResult",
    "decode_to_codepoints",
    "encode_codepoint",
    "encode_codepoints",
    "first_invalid_utf8_offset",
    "is_valid_utf8",
    "utf8_decode_step",
]
