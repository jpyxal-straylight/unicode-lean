//! Strict UTF-8 codec — validator, decoder, and encoder.
//!
//! The accepted byte set is exactly the strict RFC 3629 acceptance
//! language: it rejects overlong encodings, surrogate codepoints
//! (U+D800..U+DFFF), codepoints beyond U+10FFFF, truncated
//! multi-byte sequences, invalid start bytes, and invalid
//! continuation bytes.  The codec does not delegate to `str`'s
//! built-in UTF-8 validator; the accepted byte set is closed-form
//! per the spec.
//!
//! Offset convention for `first_invalid_utf8_offset`: the returned
//! offset is the index of the byte on which the state machine
//! transitions to reject.  For `OverlongEncoding` (detected on
//! emission of a multi-byte sequence) the offset is the start byte
//! of the sequence, not the last byte consumed.

use crate::strict::Utf8RejectKind;

// ─────────────────────────────────────────────────────────────────────
// Decoder state
// ─────────────────────────────────────────────────────────────────────

/// UTF-8 decoder state.
///
/// `ExpectStart` is the start-of-codepoint state.  `ExpectCont`
/// tracks an open multi-byte sequence with three fields:
///
///   - `remaining` — continuation bytes still needed
///   - `accum`     — codepoint bits accumulated so far
///   - `min_cp`    — smallest codepoint a sequence of this
///                   start-byte class is allowed to decode to;
///                   sequences below it are overlong.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Utf8State {
    ExpectStart,
    ExpectCont {
        remaining: u8,
        accum: u32,
        min_cp: u32,
    },
}

/// The outcome of a single decoder step: either advance to a new
/// state, emit a complete codepoint with the next state, or reject
/// with a categorised cause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Utf8StepResult {
    Continue(Utf8State),
    Emit(u32, Utf8State),
    Reject(Utf8RejectKind),
}

// ─────────────────────────────────────────────────────────────────────
// Decoder step
// ─────────────────────────────────────────────────────────────────────

/// Process one byte given the current state.
///
/// Start-byte ranges per RFC 3629:
///
///   0x00..0x7F — 1-byte ASCII, emit directly
///   0x80..0xBF — invalid as a start byte (continuation only)
///   0xC0..0xC1 — invalid (overlong 2-byte for ASCII)
///   0xC2..0xDF — 2-byte sequence, minimum codepoint 0x80
///   0xE0..0xEF — 3-byte sequence, minimum codepoint 0x800
///   0xF0..0xF4 — 4-byte sequence, minimum codepoint 0x10000
///   0xF5..0xFF — invalid (would encode codepoints > U+10FFFF)
///
/// Continuation bytes must lie in 0x80..0xBF (top two bits `10`).
/// On emission, the decoded codepoint must be at or above the
/// sequence's `min_cp` (else `OverlongEncoding`), outside the
/// surrogate range U+D800..U+DFFF (else `SurrogateCodepoint`), and
/// at or below U+10FFFF (else `CodepointBeyondMax`).
pub fn utf8_decode_step(state: Utf8State, byte: u8) -> Utf8StepResult {
    let n = u32::from(byte);
    match state {
        Utf8State::ExpectStart => {
            if n < 0x80 {
                Utf8StepResult::Emit(n, Utf8State::ExpectStart)
            } else if n < 0xC2 {
                Utf8StepResult::Reject(Utf8RejectKind::InvalidStartByte)
            } else if n < 0xE0 {
                Utf8StepResult::Continue(Utf8State::ExpectCont {
                    remaining: 1,
                    accum: n & 0x1F,
                    min_cp: 0x80,
                })
            } else if n < 0xF0 {
                Utf8StepResult::Continue(Utf8State::ExpectCont {
                    remaining: 2,
                    accum: n & 0x0F,
                    min_cp: 0x800,
                })
            } else if n < 0xF5 {
                Utf8StepResult::Continue(Utf8State::ExpectCont {
                    remaining: 3,
                    accum: n & 0x07,
                    min_cp: 0x10000,
                })
            } else {
                Utf8StepResult::Reject(Utf8RejectKind::InvalidStartByte)
            }
        }
        Utf8State::ExpectCont { remaining, accum, min_cp } => {
            if n < 0x80 || n >= 0xC0 {
                return Utf8StepResult::Reject(
                    Utf8RejectKind::InvalidContinuationByte,
                );
            }
            let next = (accum << 6) | (n & 0x3F);
            if remaining == 1 {
                if next < min_cp {
                    Utf8StepResult::Reject(Utf8RejectKind::OverlongEncoding)
                } else if (0xD800..=0xDFFF).contains(&next) {
                    Utf8StepResult::Reject(Utf8RejectKind::SurrogateCodepoint)
                } else if next > 0x10FFFF {
                    Utf8StepResult::Reject(Utf8RejectKind::CodepointBeyondMax)
                } else {
                    Utf8StepResult::Emit(next, Utf8State::ExpectStart)
                }
            } else {
                Utf8StepResult::Continue(Utf8State::ExpectCont {
                    remaining: remaining - 1,
                    accum: next,
                    min_cp,
                })
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────
// Walker
// ─────────────────────────────────────────────────────────────────────

/// The first byte offset at which the strict UTF-8 state machine
/// rejects, or `None` when the entire input is valid UTF-8.
///
/// For `OverlongEncoding` the offset is the start byte of the
/// offending sequence — the only reject category whose failure is
/// decided at sequence end rather than at the byte transition that
/// triggered detection.  Every other reject kind reports the byte
/// that caused the rejection.  `TruncatedSequence` reports an
/// offset equal to the input length.
pub fn first_invalid_utf8_offset(
    bytes: &[u8],
) -> Option<(usize, Utf8RejectKind)> {
    let mut state = Utf8State::ExpectStart;
    let mut seq_start = 0;
    for (i, &b) in bytes.iter().enumerate() {
        if matches!(state, Utf8State::ExpectStart) {
            seq_start = i;
        }
        match utf8_decode_step(state, b) {
            Utf8StepResult::Continue(s) => state = s,
            Utf8StepResult::Emit(_, s) => state = s,
            Utf8StepResult::Reject(kind) => {
                if kind == Utf8RejectKind::OverlongEncoding {
                    return Some((seq_start, kind));
                }
                return Some((i, kind));
            }
        }
    }
    if matches!(state, Utf8State::ExpectCont { .. }) {
        Some((bytes.len(), Utf8RejectKind::TruncatedSequence))
    } else {
        None
    }
}

/// Whole-input validity predicate: every byte participates in a
/// valid RFC 3629 sequence.
pub fn is_valid_utf8(bytes: &[u8]) -> bool {
    first_invalid_utf8_offset(bytes).is_none()
}

// ─────────────────────────────────────────────────────────────────────
// Encoder
// ─────────────────────────────────────────────────────────────────────

/// Encode a single codepoint as a 1–4 byte UTF-8 sequence per
/// UAX #44 §5.1.
///
/// The function trusts its input: codepoints at or above 0x110000
/// produce bogus output.  Callers feeding values from a UTF-8
/// decode are safe by construction — the decoder rejects out-of-
/// range values.  Callers synthesising codepoints from other
/// sources should guard with a range check before encoding.
pub fn encode_codepoint(cp: u32) -> Vec<u8> {
    if cp < 0x80 {
        vec![cp as u8]
    } else if cp < 0x800 {
        vec![
            (0xC0 | (cp >> 6)) as u8,
            (0x80 | (cp & 0x3F)) as u8,
        ]
    } else if cp < 0x10000 {
        vec![
            (0xE0 | (cp >> 12)) as u8,
            (0x80 | ((cp >> 6) & 0x3F)) as u8,
            (0x80 | (cp & 0x3F)) as u8,
        ]
    } else {
        vec![
            (0xF0 | (cp >> 18)) as u8,
            (0x80 | ((cp >> 12) & 0x3F)) as u8,
            (0x80 | ((cp >> 6) & 0x3F)) as u8,
            (0x80 | (cp & 0x3F)) as u8,
        ]
    }
}

/// Concatenate the UTF-8 encodings of a codepoint sequence.
pub fn encode_codepoints(cps: &[u32]) -> Vec<u8> {
    let mut out = Vec::with_capacity(cps.len());
    for &cp in cps {
        out.extend(encode_codepoint(cp));
    }
    out
}

/// Decode a UTF-8 byte string to a codepoint vector.  Semantically
/// meaningful only when the input is valid UTF-8; on malformed
/// input the walker yields the longest valid prefix and stops.
/// Callers that need explicit failure propagation should validate
/// first via `first_invalid_utf8_offset`.
pub fn decode_to_codepoints(bytes: &[u8]) -> Vec<u32> {
    let mut out = Vec::new();
    let mut state = Utf8State::ExpectStart;
    for &b in bytes {
        match utf8_decode_step(state, b) {
            Utf8StepResult::Continue(s) => state = s,
            Utf8StepResult::Emit(cp, s) => {
                out.push(cp);
                state = s;
            }
            Utf8StepResult::Reject(_) => return out,
        }
    }
    out
}
