// Strict UTF-8 codec — validator, decoder, and encoder.
//
// The accepted byte set is exactly the strict RFC 3629 acceptance
// language: it rejects overlong encodings, surrogate codepoints
// (U+D800..U+DFFF), codepoints beyond U+10FFFF, truncated multi-
// byte sequences, invalid start bytes, and invalid continuation
// bytes.  The codec does not delegate to any host-stdlib UTF-8
// routine; the accepted byte set is closed-form per the spec.
//
// Offset convention for `first_invalid_utf8_offset`: the returned
// offset is the index of the byte on which the state machine
// transitions to reject.  For `OverlongEncoding` (detected on
// emission of a multi-byte sequence) the offset is the start byte
// of the sequence, not the last byte consumed.

#ifndef UNICODE_CPP_UTF8_HPP
#define UNICODE_CPP_UTF8_HPP

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <variant>
#include <vector>

#include "unicode_cpp/strict.hpp"

namespace unicode_cpp {

// ─────────────────────────────────────────────────────────────────────
// Decoder state
// ─────────────────────────────────────────────────────────────────────

// Start-of-codepoint state.
struct ExpectStart {};

// Open-multi-byte-sequence state.
//
// `remaining` is the count of continuation bytes still needed,
// `accum` is the codepoint bits accumulated so far, and `min_cp`
// is the smallest codepoint a sequence of this start-byte class
// is allowed to decode to (sequences below it are overlong).
struct ExpectCont {
    std::uint8_t remaining;
    std::uint32_t accum;
    std::uint32_t min_cp;
};

using Utf8State = std::variant<ExpectStart, ExpectCont>;

// ─────────────────────────────────────────────────────────────────────
// Decoder step result
// ─────────────────────────────────────────────────────────────────────

struct ContinueStep {
    Utf8State state;
};

struct EmitStep {
    std::uint32_t codepoint;
    Utf8State state;
};

struct RejectStep {
    Utf8RejectKind kind;
};

using Utf8StepResult = std::variant<ContinueStep, EmitStep, RejectStep>;

// ─────────────────────────────────────────────────────────────────────
// Decoder step
// ─────────────────────────────────────────────────────────────────────

// Process one byte given the current state.
//
// Start-byte ranges per RFC 3629:
//
//   0x00..0x7F — 1-byte ASCII, emit directly
//   0x80..0xBF — invalid as a start byte (continuation only)
//   0xC0..0xC1 — invalid (overlong 2-byte for ASCII)
//   0xC2..0xDF — 2-byte sequence, minimum codepoint 0x80
//   0xE0..0xEF — 3-byte sequence, minimum codepoint 0x800
//   0xF0..0xF4 — 4-byte sequence, minimum codepoint 0x10000
//   0xF5..0xFF — invalid (would encode codepoints > U+10FFFF)
//
// Continuation bytes must lie in 0x80..0xBF (top two bits `10`).
// On emission the decoded codepoint must be at or above the
// sequence's `min_cp` (else OverlongEncoding), outside the
// surrogate range U+D800..U+DFFF (else SurrogateCodepoint), and
// at or below U+10FFFF (else CodepointBeyondMax).
inline Utf8StepResult utf8_decode_step(
    const Utf8State& state,
    std::uint8_t byte) {
    const std::uint32_t n = byte;
    if (std::holds_alternative<ExpectStart>(state)) {
        if (n < 0x80) return EmitStep{n, ExpectStart{}};
        if (n < 0xC2) return RejectStep{Utf8RejectKind::InvalidStartByte};
        if (n < 0xE0)
            return ContinueStep{ExpectCont{1, n & 0x1Fu, 0x80u}};
        if (n < 0xF0)
            return ContinueStep{ExpectCont{2, n & 0x0Fu, 0x800u}};
        if (n < 0xF5)
            return ContinueStep{ExpectCont{3, n & 0x07u, 0x10000u}};
        return RejectStep{Utf8RejectKind::InvalidStartByte};
    }
    const auto& cont = std::get<ExpectCont>(state);
    if (n < 0x80 || n >= 0xC0)
        return RejectStep{Utf8RejectKind::InvalidContinuationByte};
    const std::uint32_t next = (cont.accum << 6) | (n & 0x3Fu);
    if (cont.remaining == 1) {
        if (next < cont.min_cp)
            return RejectStep{Utf8RejectKind::OverlongEncoding};
        if (next >= 0xD800u && next <= 0xDFFFu)
            return RejectStep{Utf8RejectKind::SurrogateCodepoint};
        if (next > 0x10FFFFu)
            return RejectStep{Utf8RejectKind::CodepointBeyondMax};
        return EmitStep{next, ExpectStart{}};
    }
    return ContinueStep{ExpectCont{
        static_cast<std::uint8_t>(cont.remaining - 1),
        next,
        cont.min_cp,
    }};
}

// ─────────────────────────────────────────────────────────────────────
// Walker
// ─────────────────────────────────────────────────────────────────────

struct InvalidOffset {
    std::size_t offset;
    Utf8RejectKind kind;
};

// The first byte offset at which the strict UTF-8 state machine
// rejects, or `std::nullopt` when the entire input is valid
// UTF-8.
//
// For `OverlongEncoding` the offset is the start byte of the
// offending sequence — the only reject category whose failure is
// decided at sequence end rather than at the byte transition that
// triggered detection.  Every other reject kind reports the byte
// that caused the rejection.  `TruncatedSequence` reports an
// offset equal to the input size.
inline std::optional<InvalidOffset> first_invalid_utf8_offset(
    std::span<const std::uint8_t> bytes) {
    Utf8State state = ExpectStart{};
    std::size_t seq_start = 0;
    for (std::size_t i = 0; i < bytes.size(); ++i) {
        if (std::holds_alternative<ExpectStart>(state)) {
            seq_start = i;
        }
        Utf8StepResult result = utf8_decode_step(state, bytes[i]);
        if (auto* cont = std::get_if<ContinueStep>(&result)) {
            state = cont->state;
        } else if (auto* emit = std::get_if<EmitStep>(&result)) {
            state = emit->state;
        } else {
            auto& rej = std::get<RejectStep>(result);
            if (rej.kind == Utf8RejectKind::OverlongEncoding)
                return InvalidOffset{seq_start, rej.kind};
            return InvalidOffset{i, rej.kind};
        }
    }
    if (std::holds_alternative<ExpectCont>(state)) {
        return InvalidOffset{
            bytes.size(),
            Utf8RejectKind::TruncatedSequence,
        };
    }
    return std::nullopt;
}

// Whole-input validity predicate: every byte participates in a
// valid RFC 3629 sequence.
inline bool is_valid_utf8(std::span<const std::uint8_t> bytes) {
    return !first_invalid_utf8_offset(bytes).has_value();
}

// ─────────────────────────────────────────────────────────────────────
// Encoder
// ─────────────────────────────────────────────────────────────────────

// Encode a single codepoint as a 1–4 byte UTF-8 sequence per
// UAX #44 §5.1.
//
// The function trusts its input: codepoints at or above 0x110000
// produce bogus output.  Callers feeding values from a UTF-8
// decode are safe by construction — the decoder rejects
// out-of-range values.  Callers synthesising codepoints from other
// sources should guard with a range check before encoding.
inline std::vector<std::uint8_t> encode_codepoint(std::uint32_t cp) {
    if (cp < 0x80u) {
        return {static_cast<std::uint8_t>(cp)};
    }
    if (cp < 0x800u) {
        return {
            static_cast<std::uint8_t>(0xC0u | (cp >> 6)),
            static_cast<std::uint8_t>(0x80u | (cp & 0x3Fu)),
        };
    }
    if (cp < 0x10000u) {
        return {
            static_cast<std::uint8_t>(0xE0u | (cp >> 12)),
            static_cast<std::uint8_t>(0x80u | ((cp >> 6) & 0x3Fu)),
            static_cast<std::uint8_t>(0x80u | (cp & 0x3Fu)),
        };
    }
    return {
        static_cast<std::uint8_t>(0xF0u | (cp >> 18)),
        static_cast<std::uint8_t>(0x80u | ((cp >> 12) & 0x3Fu)),
        static_cast<std::uint8_t>(0x80u | ((cp >> 6) & 0x3Fu)),
        static_cast<std::uint8_t>(0x80u | (cp & 0x3Fu)),
    };
}

// Concatenate the UTF-8 encodings of a codepoint sequence.
inline std::vector<std::uint8_t> encode_codepoints(
    std::span<const std::uint32_t> cps) {
    std::vector<std::uint8_t> out;
    out.reserve(cps.size());
    for (std::uint32_t cp : cps) {
        auto part = encode_codepoint(cp);
        out.insert(out.end(), part.begin(), part.end());
    }
    return out;
}

// Decode a UTF-8 byte string to a codepoint vector.  Semantically
// meaningful only when the input is valid UTF-8; on malformed
// input the walker yields the longest valid prefix and stops.
// Callers that need explicit failure propagation should validate
// first via `first_invalid_utf8_offset`.
inline std::vector<std::uint32_t> decode_to_codepoints(
    std::span<const std::uint8_t> bytes) {
    std::vector<std::uint32_t> out;
    Utf8State state = ExpectStart{};
    for (std::uint8_t b : bytes) {
        Utf8StepResult result = utf8_decode_step(state, b);
        if (auto* cont = std::get_if<ContinueStep>(&result)) {
            state = cont->state;
        } else if (auto* emit = std::get_if<EmitStep>(&result)) {
            out.push_back(emit->codepoint);
            state = emit->state;
        } else {
            return out;
        }
    }
    return out;
}

}  // namespace unicode_cpp

#endif  // UNICODE_CPP_UTF8_HPP
