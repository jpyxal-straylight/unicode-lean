// UTF-16 codec — big-endian and little-endian variants.
//
// Each scalar Unicode codepoint encodes to either 2 bytes (BMP)
// or 4 bytes (supplementary planes via surrogate pair).  The
// supplementary pair is constructed as
//
//   X    = cp - 0x10000          (20-bit value)
//   high = 0xD800 + (X >> 10)    (high surrogate, 0xD800..0xDBFF)
//   low  = 0xDC00 + (X & 0x3FF)  (low  surrogate, 0xDC00..0xDFFF)
//
// The decoder rejects inputs whose length is not exactly 2 or 4,
// 2-byte sequences in the surrogate range U+D800..U+DFFF (lone
// surrogate), and 4-byte sequences not forming a valid (high,
// low) surrogate pair.

#ifndef UNICODE_CPP_UTF16_HPP
#define UNICODE_CPP_UTF16_HPP

#include <cstdint>
#include <optional>
#include <span>
#include <vector>

namespace unicode_cpp::utf16 {

// Encode a scalar codepoint as 2 or 4 bytes in big-endian UTF-16.
// The function trusts its input: codepoints outside the valid
// scalar range produce bogus output.
inline std::vector<std::uint8_t> encode_one_be(std::uint32_t cp) {
    if (cp < 0x10000u) {
        return {
            static_cast<std::uint8_t>((cp >> 8) & 0xFFu),
            static_cast<std::uint8_t>(cp & 0xFFu),
        };
    }
    const std::uint32_t x = cp - 0x10000u;
    const std::uint32_t high = 0xD800u + (x >> 10);
    const std::uint32_t low = 0xDC00u + (x & 0x3FFu);
    return {
        static_cast<std::uint8_t>((high >> 8) & 0xFFu),
        static_cast<std::uint8_t>(high & 0xFFu),
        static_cast<std::uint8_t>((low >> 8) & 0xFFu),
        static_cast<std::uint8_t>(low & 0xFFu),
    };
}

// Encode a scalar codepoint as 2 or 4 bytes in little-endian UTF-16.
inline std::vector<std::uint8_t> encode_one_le(std::uint32_t cp) {
    if (cp < 0x10000u) {
        return {
            static_cast<std::uint8_t>(cp & 0xFFu),
            static_cast<std::uint8_t>((cp >> 8) & 0xFFu),
        };
    }
    const std::uint32_t x = cp - 0x10000u;
    const std::uint32_t high = 0xD800u + (x >> 10);
    const std::uint32_t low = 0xDC00u + (x & 0x3FFu);
    return {
        static_cast<std::uint8_t>(high & 0xFFu),
        static_cast<std::uint8_t>((high >> 8) & 0xFFu),
        static_cast<std::uint8_t>(low & 0xFFu),
        static_cast<std::uint8_t>((low >> 8) & 0xFFu),
    };
}

namespace detail {
inline std::optional<std::uint32_t> scalar_from_pair(
    std::uint32_t high, std::uint32_t low) {
    if (high < 0xD800u || high > 0xDBFFu) return std::nullopt;
    if (low < 0xDC00u || low > 0xDFFFu) return std::nullopt;
    return 0x10000u + ((high - 0xD800u) << 10) + (low - 0xDC00u);
}
}  // namespace detail

// Decode a UTF-16 BE byte sequence as a single codepoint.
// Returns std::nullopt on length mismatch, lone surrogate, or
// invalid surrogate pair.  Accepts byte sequences of length
// exactly 2 (BMP) or 4 (supplementary-plane surrogate pair).
inline std::optional<std::uint32_t> decode_one_be(
    std::span<const std::uint8_t> bytes) {
    if (bytes.size() == 2) {
        std::uint32_t u =
            (static_cast<std::uint32_t>(bytes[0]) << 8) |
            static_cast<std::uint32_t>(bytes[1]);
        if (u >= 0xD800u && u <= 0xDFFFu) return std::nullopt;
        return u;
    }
    if (bytes.size() == 4) {
        std::uint32_t high =
            (static_cast<std::uint32_t>(bytes[0]) << 8) |
            static_cast<std::uint32_t>(bytes[1]);
        std::uint32_t low =
            (static_cast<std::uint32_t>(bytes[2]) << 8) |
            static_cast<std::uint32_t>(bytes[3]);
        return detail::scalar_from_pair(high, low);
    }
    return std::nullopt;
}

// Decode a UTF-16 LE byte sequence as a single codepoint.
inline std::optional<std::uint32_t> decode_one_le(
    std::span<const std::uint8_t> bytes) {
    if (bytes.size() == 2) {
        std::uint32_t u =
            static_cast<std::uint32_t>(bytes[0]) |
            (static_cast<std::uint32_t>(bytes[1]) << 8);
        if (u >= 0xD800u && u <= 0xDFFFu) return std::nullopt;
        return u;
    }
    if (bytes.size() == 4) {
        std::uint32_t high =
            static_cast<std::uint32_t>(bytes[0]) |
            (static_cast<std::uint32_t>(bytes[1]) << 8);
        std::uint32_t low =
            static_cast<std::uint32_t>(bytes[2]) |
            (static_cast<std::uint32_t>(bytes[3]) << 8);
        return detail::scalar_from_pair(high, low);
    }
    return std::nullopt;
}

// Concatenate the UTF-16 BE encodings of a codepoint sequence.
inline std::vector<std::uint8_t> encode_be(
    std::span<const std::uint32_t> cps) {
    std::vector<std::uint8_t> out;
    out.reserve(cps.size() * 2);
    for (std::uint32_t cp : cps) {
        auto part = encode_one_be(cp);
        out.insert(out.end(), part.begin(), part.end());
    }
    return out;
}

// Concatenate the UTF-16 LE encodings of a codepoint sequence.
inline std::vector<std::uint8_t> encode_le(
    std::span<const std::uint32_t> cps) {
    std::vector<std::uint8_t> out;
    out.reserve(cps.size() * 2);
    for (std::uint32_t cp : cps) {
        auto part = encode_one_le(cp);
        out.insert(out.end(), part.begin(), part.end());
    }
    return out;
}

}  // namespace unicode_cpp::utf16

#endif  // UNICODE_CPP_UTF16_HPP
