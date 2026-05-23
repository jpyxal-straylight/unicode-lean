// UTF-32 codec — big-endian and little-endian variants.
//
// Each scalar Unicode codepoint encodes to exactly 4 bytes; the
// invariant is straight identity, no length-dependent escape
// sequences.  The decoder rejects inputs whose length is not
// exactly 4, 4-byte sequences encoding a surrogate codepoint
// U+D800..U+DFFF, and 4-byte sequences encoding a value above
// U+10FFFF.

#ifndef UNICODE_CPP_UTF32_HPP
#define UNICODE_CPP_UTF32_HPP

#include <cstdint>
#include <optional>
#include <span>
#include <vector>

namespace unicode_cpp::utf32 {

// Encode a scalar codepoint as 4 bytes in big-endian order.
inline std::vector<std::uint8_t> encode_one_be(std::uint32_t cp) {
    return {
        static_cast<std::uint8_t>((cp >> 24) & 0xFFu),
        static_cast<std::uint8_t>((cp >> 16) & 0xFFu),
        static_cast<std::uint8_t>((cp >> 8) & 0xFFu),
        static_cast<std::uint8_t>(cp & 0xFFu),
    };
}

// Encode a scalar codepoint as 4 bytes in little-endian order.
inline std::vector<std::uint8_t> encode_one_le(std::uint32_t cp) {
    return {
        static_cast<std::uint8_t>(cp & 0xFFu),
        static_cast<std::uint8_t>((cp >> 8) & 0xFFu),
        static_cast<std::uint8_t>((cp >> 16) & 0xFFu),
        static_cast<std::uint8_t>((cp >> 24) & 0xFFu),
    };
}

namespace detail {
inline std::optional<std::uint32_t> scalar(std::uint32_t cp) {
    if (cp > 0x10FFFFu) return std::nullopt;
    if (cp >= 0xD800u && cp <= 0xDFFFu) return std::nullopt;
    return cp;
}
}  // namespace detail

// Decode 4 bytes as a big-endian UTF-32 codepoint.  Returns
// std::nullopt when the length is not exactly 4, the decoded
// value is a surrogate, or the value exceeds U+10FFFF.
inline std::optional<std::uint32_t> decode_one_be(
    std::span<const std::uint8_t> bytes) {
    if (bytes.size() != 4) return std::nullopt;
    std::uint32_t cp =
        (static_cast<std::uint32_t>(bytes[0]) << 24) |
        (static_cast<std::uint32_t>(bytes[1]) << 16) |
        (static_cast<std::uint32_t>(bytes[2]) << 8) |
        static_cast<std::uint32_t>(bytes[3]);
    return detail::scalar(cp);
}

// Decode 4 bytes as a little-endian UTF-32 codepoint.
inline std::optional<std::uint32_t> decode_one_le(
    std::span<const std::uint8_t> bytes) {
    if (bytes.size() != 4) return std::nullopt;
    std::uint32_t cp =
        static_cast<std::uint32_t>(bytes[0]) |
        (static_cast<std::uint32_t>(bytes[1]) << 8) |
        (static_cast<std::uint32_t>(bytes[2]) << 16) |
        (static_cast<std::uint32_t>(bytes[3]) << 24);
    return detail::scalar(cp);
}

// Concatenate the UTF-32 BE encodings of a codepoint sequence.
inline std::vector<std::uint8_t> encode_be(
    std::span<const std::uint32_t> cps) {
    std::vector<std::uint8_t> out;
    out.reserve(cps.size() * 4);
    for (std::uint32_t cp : cps) {
        auto part = encode_one_be(cp);
        out.insert(out.end(), part.begin(), part.end());
    }
    return out;
}

// Concatenate the UTF-32 LE encodings of a codepoint sequence.
inline std::vector<std::uint8_t> encode_le(
    std::span<const std::uint32_t> cps) {
    std::vector<std::uint8_t> out;
    out.reserve(cps.size() * 4);
    for (std::uint32_t cp : cps) {
        auto part = encode_one_le(cp);
        out.insert(out.end(), part.begin(), part.end());
    }
    return out;
}

}  // namespace unicode_cpp::utf32

#endif  // UNICODE_CPP_UTF32_HPP
