// Byte-Order-Mark detection across the five Unicode encodings.
//
//   UTF-8     : EF BB BF              (3 bytes)
//   UTF-16 BE : FE FF                 (2 bytes)
//   UTF-16 LE : FF FE                 (2 bytes)
//   UTF-32 BE : 00 00 FE FF           (4 bytes)
//   UTF-32 LE : FF FE 00 00           (4 bytes)
//
// Order matters: the UTF-32 BOMs share their leading bytes with
// the UTF-16 BOMs, so the 4-byte patterns must be checked BEFORE
// the 2-byte patterns.

#ifndef UNICODE_CPP_BOM_HPP
#define UNICODE_CPP_BOM_HPP

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>

namespace unicode_cpp::bom {

enum class BomKind : std::uint8_t {
    Utf8,
    Utf16BE,
    Utf16LE,
    Utf32BE,
    Utf32LE,
};

// The byte length of each BOM.
inline std::size_t length(BomKind kind) {
    switch (kind) {
        case BomKind::Utf8:    return 3;
        case BomKind::Utf16BE:
        case BomKind::Utf16LE: return 2;
        case BomKind::Utf32BE:
        case BomKind::Utf32LE: return 4;
    }
    return 0;
}

struct Detection {
    BomKind kind;
    std::size_t skip;
};

namespace detail {
inline std::uint8_t byte_at(
    std::span<const std::uint8_t> bytes, std::size_t i) {
    return i < bytes.size() ? bytes[i] : std::uint8_t{0};
}
}  // namespace detail

// Detect a leading BOM, returning the encoding kind and the
// number of BOM bytes to skip.  The 4-byte UTF-32 BOMs are tested
// before the 2-byte UTF-16 BOMs.  Returns std::nullopt when the
// input does not begin with any recognised BOM.
inline std::optional<Detection> detect(
    std::span<const std::uint8_t> bytes) {
    const auto b0 = detail::byte_at(bytes, 0);
    const auto b1 = detail::byte_at(bytes, 1);
    const auto b2 = detail::byte_at(bytes, 2);
    const auto b3 = detail::byte_at(bytes, 3);
    if (bytes.size() >= 4 && b0 == 0x00 && b1 == 0x00 && b2 == 0xFE && b3 == 0xFF)
        return Detection{BomKind::Utf32BE, 4};
    if (bytes.size() >= 4 && b0 == 0xFF && b1 == 0xFE && b2 == 0x00 && b3 == 0x00)
        return Detection{BomKind::Utf32LE, 4};
    if (bytes.size() >= 3 && b0 == 0xEF && b1 == 0xBB && b2 == 0xBF)
        return Detection{BomKind::Utf8, 3};
    if (bytes.size() >= 2 && b0 == 0xFE && b1 == 0xFF)
        return Detection{BomKind::Utf16BE, 2};
    if (bytes.size() >= 2 && b0 == 0xFF && b1 == 0xFE)
        return Detection{BomKind::Utf16LE, 2};
    return std::nullopt;
}

struct StripResult {
    std::optional<BomKind> kind;
    std::span<const std::uint8_t> rest;
};

// Strip the BOM from `bytes` if one is present, returning the
// remaining content together with the detected encoding.
inline StripResult strip(std::span<const std::uint8_t> bytes) {
    if (auto det = detect(bytes)) {
        return StripResult{det->kind, bytes.subspan(det->skip)};
    }
    return StripResult{std::nullopt, bytes};
}

}  // namespace unicode_cpp::bom

#endif  // UNICODE_CPP_BOM_HPP
