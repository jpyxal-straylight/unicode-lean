// Opaque text predicate — structurally valid UTF-8, size-bounded.
//
// No character-class or codepoint filtering beyond UTF-8
// validity.  Intended for callers who apply their own text
// hardening downstream; hardened identifier and printable
// profiles layer on top of this predicate.

#ifndef UNICODE_CPP_OPAQUE_BLOB_HPP
#define UNICODE_CPP_OPAQUE_BLOB_HPP

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <utility>
#include <vector>

#include "unicode_cpp/utf8.hpp"

namespace unicode_cpp::opaque_blob {

// Opaque-blob predicate: structurally valid UTF-8.  Exposed under
// this name so the "blob" framing — no character-class hardening —
// is explicit at the call site.
inline bool is_utf8_blob(std::span<const std::uint8_t> bytes) {
    return is_valid_utf8(bytes);
}

// A byte sequence carrying its size bound and UTF-8 validity
// claim.  Construct via the static `of` factory.
class Utf8Blob {
   public:
    static std::optional<Utf8Blob> of(
        std::vector<std::uint8_t> bytes, std::size_t max_bytes) {
        if (bytes.size() > max_bytes) return std::nullopt;
        if (!is_utf8_blob(bytes)) return std::nullopt;
        return Utf8Blob{std::move(bytes), max_bytes};
    }

    std::span<const std::uint8_t> value() const {
        return {value_.data(), value_.size()};
    }

    std::size_t max_bytes() const { return max_bytes_; }

   private:
    Utf8Blob(std::vector<std::uint8_t> bytes, std::size_t max_bytes)
        : value_(std::move(bytes)), max_bytes_(max_bytes) {}

    std::vector<std::uint8_t> value_;
    std::size_t max_bytes_;
};

}  // namespace unicode_cpp::opaque_blob

#endif  // UNICODE_CPP_OPAQUE_BLOB_HPP
