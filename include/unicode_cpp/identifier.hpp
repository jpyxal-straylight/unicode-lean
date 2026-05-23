// Strict ASCII identifier predicate — [a-zA-Z_][a-zA-Z0-9_]*.
//
//   - The first byte MUST be in 0x41..0x5A (A–Z),
//     0x61..0x7A (a–z), or 0x5F (_).
//   - Subsequent bytes MUST be in the first-byte set OR
//     0x30..0x39 (0–9).
//   - Empty byte sequences are REJECTED.
//
// The codec stays strict ASCII permanently.  Callers needing
// Unicode identifiers route through a PRECIS identifier codec
// (RFC 8264 / 8265) layered on top, providing defense-in-depth:
// an ASCII belt plus PRECIS suspenders.

#ifndef UNICODE_CPP_IDENTIFIER_HPP
#define UNICODE_CPP_IDENTIFIER_HPP

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

namespace unicode_cpp::identifier {

// Whether b may start an ASCII identifier: A–Z, a–z, or `_`.
inline bool is_start_byte(std::uint8_t b) {
    return (b >= 0x41 && b <= 0x5A) ||
           (b >= 0x61 && b <= 0x7A) || b == 0x5F;
}

// Whether b may continue an ASCII identifier: the start-byte set
// plus 0–9.
inline bool is_continue_byte(std::uint8_t b) {
    return is_start_byte(b) || (b >= 0x30 && b <= 0x39);
}

struct InvalidContinue {
    std::size_t offset;
    std::uint8_t byte;
};

// Walk the continuation positions of `bytes` starting at `from`,
// returning the offset and value of the first byte that fails
// is_continue_byte.  Returns std::nullopt when every position
// from `from` onward is a valid continuation byte.
inline std::optional<InvalidContinue> first_invalid_continue_from(
    std::span<const std::uint8_t> bytes, std::size_t from) {
    for (std::size_t i = from; i < bytes.size(); ++i) {
        if (!is_continue_byte(bytes[i])) {
            return InvalidContinue{i, bytes[i]};
        }
    }
    return std::nullopt;
}

// ASCII-identifier predicate: non-empty, valid start byte at
// position zero, and every subsequent byte a valid continuation
// byte.
inline bool is_valid_identifier_bytes(
    std::span<const std::uint8_t> bytes) {
    if (bytes.empty()) return false;
    if (!is_start_byte(bytes[0])) return false;
    return !first_invalid_continue_from(bytes, 1).has_value();
}

// A byte sequence carrying its size bound and identifier-validity
// claim.  Construct via the static `of` factory.
class IdentifierUtf8 {
   public:
    static std::optional<IdentifierUtf8> of(
        std::vector<std::uint8_t> bytes, std::size_t max_bytes) {
        if (bytes.size() > max_bytes) return std::nullopt;
        if (!is_valid_identifier_bytes(bytes)) return std::nullopt;
        return IdentifierUtf8{std::move(bytes), max_bytes};
    }

    std::span<const std::uint8_t> value() const {
        return {value_.data(), value_.size()};
    }

    std::size_t max_bytes() const { return max_bytes_; }

   private:
    IdentifierUtf8(std::vector<std::uint8_t> bytes, std::size_t max_bytes)
        : value_(std::move(bytes)), max_bytes_(max_bytes) {}

    std::vector<std::uint8_t> value_;
    std::size_t max_bytes_;
};

}  // namespace unicode_cpp::identifier

#endif  // UNICODE_CPP_IDENTIFIER_HPP
