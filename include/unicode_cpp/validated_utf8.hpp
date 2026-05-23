// Refinement type for bytes validated as strict RFC 3629 UTF-8.
//
// The validity claim is pinned at the module-boundary level: the
// only way to construct a ValidatedUtf8 is via the smart
// constructor `ValidatedUtf8::validate`, which routes through
// the strict decoder state machine.
//
// Rationale: the ingestion layer is security-critical.  A plain
// std::vector<std::uint8_t> carries no claim about its UTF-8
// validity — downstream consumers have to either re-validate or
// trust the producer.  ValidatedUtf8 makes the claim
// module-level, so a downstream consumer that wants the raw
// bytes has to explicitly `into_bytes()` — which reads as
// "I am consuming the RFC 3629 claim here".

#ifndef UNICODE_CPP_VALIDATED_UTF8_HPP
#define UNICODE_CPP_VALIDATED_UTF8_HPP

#include <cstdint>
#include <optional>
#include <span>
#include <utility>
#include <vector>

#include "unicode_cpp/utf8.hpp"

namespace unicode_cpp::validated_utf8 {

class ValidatedUtf8 {
   public:
    // Validate `bytes` and, on success, return a ValidatedUtf8
    // carrying the RFC 3629 validity claim.  Returns
    // std::nullopt when the bytes fail the strict state machine.
    static std::optional<ValidatedUtf8> validate(
        std::vector<std::uint8_t> bytes) {
        if (!is_valid_utf8(bytes)) return std::nullopt;
        return ValidatedUtf8{std::move(bytes)};
    }

    std::span<const std::uint8_t> as_bytes() const {
        return {bytes_.data(), bytes_.size()};
    }

    // Consume the validity claim, returning the underlying bytes.
    std::vector<std::uint8_t> into_bytes() && {
        return std::move(bytes_);
    }

   private:
    explicit ValidatedUtf8(std::vector<std::uint8_t> bytes)
        : bytes_(std::move(bytes)) {}

    std::vector<std::uint8_t> bytes_;
};

}  // namespace unicode_cpp::validated_utf8

#endif  // UNICODE_CPP_VALIDATED_UTF8_HPP
