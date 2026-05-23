#include <doctest/doctest.h>

#include <cstdint>
#include <optional>
#include <span>
#include <vector>

#include "unicode_cpp/utf32.hpp"

using namespace unicode_cpp::utf32;

static std::span<const std::uint8_t> as_span(
    const std::vector<std::uint8_t>& v) {
    return std::span<const std::uint8_t>(v.data(), v.size());
}

TEST_CASE("UTF-32 — encodes ASCII BE/LE") {
    CHECK(encode_one_be(0x41)
          == std::vector<std::uint8_t>{0x00, 0x00, 0x00, 0x41});
    CHECK(encode_one_le(0x41)
          == std::vector<std::uint8_t>{0x41, 0x00, 0x00, 0x00});
}

TEST_CASE("UTF-32 — encodes supplementary BE/LE") {
    CHECK(encode_one_be(0x1F600)
          == std::vector<std::uint8_t>{0x00, 0x01, 0xF6, 0x00});
    CHECK(encode_one_le(0x1F600)
          == std::vector<std::uint8_t>{0x00, 0xF6, 0x01, 0x00});
}

TEST_CASE("UTF-32 — encodes U+10FFFF") {
    CHECK(encode_one_be(0x10FFFF)
          == std::vector<std::uint8_t>{0x00, 0x10, 0xFF, 0xFF});
    CHECK(encode_one_le(0x10FFFF)
          == std::vector<std::uint8_t>{0xFF, 0xFF, 0x10, 0x00});
}

TEST_CASE("UTF-32 — decodes valid scalars BE/LE") {
    auto be = std::vector<std::uint8_t>{0x00, 0x00, 0x00, 0x41};
    auto le = std::vector<std::uint8_t>{0x41, 0x00, 0x00, 0x00};
    CHECK(decode_one_be(as_span(be))
          == std::optional<std::uint32_t>{0x41});
    CHECK(decode_one_le(as_span(le))
          == std::optional<std::uint32_t>{0x41});
}

TEST_CASE("UTF-32 — rejects surrogates") {
    auto bytes = std::vector<std::uint8_t>{0x00, 0x00, 0xD8, 0x00};
    CHECK_FALSE(decode_one_be(as_span(bytes)).has_value());
}

TEST_CASE("UTF-32 — rejects beyond U+10FFFF") {
    auto bytes = std::vector<std::uint8_t>{0x00, 0x11, 0x00, 0x00};
    CHECK_FALSE(decode_one_be(as_span(bytes)).has_value());
}

TEST_CASE("UTF-32 — rejects invalid lengths") {
    for (std::size_t n : {0u, 1u, 2u, 3u, 5u, 8u}) {
        std::vector<std::uint8_t> bytes(n);
        CHECK_FALSE(decode_one_be(as_span(bytes)).has_value());
    }
}

TEST_CASE("UTF-32 — roundtrips every boundary") {
    for (std::uint32_t cp : {0x00u, 0x7Fu, 0x80u, 0xD7FFu, 0xE000u,
                              0xFFFFu, 0x10000u, 0x10FFFFu}) {
        auto be = encode_one_be(cp);
        auto le = encode_one_le(cp);
        CHECK(decode_one_be(as_span(be))
              == std::optional<std::uint32_t>{cp});
        CHECK(decode_one_le(as_span(le))
              == std::optional<std::uint32_t>{cp});
    }
}
