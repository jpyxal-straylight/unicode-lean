#include <doctest/doctest.h>

#include <cstdint>
#include <optional>
#include <span>
#include <vector>

#include "unicode_cpp/utf16.hpp"

using namespace unicode_cpp::utf16;

static std::span<const std::uint8_t> as_span(
    const std::vector<std::uint8_t>& v) {
    return std::span<const std::uint8_t>(v.data(), v.size());
}

TEST_CASE("UTF-16 — encodes ASCII BMP BE/LE") {
    CHECK(encode_one_be(0x0041)
          == std::vector<std::uint8_t>{0x00, 0x41});
    CHECK(encode_one_le(0x0041)
          == std::vector<std::uint8_t>{0x41, 0x00});
}

TEST_CASE("UTF-16 — encodes supplementary-plane BE/LE") {
    CHECK(encode_one_be(0x1F600)
          == std::vector<std::uint8_t>{0xD8, 0x3D, 0xDE, 0x00});
    CHECK(encode_one_le(0x1F600)
          == std::vector<std::uint8_t>{0x3D, 0xD8, 0x00, 0xDE});
}

TEST_CASE("UTF-16 — encodes U+10FFFF as the maximal surrogate pair") {
    CHECK(encode_one_be(0x10FFFF)
          == std::vector<std::uint8_t>{0xDB, 0xFF, 0xDF, 0xFF});
}

TEST_CASE("UTF-16 — decodes BMP BE/LE") {
    auto bytes_be = std::vector<std::uint8_t>{0x00, 0x41};
    auto bytes_le = std::vector<std::uint8_t>{0x41, 0x00};
    CHECK(decode_one_be(as_span(bytes_be)) == std::optional<std::uint32_t>{0x41});
    CHECK(decode_one_le(as_span(bytes_le)) == std::optional<std::uint32_t>{0x41});
}

TEST_CASE("UTF-16 — decodes supplementary pair") {
    auto bytes = std::vector<std::uint8_t>{0xD8, 0x3D, 0xDE, 0x00};
    CHECK(decode_one_be(as_span(bytes))
          == std::optional<std::uint32_t>{0x1F600});
}

TEST_CASE("UTF-16 — rejects lone high surrogate") {
    auto lone = std::vector<std::uint8_t>{0xD8, 0x00};
    CHECK_FALSE(decode_one_be(as_span(lone)).has_value());
}

TEST_CASE("UTF-16 — rejects high followed by non-low") {
    auto bad = std::vector<std::uint8_t>{0xD8, 0x00, 0x00, 0x42};
    CHECK_FALSE(decode_one_be(as_span(bad)).has_value());
}

TEST_CASE("UTF-16 — rejects invalid lengths") {
    for (std::size_t n : {0u, 1u, 3u, 5u, 6u}) {
        std::vector<std::uint8_t> bytes(n);
        CHECK_FALSE(decode_one_be(as_span(bytes)).has_value());
        CHECK_FALSE(decode_one_le(as_span(bytes)).has_value());
    }
}

TEST_CASE("UTF-16 — roundtrips every boundary") {
    for (std::uint32_t cp : {0x0000u, 0x007Fu, 0x0080u, 0xD7FFu,
                              0xE000u, 0xFFFDu, 0x10000u, 0x1F600u,
                              0x10FFFDu, 0x10FFFFu}) {
        auto be = encode_one_be(cp);
        auto le = encode_one_le(cp);
        CHECK(decode_one_be(as_span(be))
              == std::optional<std::uint32_t>{cp});
        CHECK(decode_one_le(as_span(le))
              == std::optional<std::uint32_t>{cp});
    }
}
