#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include <doctest/doctest.h>

#include <cstdint>
#include <span>
#include <vector>

#include "unicode_cpp/utf8.hpp"

using namespace unicode_cpp;

static std::span<const std::uint8_t> as_span(
    const std::vector<std::uint8_t>& v) {
    return std::span<const std::uint8_t>(v.data(), v.size());
}

// ─────────────────────────────────────────────────────────────────────
// Acceptance
// ─────────────────────────────────────────────────────────────────────

TEST_CASE("strict UTF-8 codec — empty input is valid") {
    std::vector<std::uint8_t> empty;
    CHECK(is_valid_utf8(as_span(empty)));
    CHECK_FALSE(first_invalid_utf8_offset(as_span(empty)).has_value());
}

TEST_CASE("strict UTF-8 codec — pure ASCII is valid") {
    std::vector<std::uint8_t> bytes = {0x48, 0x65, 0x6c, 0x6c, 0x6f};
    CHECK(is_valid_utf8(as_span(bytes)));
    auto cps = decode_to_codepoints(as_span(bytes));
    CHECK(cps == std::vector<std::uint32_t>{0x48, 0x65, 0x6c, 0x6c, 0x6f});
}

TEST_CASE("strict UTF-8 codec — 2-byte sequence U+00E9") {
    std::vector<std::uint8_t> bytes = {0xc3, 0xa9};
    CHECK(is_valid_utf8(as_span(bytes)));
    CHECK(decode_to_codepoints(as_span(bytes))
          == std::vector<std::uint32_t>{0xe9});
}

TEST_CASE("strict UTF-8 codec — 3-byte sequence U+4E2D") {
    std::vector<std::uint8_t> bytes = {0xe4, 0xb8, 0xad};
    CHECK(is_valid_utf8(as_span(bytes)));
    CHECK(decode_to_codepoints(as_span(bytes))
          == std::vector<std::uint32_t>{0x4e2d});
}

TEST_CASE("strict UTF-8 codec — 4-byte sequence U+1F600") {
    std::vector<std::uint8_t> bytes = {0xf0, 0x9f, 0x98, 0x80};
    CHECK(is_valid_utf8(as_span(bytes)));
    CHECK(decode_to_codepoints(as_span(bytes))
          == std::vector<std::uint32_t>{0x1f600});
}

// ─────────────────────────────────────────────────────────────────────
// Rejection — every Utf8RejectKind
// ─────────────────────────────────────────────────────────────────────

TEST_CASE("strict UTF-8 codec — 0xC0 start byte is invalid") {
    std::vector<std::uint8_t> bytes = {0xc0, 0xaf};
    auto result = first_invalid_utf8_offset(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->offset == 0);
    CHECK(result->kind == Utf8RejectKind::InvalidStartByte);
}

TEST_CASE("strict UTF-8 codec — overlong 3-byte encoding") {
    std::vector<std::uint8_t> bytes = {0xe0, 0x80, 0xaf};
    auto result = first_invalid_utf8_offset(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->offset == 0);
    CHECK(result->kind == Utf8RejectKind::OverlongEncoding);
}

TEST_CASE("strict UTF-8 codec — high surrogate U+D800") {
    std::vector<std::uint8_t> bytes = {0xed, 0xa0, 0x80};
    auto result = first_invalid_utf8_offset(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->kind == Utf8RejectKind::SurrogateCodepoint);
}

TEST_CASE("strict UTF-8 codec — codepoint beyond U+10FFFF") {
    std::vector<std::uint8_t> bytes = {0xf4, 0x90, 0x80, 0x80};
    auto result = first_invalid_utf8_offset(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->kind == Utf8RejectKind::CodepointBeyondMax);
}

TEST_CASE("strict UTF-8 codec — truncated 2-byte sequence") {
    std::vector<std::uint8_t> bytes = {0xc2};
    auto result = first_invalid_utf8_offset(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->offset == 1);
    CHECK(result->kind == Utf8RejectKind::TruncatedSequence);
}

TEST_CASE("strict UTF-8 codec — invalid start byte 0x80") {
    std::vector<std::uint8_t> bytes = {0x80};
    auto result = first_invalid_utf8_offset(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->offset == 0);
    CHECK(result->kind == Utf8RejectKind::InvalidStartByte);
}

TEST_CASE("strict UTF-8 codec — invalid continuation byte after 0xC2") {
    std::vector<std::uint8_t> bytes = {0xc2, 0x00};
    auto result = first_invalid_utf8_offset(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->offset == 1);
    CHECK(result->kind == Utf8RejectKind::InvalidContinuationByte);
}

TEST_CASE("strict UTF-8 codec — 0xF5 start byte is invalid") {
    std::vector<std::uint8_t> bytes = {0xf5, 0x80, 0x80, 0x80};
    auto result = first_invalid_utf8_offset(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->kind == Utf8RejectKind::InvalidStartByte);
}

// ─────────────────────────────────────────────────────────────────────
// Encoder
// ─────────────────────────────────────────────────────────────────────

TEST_CASE("encoder — 1-byte codepoints") {
    CHECK(encode_codepoint(0x00) == std::vector<std::uint8_t>{0x00});
    CHECK(encode_codepoint(0x41) == std::vector<std::uint8_t>{0x41});
    CHECK(encode_codepoint(0x7f) == std::vector<std::uint8_t>{0x7f});
}

TEST_CASE("encoder — 2-byte codepoints") {
    CHECK(encode_codepoint(0x80)
          == std::vector<std::uint8_t>{0xc2, 0x80});
    CHECK(encode_codepoint(0xe9)
          == std::vector<std::uint8_t>{0xc3, 0xa9});
    CHECK(encode_codepoint(0x7ff)
          == std::vector<std::uint8_t>{0xdf, 0xbf});
}

TEST_CASE("encoder — 3-byte codepoints") {
    CHECK(encode_codepoint(0x800)
          == std::vector<std::uint8_t>{0xe0, 0xa0, 0x80});
    CHECK(encode_codepoint(0x4e2d)
          == std::vector<std::uint8_t>{0xe4, 0xb8, 0xad});
    CHECK(encode_codepoint(0xffff)
          == std::vector<std::uint8_t>{0xef, 0xbf, 0xbf});
}

TEST_CASE("encoder — 4-byte codepoints") {
    CHECK(encode_codepoint(0x10000)
          == std::vector<std::uint8_t>{0xf0, 0x90, 0x80, 0x80});
    CHECK(encode_codepoint(0x1f600)
          == std::vector<std::uint8_t>{0xf0, 0x9f, 0x98, 0x80});
    CHECK(encode_codepoint(0x10ffff)
          == std::vector<std::uint8_t>{0xf4, 0x8f, 0xbf, 0xbf});
}

// ─────────────────────────────────────────────────────────────────────
// Roundtrips
// ─────────────────────────────────────────────────────────────────────

TEST_CASE("roundtrip — mixed codepoint sequence") {
    std::vector<std::uint32_t> cps = {
        0x48, 0x69, 0xe9, 0x4e2d, 0x6587, 0x1f600,
    };
    auto encoded = encode_codepoints(
        std::span<const std::uint32_t>(cps.data(), cps.size()));
    CHECK(is_valid_utf8(as_span(encoded)));
    CHECK(decode_to_codepoints(as_span(encoded)) == cps);
}

TEST_CASE("roundtrip — every byte-class boundary") {
    const std::uint32_t boundaries[] = {
        0x00,       0x7f,        // 1-byte
        0x80,       0x7ff,       // 2-byte
        0x800,      0xd7ff,      // 3-byte just below surrogates
        0xe000,     0xffff,      // 3-byte just above surrogates
        0x10000,    0x10ffff,    // 4-byte
    };
    for (std::uint32_t cp : boundaries) {
        auto encoded = encode_codepoint(cp);
        INFO("codepoint U+", cp);
        CHECK(is_valid_utf8(as_span(encoded)));
        CHECK(decode_to_codepoints(as_span(encoded))
              == std::vector<std::uint32_t>{cp});
    }
}
