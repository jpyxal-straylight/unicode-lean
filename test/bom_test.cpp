#include <doctest/doctest.h>

#include <cstdint>
#include <span>
#include <vector>

#include "unicode_cpp/bom.hpp"

using namespace unicode_cpp::bom;

static std::span<const std::uint8_t> as_span(
    const std::vector<std::uint8_t>& v) {
    return std::span<const std::uint8_t>(v.data(), v.size());
}

TEST_CASE("BOM — empty input returns nullopt") {
    std::vector<std::uint8_t> empty;
    CHECK_FALSE(detect(as_span(empty)).has_value());
}

TEST_CASE("BOM — non-BOM bytes return nullopt") {
    auto bytes = std::vector<std::uint8_t>{0x41, 0x42, 0x43};
    CHECK_FALSE(detect(as_span(bytes)).has_value());
}

TEST_CASE("BOM — detects UTF-8") {
    auto bytes = std::vector<std::uint8_t>{0xEF, 0xBB, 0xBF};
    auto result = detect(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->kind == BomKind::Utf8);
    CHECK(result->skip == 3);
}

TEST_CASE("BOM — detects UTF-16 BE") {
    auto bytes = std::vector<std::uint8_t>{0xFE, 0xFF};
    auto result = detect(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->kind == BomKind::Utf16BE);
}

TEST_CASE("BOM — detects UTF-16 LE (2-byte)") {
    auto bytes = std::vector<std::uint8_t>{0xFF, 0xFE};
    auto result = detect(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->kind == BomKind::Utf16LE);
}

TEST_CASE("BOM — detects UTF-32 BE") {
    auto bytes = std::vector<std::uint8_t>{0x00, 0x00, 0xFE, 0xFF};
    auto result = detect(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->kind == BomKind::Utf32BE);
}

TEST_CASE("BOM — UTF-32 LE wins over UTF-16 LE on FF FE 00 00") {
    auto bytes = std::vector<std::uint8_t>{0xFF, 0xFE, 0x00, 0x00};
    auto result = detect(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->kind == BomKind::Utf32LE);
    CHECK(result->skip == 4);
}

TEST_CASE("BOM — UTF-16 LE matched when followed by non-zero") {
    auto bytes = std::vector<std::uint8_t>{0xFF, 0xFE, 0x41};
    auto result = detect(as_span(bytes));
    REQUIRE(result.has_value());
    CHECK(result->kind == BomKind::Utf16LE);
}

TEST_CASE("BOM — length() for each kind") {
    CHECK(length(BomKind::Utf8) == 3);
    CHECK(length(BomKind::Utf16BE) == 2);
    CHECK(length(BomKind::Utf16LE) == 2);
    CHECK(length(BomKind::Utf32BE) == 4);
    CHECK(length(BomKind::Utf32LE) == 4);
}

TEST_CASE("BOM — strip returns kind and rest") {
    auto bytes = std::vector<std::uint8_t>{0xEF, 0xBB, 0xBF, 0x48, 0x69};
    auto result = strip(as_span(bytes));
    REQUIRE(result.kind.has_value());
    CHECK(*result.kind == BomKind::Utf8);
    CHECK(result.rest.size() == 2);
}

TEST_CASE("BOM — strip passes through when no BOM") {
    auto bytes = std::vector<std::uint8_t>{0x41, 0x42};
    auto result = strip(as_span(bytes));
    CHECK_FALSE(result.kind.has_value());
    CHECK(result.rest.size() == 2);
}
