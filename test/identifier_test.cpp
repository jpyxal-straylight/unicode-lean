#include <doctest/doctest.h>

#include <cstdint>
#include <span>
#include <string>
#include <vector>

#include "unicode_cpp/identifier.hpp"

using namespace unicode_cpp::identifier;

static std::vector<std::uint8_t> ascii(const std::string& s) {
    return std::vector<std::uint8_t>(s.begin(), s.end());
}

static std::span<const std::uint8_t> as_span(
    const std::vector<std::uint8_t>& v) {
    return std::span<const std::uint8_t>(v.data(), v.size());
}

TEST_CASE("Identifier — start-byte predicate accepts A-Z, a-z, _") {
    for (char c : std::string("AZazMno_")) {
        CHECK(is_start_byte(static_cast<std::uint8_t>(c)));
    }
}

TEST_CASE("Identifier — start-byte predicate rejects digits/punct") {
    for (char c : std::string("0123-.@$")) {
        CHECK_FALSE(is_start_byte(static_cast<std::uint8_t>(c)));
    }
}

TEST_CASE("Identifier — continue-byte predicate accepts start-set + digits") {
    for (char c : std::string("Az_09")) {
        CHECK(is_continue_byte(static_cast<std::uint8_t>(c)));
    }
}

TEST_CASE("Identifier — rejects empty input") {
    std::vector<std::uint8_t> empty;
    CHECK_FALSE(is_valid_identifier_bytes(as_span(empty)));
}

TEST_CASE("Identifier — accepts a single underscore") {
    auto bytes = ascii("_");
    CHECK(is_valid_identifier_bytes(as_span(bytes)));
}

TEST_CASE("Identifier — accepts typical identifiers") {
    for (const auto& s : {"x", "foo", "foo_bar", "X123", "_x9"}) {
        auto bytes = ascii(s);
        CHECK(is_valid_identifier_bytes(as_span(bytes)));
    }
}

TEST_CASE("Identifier — rejects starting with digit") {
    auto bytes = ascii("1abc");
    CHECK_FALSE(is_valid_identifier_bytes(as_span(bytes)));
}

TEST_CASE("Identifier — rejects punctuation inside") {
    for (const auto& s : {"foo-bar", "a.b", "a@b", "a b"}) {
        auto bytes = ascii(s);
        CHECK_FALSE(is_valid_identifier_bytes(as_span(bytes)));
    }
}

TEST_CASE("Identifier — walker returns nullopt on all-valid input") {
    auto bytes = ascii("abc123");
    CHECK_FALSE(first_invalid_continue_from(as_span(bytes), 1).has_value());
}

TEST_CASE("Identifier — walker returns first invalid offset") {
    auto bytes = ascii("foo-bar");
    auto result = first_invalid_continue_from(as_span(bytes), 1);
    REQUIRE(result.has_value());
    CHECK(result->offset == 3);
    CHECK(result->byte == 0x2D);
}

TEST_CASE("Identifier — refinement builds when valid and within bound") {
    auto id = IdentifierUtf8::of(ascii("foo"), 16);
    REQUIRE(id.has_value());
    CHECK(id->value().size() == 3);
    CHECK(id->max_bytes() == 16);
}

TEST_CASE("Identifier — refinement rejects over bound") {
    CHECK_FALSE(IdentifierUtf8::of(ascii("foo_bar"), 4).has_value());
}

TEST_CASE("Identifier — refinement rejects invalid") {
    CHECK_FALSE(IdentifierUtf8::of(ascii("1abc"), 16).has_value());
}
