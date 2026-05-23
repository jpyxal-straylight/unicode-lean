#include <doctest/doctest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "unicode_cpp/validated_utf8.hpp"

using namespace unicode_cpp::validated_utf8;

TEST_CASE("ValidatedUtf8 — validates valid input") {
    CHECK(ValidatedUtf8::validate({0x48, 0x69}).has_value());
}

TEST_CASE("ValidatedUtf8 — rejects overlong NUL") {
    CHECK_FALSE(ValidatedUtf8::validate({0xC0, 0x80}).has_value());
}

TEST_CASE("ValidatedUtf8 — rejects surrogate") {
    CHECK_FALSE(ValidatedUtf8::validate({0xED, 0xA0, 0x80}).has_value());
}

TEST_CASE("ValidatedUtf8 — rejects beyond U+10FFFF") {
    CHECK_FALSE(
        ValidatedUtf8::validate({0xF4, 0x90, 0x80, 0x80}).has_value());
}

TEST_CASE("ValidatedUtf8 — rejects truncated") {
    CHECK_FALSE(ValidatedUtf8::validate({0xC2}).has_value());
}

TEST_CASE("ValidatedUtf8 — as_bytes borrows the validated bytes") {
    auto v = ValidatedUtf8::validate({0x48, 0x69});
    REQUIRE(v.has_value());
    CHECK(v->as_bytes().size() == 2);
}

TEST_CASE("ValidatedUtf8 — into_bytes consumes the claim") {
    auto v = ValidatedUtf8::validate({0x48, 0x69});
    REQUIRE(v.has_value());
    auto bytes = std::move(*v).into_bytes();
    CHECK(bytes == std::vector<std::uint8_t>{0x48, 0x69});
}

TEST_CASE("ValidatedUtf8 — validates empty input") {
    auto v = ValidatedUtf8::validate({});
    REQUIRE(v.has_value());
    CHECK(v->as_bytes().empty());
}
