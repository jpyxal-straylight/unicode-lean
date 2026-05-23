#include <doctest/doctest.h>

#include <cstdint>
#include <span>
#include <vector>

#include "unicode_cpp/opaque_blob.hpp"

using namespace unicode_cpp::opaque_blob;

static std::span<const std::uint8_t> as_span(
    const std::vector<std::uint8_t>& v) {
    return std::span<const std::uint8_t>(v.data(), v.size());
}

TEST_CASE("Utf8Blob — predicate accepts valid UTF-8") {
    auto a = std::vector<std::uint8_t>{0x48, 0x69};
    auto b = std::vector<std::uint8_t>{0xC3, 0xA9};
    auto c = std::vector<std::uint8_t>{0xF0, 0x9F, 0x98, 0x80};
    CHECK(is_utf8_blob(as_span(a)));
    CHECK(is_utf8_blob(as_span(b)));
    CHECK(is_utf8_blob(as_span(c)));
}

TEST_CASE("Utf8Blob — predicate rejects invalid UTF-8") {
    auto a = std::vector<std::uint8_t>{0xC0, 0x80};
    auto b = std::vector<std::uint8_t>{0xED, 0xA0, 0x80};
    CHECK_FALSE(is_utf8_blob(as_span(a)));
    CHECK_FALSE(is_utf8_blob(as_span(b)));
}

TEST_CASE("Utf8Blob — refinement builds within bound") {
    auto blob = Utf8Blob::of({0x48, 0x69}, 16);
    REQUIRE(blob.has_value());
    CHECK(blob->value().size() == 2);
    CHECK(blob->max_bytes() == 16);
}

TEST_CASE("Utf8Blob — refinement rejects over bound") {
    CHECK_FALSE(Utf8Blob::of({0x48, 0x69, 0x21}, 2).has_value());
}

TEST_CASE("Utf8Blob — refinement rejects malformed UTF-8") {
    CHECK_FALSE(Utf8Blob::of({0xC0, 0x80}, 16).has_value());
}

TEST_CASE("Utf8Blob — refinement accepts empty under any bound") {
    CHECK(Utf8Blob::of({}, 32).has_value());
}
