#include <doctest/doctest.h>

#include <cstdint>

#include "unicode_cpp/noncharacters.hpp"

using namespace unicode_cpp::noncharacters;

TEST_CASE("Noncharacters — flags BMP block U+FDD0..U+FDEF") {
    for (std::uint32_t cp = 0xFDD0u; cp <= 0xFDEFu; ++cp) {
        CHECK(is_noncharacter(cp));
    }
}

TEST_CASE("Noncharacters — flags every plane end") {
    for (std::uint32_t n = 0; n <= 16; ++n) {
        CHECK(is_noncharacter(n * 0x10000u + 0xFFFEu));
        CHECK(is_noncharacter(n * 0x10000u + 0xFFFFu));
    }
}

TEST_CASE("Noncharacters — rejects ASCII") {
    for (std::uint32_t cp : {0x00u, 0x41u, 0x7Fu}) {
        CHECK_FALSE(is_noncharacter(cp));
    }
}

TEST_CASE("Noncharacters — rejects adjacent to FDDx block") {
    CHECK_FALSE(is_noncharacter(0xFDCFu));
    CHECK_FALSE(is_noncharacter(0xFDF0u));
}

TEST_CASE("Noncharacters — rejects U+FFFD replacement character") {
    CHECK_FALSE(is_noncharacter(0xFFFDu));
}

TEST_CASE("Noncharacters — rejects above U+10FFFF") {
    CHECK_FALSE(is_noncharacter(0x110000u));
}

TEST_CASE("Noncharacters — enumerates exactly 66") {
    CHECK(all_noncharacters().size() == 66);
}

TEST_CASE("Noncharacters — enumeration is ascending") {
    auto all = all_noncharacters();
    for (std::size_t i = 1; i < all.size(); ++i) {
        CHECK(all[i] > all[i - 1]);
    }
}

TEST_CASE("Noncharacters — every enumerated satisfies predicate") {
    for (std::uint32_t cp : all_noncharacters()) {
        CHECK(is_noncharacter(cp));
    }
}
