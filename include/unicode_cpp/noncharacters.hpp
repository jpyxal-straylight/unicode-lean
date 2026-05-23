// Detection and enumeration of the 66 designated Unicode
// noncharacters per UAX #44 §5.6 / Unicode Standard 17.0 §23.7.
//
//   - BMP block:  U+FDD0 .. U+FDEF                (32 codepoints)
//   - Plane ends: U+nnFFFE / U+nnFFFF for n=0..16 (34 codepoints)
//
// Total: 66.
//
// Noncharacters are reserved for internal use; conformant Unicode
// text MUST NOT contain them in interchange.  They are
// technically valid scalar codepoints (in the range and not
// surrogates), so a scalar-codepoint predicate accepts them;
// downstream consumers that reject noncharacters layer this
// predicate on top.

#ifndef UNICODE_CPP_NONCHARACTERS_HPP
#define UNICODE_CPP_NONCHARACTERS_HPP

#include <cstdint>
#include <vector>

namespace unicode_cpp::noncharacters {

// Whether cp is one of the 66 designated Unicode noncharacters.
inline bool is_noncharacter(std::uint32_t cp) {
    if (cp >= 0xFDD0u && cp <= 0xFDEFu) return true;
    if (cp > 0x10FFFFu) return false;
    const std::uint32_t low16 = cp & 0xFFFFu;
    return low16 == 0xFFFEu || low16 == 0xFFFFu;
}

// Enumerate the 66 noncharacters in ascending order.
inline std::vector<std::uint32_t> all_noncharacters() {
    std::vector<std::uint32_t> out;
    out.reserve(66);
    for (std::uint32_t cp = 0xFDD0u; cp <= 0xFDEFu; ++cp) {
        out.push_back(cp);
    }
    for (std::uint32_t n = 0; n <= 16; ++n) {
        out.push_back(n * 0x10000u + 0xFFFEu);
        out.push_back(n * 0x10000u + 0xFFFFu);
    }
    return out;
}

}  // namespace unicode_cpp::noncharacters

#endif  // UNICODE_CPP_NONCHARACTERS_HPP
