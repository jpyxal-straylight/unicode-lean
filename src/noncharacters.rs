//! Detection and enumeration of the 66 designated Unicode
//! noncharacters per UAX #44 §5.6 / Unicode Standard 17.0 §23.7.
//!
//! Two categories:
//!
//!   - BMP block:  U+FDD0 .. U+FDEF                (32 codepoints)
//!   - Plane ends: U+nnFFFE / U+nnFFFF for n=0..16 (34 codepoints)
//!
//! Total: 66.
//!
//! Noncharacters are reserved for internal use; conformant Unicode
//! text MUST NOT contain them in interchange.  They are
//! technically valid scalar codepoints (in the range and not
//! surrogates), so a scalar-codepoint predicate accepts them;
//! downstream consumers that reject noncharacters layer this
//! predicate on top.

/// Whether `cp` is one of the 66 designated Unicode noncharacters.
pub fn is_noncharacter(cp: u32) -> bool {
    if (0xFDD0..=0xFDEF).contains(&cp) {
        return true;
    }
    if cp > 0x10FFFF {
        return false;
    }
    let low16 = cp & 0xFFFF;
    low16 == 0xFFFE || low16 == 0xFFFF
}

/// Enumerate the 66 noncharacters in ascending order.
pub fn all_noncharacters() -> Vec<u32> {
    let mut out = Vec::with_capacity(66);
    for cp in 0xFDD0u32..=0xFDEFu32 {
        out.push(cp);
    }
    for n in 0u32..=16u32 {
        out.push(n * 0x10000 + 0xFFFE);
        out.push(n * 0x10000 + 0xFFFF);
    }
    out
}
