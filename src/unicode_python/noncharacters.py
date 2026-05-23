"""Detection and enumeration of the 66 designated Unicode
noncharacters per UAX #44 §5.6 / Unicode Standard 17.0 §23.7.

Two categories:

  * BMP block:  U+FDD0 .. U+FDEF                (32 codepoints)
  * Plane ends: U+nnFFFE / U+nnFFFF for n=0..16 (34 codepoints)

Total: 66.

Noncharacters are reserved for internal use; conformant Unicode
text MUST NOT contain them in interchange.  They are technically
valid scalar codepoints (in the range and not surrogates), so a
scalar-codepoint predicate accepts them; downstream consumers
that reject noncharacters layer this predicate on top.
"""

def is_noncharacter(cp: int) -> bool:
    """Whether ``cp`` is one of the 66 designated Unicode
    noncharacters."""
    if 0xFDD0 <= cp <= 0xFDEF:
        return True
    if cp > 0x10FFFF:
        return False
    low16 = cp & 0xFFFF
    return low16 == 0xFFFE or low16 == 0xFFFF


def all_noncharacters() -> list[int]:
    """Enumerate the 66 noncharacters in ascending order."""
    out = list(range(0xFDD0, 0xFDF0))
    for n in range(17):
        out.append(n * 0x10000 + 0xFFFE)
        out.append(n * 0x10000 + 0xFFFF)
    return out


__all__ = ["all_noncharacters", "is_noncharacter"]
