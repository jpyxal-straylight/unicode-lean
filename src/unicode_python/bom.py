"""Byte-Order-Mark detection across the five Unicode encodings.

    UTF-8     : EF BB BF              (3 bytes)
    UTF-16 BE : FE FF                 (2 bytes)
    UTF-16 LE : FF FE                 (2 bytes)
    UTF-32 BE : 00 00 FE FF           (4 bytes)
    UTF-32 LE : FF FE 00 00           (4 bytes)

Order matters: the UTF-32 BOMs share their leading bytes with the
UTF-16 BOMs, so the 4-byte patterns must be checked BEFORE the
2-byte patterns.  Specifically, ``FF FE 00 00`` is a UTF-32 LE
BOM, not a UTF-16 LE BOM followed by two NUL bytes.
"""

from enum import Enum


class BomKind(Enum):
    """The five Unicode encoding kinds distinguishable by their BOM."""

    UTF8 = "Utf8"
    UTF16_BE = "Utf16BE"
    UTF16_LE = "Utf16LE"
    UTF32_BE = "Utf32BE"
    UTF32_LE = "Utf32LE"


_LENGTHS: dict[BomKind, int] = {
    BomKind.UTF8: 3,
    BomKind.UTF16_BE: 2,
    BomKind.UTF16_LE: 2,
    BomKind.UTF32_BE: 4,
    BomKind.UTF32_LE: 4,
}


def bom_length(kind: BomKind) -> int:
    """The byte length of each BOM."""
    return _LENGTHS[kind]


def _byte_at(data: bytes, i: int) -> int:
    return data[i] if i < len(data) else 0


def detect(data: bytes) -> tuple[BomKind, int] | None:
    """Detect a leading BOM, returning the encoding kind and the
    number of BOM bytes to skip.

    The 4-byte UTF-32 BOMs are tested before the 2-byte UTF-16
    BOMs.  Returns ``None`` if the input does not begin with any
    recognised BOM.
    """
    b0 = _byte_at(data, 0)
    b1 = _byte_at(data, 1)
    b2 = _byte_at(data, 2)
    b3 = _byte_at(data, 3)
    if len(data) >= 4 and b0 == 0x00 and b1 == 0x00 and b2 == 0xFE and b3 == 0xFF:
        return (BomKind.UTF32_BE, 4)
    if len(data) >= 4 and b0 == 0xFF and b1 == 0xFE and b2 == 0x00 and b3 == 0x00:
        return (BomKind.UTF32_LE, 4)
    if len(data) >= 3 and b0 == 0xEF and b1 == 0xBB and b2 == 0xBF:
        return (BomKind.UTF8, 3)
    if len(data) >= 2 and b0 == 0xFE and b1 == 0xFF:
        return (BomKind.UTF16_BE, 2)
    if len(data) >= 2 and b0 == 0xFF and b1 == 0xFE:
        return (BomKind.UTF16_LE, 2)
    return None


def strip(data: bytes) -> tuple[BomKind | None, bytes]:
    """Strip the BOM from ``data`` if one is present, returning the
    remaining content together with the detected encoding.  When
    the input does not begin with a recognised BOM the function
    returns ``(None, data)``.
    """
    result = detect(data)
    if result is None:
        return (None, data)
    kind, k = result
    return (kind, data[k:])


__all__ = ["BomKind", "bom_length", "detect", "strip"]
