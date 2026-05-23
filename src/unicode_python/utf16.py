"""UTF-16 codec — big-endian and little-endian variants.

Each scalar Unicode codepoint encodes to either 2 bytes (BMP) or
4 bytes (supplementary planes via surrogate pair).  The
supplementary pair is constructed as

    X    = cp - 0x10000          (20-bit value)
    high = 0xD800 + (X >> 10)    (high surrogate, 0xD800..0xDBFF)
    low  = 0xDC00 + (X & 0x3FF)  (low  surrogate, 0xDC00..0xDFFF)

The decoder rejects inputs whose length is not exactly 2 or 4,
2-byte sequences in the surrogate range U+D800..U+DFFF (lone
surrogate), and 4-byte sequences not forming a valid (high, low)
surrogate pair.
"""

def encode_one_be(cp: int) -> bytes:
    """Encode a scalar codepoint as 2 or 4 bytes in big-endian UTF-16.

    The function trusts its input: codepoints outside the valid
    scalar range (0..0x10FFFF minus surrogates) produce bogus
    output.  The decoder rejects them.
    """
    if cp < 0x10000:
        return bytes([(cp >> 8) & 0xFF, cp & 0xFF])
    x = cp - 0x10000
    high = 0xD800 + (x >> 10)
    low = 0xDC00 + (x & 0x3FF)
    return bytes(
        [
            (high >> 8) & 0xFF,
            high & 0xFF,
            (low >> 8) & 0xFF,
            low & 0xFF,
        ]
    )


def encode_one_le(cp: int) -> bytes:
    """Encode a scalar codepoint as 2 or 4 bytes in little-endian UTF-16."""
    if cp < 0x10000:
        return bytes([cp & 0xFF, (cp >> 8) & 0xFF])
    x = cp - 0x10000
    high = 0xD800 + (x >> 10)
    low = 0xDC00 + (x & 0x3FF)
    return bytes(
        [
            high & 0xFF,
            (high >> 8) & 0xFF,
            low & 0xFF,
            (low >> 8) & 0xFF,
        ]
    )


def _scalar_from_pair(high: int, low: int) -> int | None:
    if not 0xD800 <= high <= 0xDBFF:
        return None
    if not 0xDC00 <= low <= 0xDFFF:
        return None
    return 0x10000 + ((high - 0xD800) << 10) + (low - 0xDC00)


def decode_one_be(data: bytes) -> int | None:
    """Decode a UTF-16 BE byte sequence as a single codepoint.

    Returns ``None`` on length mismatch, lone surrogate, or
    invalid surrogate pair.  Accepts byte sequences of length
    exactly 2 (BMP) or 4 (supplementary-plane surrogate pair).
    """
    if len(data) == 2:
        u = (data[0] << 8) | data[1]
        if 0xD800 <= u <= 0xDFFF:
            return None
        return u
    if len(data) == 4:
        high = (data[0] << 8) | data[1]
        low = (data[2] << 8) | data[3]
        return _scalar_from_pair(high, low)
    return None


def decode_one_le(data: bytes) -> int | None:
    """Decode a UTF-16 LE byte sequence as a single codepoint."""
    if len(data) == 2:
        u = data[0] | (data[1] << 8)
        if 0xD800 <= u <= 0xDFFF:
            return None
        return u
    if len(data) == 4:
        high = data[0] | (data[1] << 8)
        low = data[2] | (data[3] << 8)
        return _scalar_from_pair(high, low)
    return None


def encode_be(cps: list[int]) -> bytes:
    """Concatenate the UTF-16 BE encodings of a codepoint sequence."""
    return b"".join(encode_one_be(cp) for cp in cps)


def encode_le(cps: list[int]) -> bytes:
    """Concatenate the UTF-16 LE encodings of a codepoint sequence."""
    return b"".join(encode_one_le(cp) for cp in cps)


__all__ = [
    "decode_one_be",
    "decode_one_le",
    "encode_be",
    "encode_le",
    "encode_one_be",
    "encode_one_le",
]
