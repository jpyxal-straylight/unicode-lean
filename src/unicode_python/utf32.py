"""UTF-32 codec — big-endian and little-endian variants.

Each scalar Unicode codepoint encodes to exactly 4 bytes; the
invariant is straight identity, no length-dependent escape
sequences.  The decoder rejects inputs whose length is not
exactly 4, 4-byte sequences encoding a surrogate codepoint
U+D800..U+DFFF, and 4-byte sequences encoding a value above
U+10FFFF.
"""

def encode_one_be(cp: int) -> bytes:
    """Encode a scalar codepoint as 4 bytes in big-endian order."""
    return cp.to_bytes(4, "big", signed=False)


def encode_one_le(cp: int) -> bytes:
    """Encode a scalar codepoint as 4 bytes in little-endian order."""
    return cp.to_bytes(4, "little", signed=False)


def _scalar(cp: int) -> int | None:
    if cp > 0x10FFFF:
        return None
    if 0xD800 <= cp <= 0xDFFF:
        return None
    return cp


def decode_one_be(data: bytes) -> int | None:
    """Decode 4 bytes as a big-endian UTF-32 codepoint.

    Returns ``None`` when the length is not exactly 4, the decoded
    value is a surrogate, or the value exceeds U+10FFFF.
    """
    if len(data) != 4:
        return None
    return _scalar(int.from_bytes(data, "big", signed=False))


def decode_one_le(data: bytes) -> int | None:
    """Decode 4 bytes as a little-endian UTF-32 codepoint."""
    if len(data) != 4:
        return None
    return _scalar(int.from_bytes(data, "little", signed=False))


def encode_be(cps: list[int]) -> bytes:
    """Concatenate the UTF-32 BE encodings of a codepoint sequence."""
    return b"".join(encode_one_be(cp) for cp in cps)


def encode_le(cps: list[int]) -> bytes:
    """Concatenate the UTF-32 LE encodings of a codepoint sequence."""
    return b"".join(encode_one_le(cp) for cp in cps)


__all__ = [
    "decode_one_be",
    "decode_one_le",
    "encode_be",
    "encode_le",
    "encode_one_be",
    "encode_one_le",
]
