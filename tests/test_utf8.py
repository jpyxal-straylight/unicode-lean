"""Strict UTF-8 codec — acceptance, rejection, and roundtrip tests."""

import pytest

from unicode_python import (
    Utf8RejectKind,
    decode_to_codepoints,
    encode_codepoint,
    encode_codepoints,
    first_invalid_utf8_offset,
    is_valid_utf8,
)


# ─────────────────────────────────────────────────────────────────────
# Acceptance
# ─────────────────────────────────────────────────────────────────────


def test_accepts_empty_input() -> None:
    assert is_valid_utf8(b"")
    assert first_invalid_utf8_offset(b"") is None


def test_accepts_pure_ascii() -> None:
    assert is_valid_utf8(b"Hello")
    assert decode_to_codepoints(b"Hello") == [0x48, 0x65, 0x6C, 0x6C, 0x6F]


def test_accepts_two_byte_sequence() -> None:
    # U+00E9 é
    assert is_valid_utf8(b"\xc3\xa9")
    assert decode_to_codepoints(b"\xc3\xa9") == [0xE9]


def test_accepts_three_byte_sequence() -> None:
    # U+4E2D 中
    assert is_valid_utf8(b"\xe4\xb8\xad")
    assert decode_to_codepoints(b"\xe4\xb8\xad") == [0x4E2D]


def test_accepts_four_byte_sequence() -> None:
    # U+1F600 😀
    assert is_valid_utf8(b"\xf0\x9f\x98\x80")
    assert decode_to_codepoints(b"\xf0\x9f\x98\x80") == [0x1F600]


# ─────────────────────────────────────────────────────────────────────
# Rejection — every Utf8RejectKind
# ─────────────────────────────────────────────────────────────────────


def test_rejects_overlong_two_byte_via_invalid_start() -> None:
    # 0xC0 / 0xC1 rejected at the start-byte level.
    bytes_in = b"\xc0\xaf"
    assert not is_valid_utf8(bytes_in)
    assert first_invalid_utf8_offset(bytes_in) == (
        0,
        Utf8RejectKind.INVALID_START_BYTE,
    )


def test_rejects_overlong_three_byte() -> None:
    # 0xE0 0x80 0xAF — overlong encoding of U+002F
    bytes_in = b"\xe0\x80\xaf"
    assert not is_valid_utf8(bytes_in)
    assert first_invalid_utf8_offset(bytes_in) == (
        0,
        Utf8RejectKind.OVERLONG_ENCODING,
    )


def test_rejects_high_surrogate() -> None:
    # U+D800 attempted as 0xED 0xA0 0x80
    bytes_in = b"\xed\xa0\x80"
    assert not is_valid_utf8(bytes_in)
    result = first_invalid_utf8_offset(bytes_in)
    assert result is not None
    assert result[1] is Utf8RejectKind.SURROGATE_CODEPOINT


def test_rejects_codepoint_beyond_max() -> None:
    # U+110000 attempted as 0xF4 0x90 0x80 0x80
    bytes_in = b"\xf4\x90\x80\x80"
    assert not is_valid_utf8(bytes_in)
    result = first_invalid_utf8_offset(bytes_in)
    assert result is not None
    assert result[1] is Utf8RejectKind.CODEPOINT_BEYOND_MAX


def test_rejects_truncated_two_byte_sequence() -> None:
    bytes_in = b"\xc2"
    assert not is_valid_utf8(bytes_in)
    assert first_invalid_utf8_offset(bytes_in) == (
        1,
        Utf8RejectKind.TRUNCATED_SEQUENCE,
    )


def test_rejects_invalid_start_byte() -> None:
    bytes_in = b"\x80"
    assert not is_valid_utf8(bytes_in)
    assert first_invalid_utf8_offset(bytes_in) == (
        0,
        Utf8RejectKind.INVALID_START_BYTE,
    )


def test_rejects_invalid_continuation_byte() -> None:
    bytes_in = b"\xc2\x00"
    assert not is_valid_utf8(bytes_in)
    assert first_invalid_utf8_offset(bytes_in) == (
        1,
        Utf8RejectKind.INVALID_CONTINUATION_BYTE,
    )


def test_rejects_0xf5_start_byte() -> None:
    bytes_in = b"\xf5\x80\x80\x80"
    assert not is_valid_utf8(bytes_in)
    result = first_invalid_utf8_offset(bytes_in)
    assert result is not None
    assert result[1] is Utf8RejectKind.INVALID_START_BYTE


# ─────────────────────────────────────────────────────────────────────
# Encoder
# ─────────────────────────────────────────────────────────────────────


def test_encodes_one_byte_codepoints() -> None:
    assert encode_codepoint(0x00) == b"\x00"
    assert encode_codepoint(0x41) == b"\x41"
    assert encode_codepoint(0x7F) == b"\x7f"


def test_encodes_two_byte_codepoints() -> None:
    assert encode_codepoint(0x80) == b"\xc2\x80"
    assert encode_codepoint(0xE9) == b"\xc3\xa9"
    assert encode_codepoint(0x7FF) == b"\xdf\xbf"


def test_encodes_three_byte_codepoints() -> None:
    assert encode_codepoint(0x800) == b"\xe0\xa0\x80"
    assert encode_codepoint(0x4E2D) == b"\xe4\xb8\xad"
    assert encode_codepoint(0xFFFF) == b"\xef\xbf\xbf"


def test_encodes_four_byte_codepoints() -> None:
    assert encode_codepoint(0x10000) == b"\xf0\x90\x80\x80"
    assert encode_codepoint(0x1F600) == b"\xf0\x9f\x98\x80"
    assert encode_codepoint(0x10FFFF) == b"\xf4\x8f\xbf\xbf"


# ─────────────────────────────────────────────────────────────────────
# Roundtrips
# ─────────────────────────────────────────────────────────────────────


def test_roundtrips_mixed_codepoint_sequence() -> None:
    # 'H', 'i', U+00E9 é, U+4E2D 中, U+6587 文, U+1F600 😀
    cps = [0x48, 0x69, 0xE9, 0x4E2D, 0x6587, 0x1F600]
    encoded = encode_codepoints(cps)
    assert is_valid_utf8(encoded)
    assert decode_to_codepoints(encoded) == cps


@pytest.mark.parametrize(
    "cp",
    [
        0x00, 0x7F,         # 1-byte
        0x80, 0x7FF,        # 2-byte
        0x800, 0xD7FF,      # 3-byte just below surrogates
        0xE000, 0xFFFF,     # 3-byte just above surrogates
        0x10000, 0x10FFFF,  # 4-byte
    ],
)
def test_roundtrips_byte_class_boundary(cp: int) -> None:
    encoded = encode_codepoint(cp)
    assert is_valid_utf8(encoded)
    assert decode_to_codepoints(encoded) == [cp]
