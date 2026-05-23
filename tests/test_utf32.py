"""UTF-32 codec tests."""

import pytest

from unicode_python.utf32 import (
    decode_one_be,
    decode_one_le,
    encode_be,
    encode_le,
    encode_one_be,
    encode_one_le,
)


def test_encodes_ascii_be_le() -> None:
    assert encode_one_be(0x41) == bytes([0x00, 0x00, 0x00, 0x41])
    assert encode_one_le(0x41) == bytes([0x41, 0x00, 0x00, 0x00])


def test_encodes_bmp_be_le() -> None:
    assert encode_one_be(0x4E2D) == bytes([0x00, 0x00, 0x4E, 0x2D])
    assert encode_one_le(0x4E2D) == bytes([0x2D, 0x4E, 0x00, 0x00])


def test_encodes_supplementary_be_le() -> None:
    assert encode_one_be(0x1F600) == bytes([0x00, 0x01, 0xF6, 0x00])
    assert encode_one_le(0x1F600) == bytes([0x00, 0xF6, 0x01, 0x00])


def test_encodes_u10ffff() -> None:
    assert encode_one_be(0x10FFFF) == bytes([0x00, 0x10, 0xFF, 0xFF])
    assert encode_one_le(0x10FFFF) == bytes([0xFF, 0xFF, 0x10, 0x00])


def test_decodes_valid_scalars_be_le() -> None:
    assert decode_one_be(bytes([0x00, 0x00, 0x00, 0x41])) == 0x41
    assert decode_one_le(bytes([0x41, 0x00, 0x00, 0x00])) == 0x41


def test_rejects_surrogates() -> None:
    assert decode_one_be(bytes([0x00, 0x00, 0xD8, 0x00])) is None
    assert decode_one_le(bytes([0xFF, 0xDF, 0x00, 0x00])) is None


def test_rejects_beyond_max() -> None:
    assert decode_one_be(bytes([0x00, 0x11, 0x00, 0x00])) is None
    assert decode_one_le(bytes([0x00, 0x00, 0x11, 0x00])) is None


@pytest.mark.parametrize("n", [0, 1, 2, 3, 5, 6, 8])
def test_rejects_invalid_lengths(n: int) -> None:
    assert decode_one_be(b"\x00" * n) is None
    assert decode_one_le(b"\x00" * n) is None


@pytest.mark.parametrize(
    "cp",
    [0x00, 0x7F, 0x80, 0xD7FF, 0xE000, 0xFFFF, 0x10000, 0x10FFFF],
)
def test_roundtrips_boundaries(cp: int) -> None:
    assert decode_one_be(encode_one_be(cp)) == cp
    assert decode_one_le(encode_one_le(cp)) == cp


def test_encodes_sequence_be() -> None:
    out = encode_be([0x41, 0x4E2D, 0x1F600])
    assert len(out) == 12
    assert out[0:4] == bytes([0x00, 0x00, 0x00, 0x41])
    assert out[4:8] == bytes([0x00, 0x00, 0x4E, 0x2D])
    assert out[8:12] == bytes([0x00, 0x01, 0xF6, 0x00])


def test_encodes_sequence_le() -> None:
    out = encode_le([0x41, 0x4E2D, 0x1F600])
    assert len(out) == 12
    assert out[0:4] == bytes([0x41, 0x00, 0x00, 0x00])
