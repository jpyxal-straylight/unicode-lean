"""UTF-16 codec tests."""

import pytest

from unicode_python.utf16 import (
    decode_one_be,
    decode_one_le,
    encode_be,
    encode_le,
    encode_one_be,
    encode_one_le,
)


def test_encodes_ascii_bmp_be_le() -> None:
    assert encode_one_be(0x0041) == bytes([0x00, 0x41])
    assert encode_one_le(0x0041) == bytes([0x41, 0x00])


def test_encodes_supplementary_plane() -> None:
    assert encode_one_be(0x1F600) == bytes([0xD8, 0x3D, 0xDE, 0x00])
    assert encode_one_le(0x1F600) == bytes([0x3D, 0xD8, 0x00, 0xDE])


def test_encodes_u10ffff_as_maximal_pair() -> None:
    assert encode_one_be(0x10FFFF) == bytes([0xDB, 0xFF, 0xDF, 0xFF])


def test_decodes_bmp_be_le() -> None:
    assert decode_one_be(bytes([0x00, 0x41])) == 0x0041
    assert decode_one_le(bytes([0x41, 0x00])) == 0x0041


def test_decodes_supplementary_pair() -> None:
    assert decode_one_be(bytes([0xD8, 0x3D, 0xDE, 0x00])) == 0x1F600
    assert decode_one_le(bytes([0x3D, 0xD8, 0x00, 0xDE])) == 0x1F600


def test_rejects_lone_high_surrogate() -> None:
    assert decode_one_be(bytes([0xD8, 0x00])) is None
    assert decode_one_le(bytes([0x00, 0xD8])) is None


def test_rejects_lone_low_surrogate() -> None:
    assert decode_one_be(bytes([0xDC, 0x00])) is None


def test_rejects_high_followed_by_non_low() -> None:
    assert decode_one_be(bytes([0xD8, 0x00, 0x00, 0x42])) is None


@pytest.mark.parametrize("n", [0, 1, 3, 5, 6])
def test_rejects_invalid_lengths(n: int) -> None:
    assert decode_one_be(b"\x00" * n) is None
    assert decode_one_le(b"\x00" * n) is None


@pytest.mark.parametrize(
    "cp",
    [
        0x0000, 0x007F, 0x0080, 0xD7FF, 0xE000, 0xFFFD,
        0x10000, 0x1F600, 0x10FFFD, 0x10FFFF,
    ],
)
def test_roundtrips_boundaries(cp: int) -> None:
    assert decode_one_be(encode_one_be(cp)) == cp
    assert decode_one_le(encode_one_le(cp)) == cp


def test_encodes_mixed_sequence_be() -> None:
    assert encode_be([0x0041, 0x1F600]) == bytes(
        [0x00, 0x41, 0xD8, 0x3D, 0xDE, 0x00]
    )


def test_encodes_mixed_sequence_le() -> None:
    assert encode_le([0x0041, 0x1F600]) == bytes(
        [0x41, 0x00, 0x3D, 0xD8, 0x00, 0xDE]
    )
