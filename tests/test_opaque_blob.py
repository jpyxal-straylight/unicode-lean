"""Utf8Blob refinement-type tests."""

from unicode_python.opaque_blob import Utf8Blob, is_utf8_blob


def test_accepts_valid_utf8() -> None:
    assert is_utf8_blob(b"Hi")
    assert is_utf8_blob(bytes([0xC3, 0xA9]))
    assert is_utf8_blob(bytes([0xF0, 0x9F, 0x98, 0x80]))


def test_rejects_invalid_utf8() -> None:
    assert not is_utf8_blob(bytes([0xC0, 0x80]))
    assert not is_utf8_blob(bytes([0xED, 0xA0, 0x80]))


def test_refinement_builds_within_bound() -> None:
    blob = Utf8Blob.of(b"Hi", 16)
    assert blob is not None
    assert blob.value == b"Hi"
    assert blob.max_bytes == 16


def test_refinement_rejects_over_bound() -> None:
    assert Utf8Blob.of(b"Hi!", 2) is None


def test_refinement_rejects_malformed_utf8() -> None:
    assert Utf8Blob.of(bytes([0xC0, 0x80]), 16) is None


def test_refinement_accepts_empty_under_any_bound() -> None:
    assert Utf8Blob.of(b"", 32) is not None
