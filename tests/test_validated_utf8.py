"""ValidatedUtf8 refinement-type tests."""

from unicode_python.validated_utf8 import ValidatedUtf8, unwrap


def test_validates_valid_input() -> None:
    assert ValidatedUtf8.validate(b"Hi") is not None


def test_rejects_overlong_nul() -> None:
    assert ValidatedUtf8.validate(bytes([0xC0, 0x80])) is None


def test_rejects_surrogate_codepoint() -> None:
    assert ValidatedUtf8.validate(bytes([0xED, 0xA0, 0x80])) is None


def test_rejects_codepoint_beyond_max() -> None:
    assert ValidatedUtf8.validate(bytes([0xF4, 0x90, 0x80, 0x80])) is None


def test_rejects_truncated_sequence() -> None:
    assert ValidatedUtf8.validate(bytes([0xC2])) is None


def test_as_bytes_returns_validated_bytes() -> None:
    v = ValidatedUtf8.validate(b"Hi")
    assert v is not None
    assert v.as_bytes() == b"Hi"


def test_unwrap_consumes_the_claim() -> None:
    v = ValidatedUtf8.validate(b"Hi")
    assert v is not None
    assert unwrap(v) == b"Hi"


def test_validates_empty_input() -> None:
    v = ValidatedUtf8.validate(b"")
    assert v is not None
    assert v.as_bytes() == b""
