"""BOM-detection tests."""

from unicode_python.bom import BomKind, bom_length, detect, strip


def test_returns_none_on_empty_input() -> None:
    assert detect(b"") is None


def test_returns_none_on_non_bom_bytes() -> None:
    assert detect(bytes([0x41, 0x42, 0x43])) is None


def test_detects_utf8_bom() -> None:
    assert detect(bytes([0xEF, 0xBB, 0xBF])) == (BomKind.UTF8, 3)


def test_detects_utf16_be_bom() -> None:
    assert detect(bytes([0xFE, 0xFF])) == (BomKind.UTF16_BE, 2)


def test_detects_utf16_le_bom_two_bytes() -> None:
    assert detect(bytes([0xFF, 0xFE])) == (BomKind.UTF16_LE, 2)


def test_detects_utf32_be_bom() -> None:
    assert detect(bytes([0x00, 0x00, 0xFE, 0xFF])) == (
        BomKind.UTF32_BE,
        4,
    )


def test_detects_utf32_le_precedence_over_utf16_le() -> None:
    assert detect(bytes([0xFF, 0xFE, 0x00, 0x00])) == (
        BomKind.UTF32_LE,
        4,
    )


def test_detects_utf16_le_when_followed_by_nonzero() -> None:
    assert detect(bytes([0xFF, 0xFE, 0x41])) == (BomKind.UTF16_LE, 2)


def test_reports_bom_length_for_each_kind() -> None:
    assert bom_length(BomKind.UTF8) == 3
    assert bom_length(BomKind.UTF16_BE) == 2
    assert bom_length(BomKind.UTF16_LE) == 2
    assert bom_length(BomKind.UTF32_BE) == 4
    assert bom_length(BomKind.UTF32_LE) == 4


def test_strip_returns_kind_and_rest() -> None:
    kind, rest = strip(bytes([0xEF, 0xBB, 0xBF, 0x48, 0x69]))
    assert kind is BomKind.UTF8
    assert rest == bytes([0x48, 0x69])


def test_strip_passes_through_when_no_bom() -> None:
    data = bytes([0x41, 0x42])
    kind, rest = strip(data)
    assert kind is None
    assert rest == data
