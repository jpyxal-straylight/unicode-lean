"""Strict ASCII identifier tests."""

import pytest

from unicode_python.identifier import (
    IdentifierUtf8,
    first_invalid_identifier_continue_from,
    is_identifier_continue_byte,
    is_identifier_start_byte,
    is_valid_identifier_bytes,
)


@pytest.mark.parametrize("c", list("AZazMno_"))
def test_accepts_start_bytes(c: str) -> None:
    assert is_identifier_start_byte(ord(c))


@pytest.mark.parametrize("c", list("0123-.@$"))
def test_rejects_digits_and_punctuation_as_start(c: str) -> None:
    assert not is_identifier_start_byte(ord(c))


@pytest.mark.parametrize("c", list("Az_09"))
def test_accepts_continue_bytes(c: str) -> None:
    assert is_identifier_continue_byte(ord(c))


@pytest.mark.parametrize("c", list("-.@$ "))
def test_rejects_punctuation_as_continue(c: str) -> None:
    assert not is_identifier_continue_byte(ord(c))


def test_rejects_empty_input() -> None:
    assert not is_valid_identifier_bytes(b"")


def test_accepts_single_underscore() -> None:
    assert is_valid_identifier_bytes(b"_")


@pytest.mark.parametrize("s", ["x", "foo", "foo_bar", "X123", "_x9"])
def test_accepts_typical_identifiers(s: str) -> None:
    assert is_valid_identifier_bytes(s.encode("ascii"))


def test_rejects_starting_with_digit() -> None:
    assert not is_valid_identifier_bytes(b"1abc")


@pytest.mark.parametrize("s", ["foo-bar", "a.b", "a@b", "a b"])
def test_rejects_punctuation_inside(s: str) -> None:
    assert not is_valid_identifier_bytes(s.encode("ascii"))


def test_rejects_non_ascii_bytes() -> None:
    assert not is_valid_identifier_bytes(bytes([0x80]))
    assert not is_valid_identifier_bytes(bytes([0x41, 0xC2, 0xA0]))


def test_walker_returns_none_on_all_valid() -> None:
    assert first_invalid_identifier_continue_from(b"abc123", 1) is None


def test_walker_returns_first_invalid_offset() -> None:
    assert first_invalid_identifier_continue_from(b"foo-bar", 1) == (
        3,
        0x2D,
    )


def test_refinement_builds_when_valid_and_within_bound() -> None:
    ident = IdentifierUtf8.of(b"foo", 16)
    assert ident is not None
    assert ident.value == b"foo"
    assert ident.max_bytes == 16


def test_refinement_rejects_over_bound() -> None:
    assert IdentifierUtf8.of(b"foo_bar", 4) is None


def test_refinement_rejects_invalid() -> None:
    assert IdentifierUtf8.of(b"1abc", 16) is None
