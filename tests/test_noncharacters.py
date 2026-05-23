"""Noncharacter predicate tests."""

import pytest

from unicode_python.noncharacters import all_noncharacters, is_noncharacter


@pytest.mark.parametrize("cp", list(range(0xFDD0, 0xFDF0)))
def test_flags_bmp_block(cp: int) -> None:
    assert is_noncharacter(cp)


@pytest.mark.parametrize("n", list(range(17)))
def test_flags_plane_ends(n: int) -> None:
    assert is_noncharacter(n * 0x10000 + 0xFFFE)
    assert is_noncharacter(n * 0x10000 + 0xFFFF)


@pytest.mark.parametrize("cp", [0x00, 0x41, 0x7F])
def test_rejects_ascii(cp: int) -> None:
    assert not is_noncharacter(cp)


def test_rejects_adjacent_to_fddx_block() -> None:
    assert not is_noncharacter(0xFDCF)
    assert not is_noncharacter(0xFDF0)


def test_rejects_replacement_character() -> None:
    assert not is_noncharacter(0xFFFD)


def test_rejects_codepoints_above_max() -> None:
    assert not is_noncharacter(0x110000)
    assert not is_noncharacter(0x10FFFF + 0xFFFF)


def test_enumerates_exactly_66() -> None:
    assert len(all_noncharacters()) == 66


def test_enumeration_is_ascending() -> None:
    all_ = all_noncharacters()
    assert all(all_[i] < all_[i + 1] for i in range(len(all_) - 1))


def test_every_enumerated_satisfies_predicate() -> None:
    for cp in all_noncharacters():
        assert is_noncharacter(cp)
