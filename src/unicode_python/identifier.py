"""Strict ASCII identifier predicate — ``[a-zA-Z_][a-zA-Z0-9_]*``.

  * The first byte MUST be in 0x41..0x5A (A–Z),
    0x61..0x7A (a–z), or 0x5F (_).
  * Subsequent bytes MUST be in the first-byte set OR
    0x30..0x39 (0–9).
  * Empty byte sequences are REJECTED.

The codec stays strict ASCII permanently.  Callers needing
Unicode identifiers route through a PRECIS identifier codec
(RFC 8264 / 8265) layered on top, providing defense-in-depth: an
ASCII belt plus PRECIS suspenders.
"""

from dataclasses import dataclass


def is_identifier_start_byte(b: int) -> bool:
    """Whether ``b`` may start an ASCII identifier: A–Z, a–z, or ``_``."""
    return (0x41 <= b <= 0x5A) or (0x61 <= b <= 0x7A) or b == 0x5F


def is_identifier_continue_byte(b: int) -> bool:
    """Whether ``b`` may continue an ASCII identifier: the
    start-byte set plus 0–9."""
    return is_identifier_start_byte(b) or 0x30 <= b <= 0x39


def first_invalid_identifier_continue_from(
    data: bytes, start: int
) -> tuple[int, int] | None:
    """Walk the continuation positions of ``data`` starting at
    ``start``, returning the offset and value of the first byte
    that fails :func:`is_identifier_continue_byte`.  Returns
    ``None`` when every position from ``start`` onward is a valid
    continuation byte.
    """
    for i in range(start, len(data)):
        b = data[i]
        if not is_identifier_continue_byte(b):
            return (i, b)
    return None


def is_valid_identifier_bytes(data: bytes) -> bool:
    """ASCII-identifier predicate: non-empty, valid start byte at
    position zero, and every subsequent byte a valid continuation
    byte."""
    if len(data) == 0:
        return False
    if not is_identifier_start_byte(data[0]):
        return False
    return first_invalid_identifier_continue_from(data, 1) is None


@dataclass(frozen=True, slots=True)
class IdentifierUtf8:
    """A byte sequence carrying its size bound and identifier-
    validity claim.  Construct via :meth:`of`.
    """

    value: bytes
    max_bytes: int

    @classmethod
    def of(cls, data: bytes, max_bytes: int) -> "IdentifierUtf8 | None":
        """Build an ``IdentifierUtf8`` under the size bound
        ``max_bytes``.  Returns ``None`` when either the bound or
        identifier validity is violated."""
        if len(data) > max_bytes:
            return None
        if not is_valid_identifier_bytes(data):
            return None
        return cls(value=data, max_bytes=max_bytes)


__all__ = [
    "IdentifierUtf8",
    "first_invalid_identifier_continue_from",
    "is_identifier_continue_byte",
    "is_identifier_start_byte",
    "is_valid_identifier_bytes",
]
