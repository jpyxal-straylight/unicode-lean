"""Opaque text predicate — structurally valid UTF-8, size-bounded.

No character-class or codepoint filtering beyond UTF-8 validity.
Intended for callers who apply their own text hardening
downstream; hardened identifier and printable profiles layer on
top of this predicate.
"""

from dataclasses import dataclass

from .utf8 import is_valid_utf8


def is_utf8_blob(data: bytes) -> bool:
    """Opaque-blob predicate: structurally valid UTF-8.  Exposed
    under this name so the "blob" framing — no character-class
    hardening — is explicit at the call site."""
    return is_valid_utf8(data)


@dataclass(frozen=True, slots=True)
class Utf8Blob:
    """A byte sequence carrying its size bound and UTF-8 validity
    claim.  Construct via :meth:`of`.
    """

    value: bytes
    max_bytes: int

    @classmethod
    def of(cls, data: bytes, max_bytes: int) -> "Utf8Blob | None":
        """Build a ``Utf8Blob`` under the size bound ``max_bytes``.
        Returns ``None`` when either the bound or UTF-8 validity
        is violated."""
        if len(data) > max_bytes:
            return None
        if not is_utf8_blob(data):
            return None
        return cls(value=data, max_bytes=max_bytes)


__all__ = ["Utf8Blob", "is_utf8_blob"]
