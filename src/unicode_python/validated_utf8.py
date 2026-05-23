"""Refinement type for bytes validated as strict RFC 3629 UTF-8.

The validity claim is pinned at the module-boundary level: the
only way to construct a :class:`ValidatedUtf8` is via the smart
constructor :meth:`ValidatedUtf8.validate`, which routes through
the strict decoder state machine.

Rationale: the ingestion layer is security-critical.  A plain
``bytes`` field on a codec output type carries no claim about its
UTF-8 validity — downstream consumers have to either re-validate
or trust the producer.  ``ValidatedUtf8`` makes the claim
module-level, so a downstream consumer that wants the raw bytes
has to explicitly :meth:`unwrap` — which reads as "I am
consuming the RFC 3629 claim here".
"""

from dataclasses import dataclass

from .utf8 import is_valid_utf8


@dataclass(frozen=True, slots=True)
class ValidatedUtf8:
    """A ``bytes`` value that has been validated as strict RFC 3629
    UTF-8.  The constructor is conventionally private;
    :meth:`validate` is the only blessed way to build one."""

    _bytes: bytes

    @classmethod
    def validate(cls, data: bytes) -> "ValidatedUtf8 | None":
        """Validate ``data`` and, on success, return a
        :class:`ValidatedUtf8` carrying the RFC 3629 validity
        claim.  Returns ``None`` when the bytes fail the strict
        state machine."""
        if not is_valid_utf8(data):
            return None
        return cls(_bytes=data)

    def as_bytes(self) -> bytes:
        """Borrow the validated bytes."""
        return self._bytes


def unwrap(validated: ValidatedUtf8) -> bytes:
    """Consume the validity claim, returning the underlying bytes.

    After this call the validity claim is no longer carried at
    the module-boundary level — the caller owns the "these bytes
    are RFC 3629 valid" reasoning from here forward.
    """
    return validated._bytes


__all__ = ["ValidatedUtf8", "unwrap"]
