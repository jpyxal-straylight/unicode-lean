"""Strict Unicode-as-attack-surface conformance for Python.

The package's public surface is a family of strict text codecs
(UTF-8, UTF-16 BE/LE, UTF-32 BE/LE, BOM detection, noncharacter
predicate, ASCII identifier predicate) and three refinement
types (``Utf8Blob``, ``IdentifierUtf8``, ``ValidatedUtf8``) that
carry their validity claim at the module-boundary level.
"""

from . import bom, utf16, utf32
from .bom import BomKind, bom_length
from .bom import detect as detect_bom
from .bom import strip as strip_bom
from .identifier import (
    IdentifierUtf8,
    first_invalid_identifier_continue_from,
    is_identifier_continue_byte,
    is_identifier_start_byte,
    is_valid_identifier_bytes,
)
from .noncharacters import all_noncharacters, is_noncharacter
from .opaque_blob import Utf8Blob, is_utf8_blob
from .strict import Utf8RejectKind
from .utf8 import (
    Continue,
    Emit,
    ExpectCont,
    ExpectStart,
    Reject,
    Utf8State,
    Utf8StepResult,
    decode_to_codepoints,
    encode_codepoint,
    encode_codepoints,
    first_invalid_utf8_offset,
    is_valid_utf8,
    utf8_decode_step,
)
from .validated_utf8 import ValidatedUtf8, unwrap

__all__ = [
    "BomKind",
    "Continue",
    "Emit",
    "ExpectCont",
    "ExpectStart",
    "IdentifierUtf8",
    "Reject",
    "Utf8Blob",
    "Utf8RejectKind",
    "Utf8State",
    "Utf8StepResult",
    "ValidatedUtf8",
    "all_noncharacters",
    "bom",
    "bom_length",
    "decode_to_codepoints",
    "detect_bom",
    "encode_codepoint",
    "encode_codepoints",
    "first_invalid_identifier_continue_from",
    "first_invalid_utf8_offset",
    "is_identifier_continue_byte",
    "is_identifier_start_byte",
    "is_noncharacter",
    "is_utf8_blob",
    "is_valid_identifier_bytes",
    "is_valid_utf8",
    "strip_bom",
    "utf16",
    "utf32",
    "utf8_decode_step",
    "unwrap",
]
