"""Detection of invisible payloads encoded in the Unicode tag
block U+E0000..U+E007F.

Threat model.  Tier A1 (local injector).  Adversary crafts an
input containing tag-block codepoints that pass through string-
processing pipelines as zero-width / no-glyph characters but
carry a recoverable ASCII payload under the decoder

    tag(c) = c + 0xE0000 for c in [0x20, 0x7E].

No tag-block codepoint has a legitimate visible glyph or a
registered clean use in modern Unicode.  Every occurrence is
reportable; the detector's job is to attribute the kind of use
(direct payload, language-tag prefix, mixed-in-with-text, or
isolated single tag).
"""

from dataclasses import dataclass, field
from typing import Union

from ..calculus import ClassificationKind


def is_tag_character(cp: int) -> bool:
    """True iff cp is in the Unicode tag block U+E0000..U+E007F."""
    return 0xE0000 <= cp <= 0xE007F


def is_language_tag(cp: int) -> bool:
    return cp == 0xE0001


def is_cancel_tag(cp: int) -> bool:
    return cp == 0xE007F


def tag_to_ascii(cp: int) -> str | None:
    """Decode a tag-block codepoint to its ASCII correspondent.
    Returns ``None`` for tag codepoints outside the printable-ASCII
    range and for any non-tag codepoint."""
    if 0xE0020 <= cp <= 0xE007E:
        return chr(cp - 0xE0000)
    return None


@dataclass(frozen=True, slots=True)
class DirectAscii:
    decoded: str


@dataclass(frozen=True, slots=True)
class LanguageTagRevival:
    lang_tag_pos: int
    decoded_tail: str


@dataclass(frozen=True, slots=True)
class MixedBlock:
    tag_count: int
    total_cps: int


@dataclass(frozen=True, slots=True)
class BareTagPresent:
    tag_cp: int


SubThreat = Union[DirectAscii, LanguageTagRevival, MixedBlock, BareTagPresent]


def sub_threat_tag(sub: SubThreat) -> str:
    if isinstance(sub, DirectAscii):
        return "DirectAscii"
    if isinstance(sub, LanguageTagRevival):
        return "LanguageTagRevival"
    if isinstance(sub, MixedBlock):
        return "MixedBlock"
    return "BareTagPresent"


@dataclass(slots=True)
class Verdict:
    kind: ClassificationKind
    sub: SubThreat | None = None
    tag_positions: list[int] = field(default_factory=list)
    recovered_ascii: str = ""


def _decode_tag_run(input_cps: list[int], positions: list[int]) -> str:
    out = []
    for p in positions:
        if p < len(input_cps):
            c = tag_to_ascii(input_cps[p])
            if c is not None:
                out.append(c)
    return "".join(out)


def detect(input_cps: list[int]) -> Verdict:
    """Detect tag-block payloads in ``input_cps``.

    Returns a structured verdict; the ``kind`` field is
    ``CLEAR`` when no tag-block codepoints are present, otherwise
    ``HAZARD`` with a ``sub`` field carrying the categorised
    sub-threat.
    """
    tag_positions = [i for i, cp in enumerate(input_cps) if is_tag_character(cp)]
    if not tag_positions:
        return Verdict(kind=ClassificationKind.CLEAR)

    decoded = _decode_tag_run(input_cps, tag_positions)

    # Phase 4: pick sub-threat by priority.
    sub: SubThreat
    first_pos = tag_positions[0]
    if first_pos < len(input_cps) and is_language_tag(input_cps[first_pos]) and len(tag_positions) >= 2:
        tail = [p for p in tag_positions if p != first_pos]
        sub = LanguageTagRevival(
            lang_tag_pos=first_pos,
            decoded_tail=_decode_tag_run(input_cps, tail),
        )
    elif all(is_tag_character(cp) for cp in input_cps) and decoded:
        sub = DirectAscii(decoded=decoded)
    elif len(input_cps) > len(tag_positions):
        sub = MixedBlock(tag_count=len(tag_positions), total_cps=len(input_cps))
    else:
        sub = BareTagPresent(tag_cp=input_cps[first_pos])

    return Verdict(
        kind=ClassificationKind.HAZARD,
        sub=sub,
        tag_positions=tag_positions,
        recovered_ascii=decoded,
    )


__all__ = [
    "BareTagPresent",
    "DirectAscii",
    "LanguageTagRevival",
    "MixedBlock",
    "SubThreat",
    "Verdict",
    "detect",
    "is_cancel_tag",
    "is_language_tag",
    "is_tag_character",
    "sub_threat_tag",
    "tag_to_ascii",
]
