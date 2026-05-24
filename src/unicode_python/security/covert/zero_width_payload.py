"""Detection of payloads encoded in zero-width and near-zero-width
Unicode codepoints.

Threat model.  Tier A1.  Adversary embeds zero-width / no-glyph
codepoints inside otherwise-normal text to carry a covert binary
payload, to splice WORD JOINER / byte-order-mark sequences into
identifiers, or to emit a suspected AI-watermark NNBSP pattern.

Zero-width codepoint inventory:

    U+200B  ZERO WIDTH SPACE                (ZWSP)
    U+200C  ZERO WIDTH NON-JOINER           (ZWNJ)
    U+200D  ZERO WIDTH JOINER               (ZWJ)
    U+200E  LEFT-TO-RIGHT MARK              (LRM)
    U+200F  RIGHT-TO-LEFT MARK              (RLM)
    U+2060  WORD JOINER                     (WJ)
    U+2061..U+2064  invisible math operators
    U+202F  NARROW NO-BREAK SPACE           (NNBSP)
    U+FEFF  ZERO WIDTH NO-BREAK SPACE / BOM
    U+FFF9..U+FFFB  INTERLINEAR ANNOTATION marks

This port treats every zero-width occurrence as reportable.  The
Lean reference additionally exempts ZWJ flanked by emoji
codepoints (RGI-context legitimate emoji-ZWJ sequence) — that
exemption requires the UCD emoji-data table.  Callers needing
emoji-aware ZWJ exemption can pre-filter the input before calling
this detector.
"""

from dataclasses import dataclass, field
from typing import Union

from ..calculus import ClassificationKind
from ..identity import ucd


def _is_sibling_handled(cp: int) -> bool:
    """Sibling-detector codepoint ranges — these ARE
    Default_Ignorable per UAX #44 but are dispatched elsewhere:

      - U+FE00..U+FE0F      VariationSelectorPayload
      - U+E0100..U+E01EF    VariationSelectorPayload
      - U+E0000..U+E007F    TagBlockPayload
      - U+202A..U+202E      BidiControlBalance (LRE/RLE/PDF/LRO/RLO)
      - U+2066..U+2069      BidiControlBalance (LRI/RLI/FSI/PDI)

    LRM / RLM (U+200E / U+200F) are NOT excluded — they're
    direction markers, not push/pop bidi controls.
    """
    return (
        0xFE00 <= cp <= 0xFE0F
        or 0xE0100 <= cp <= 0xE01EF
        or 0xE0000 <= cp <= 0xE007F
        or 0x202A <= cp <= 0x202E
        or 0x2066 <= cp <= 0x2069
    )


def is_zero_width(cp: int) -> bool:
    """True iff `cp` is a Unicode codepoint that renders as
    nothing OR is in the explicit historical "tracked zero-width"
    set.  Built on the explicit hardcoded list PLUS UAX #44
    Default_Ignorable_Code_Point, with sibling-detector exclusions.
    """
    # Explicit historical set — preserves sub-threat dispatch.
    if cp in (0x200B, 0x200C, 0x200D, 0x200E, 0x200F):
        return True
    if 0x2060 <= cp <= 0x2064:
        return True
    if cp == 0x202F or cp == 0xFEFF:
        return True
    if 0xFFF9 <= cp <= 0xFFFB:
        return True
    # UAX #44 Default_Ignorable_Code_Point — catches everything
    # else invisible, modulo sibling-detector ranges.
    return ucd.is_default_ignorable(cp) and not _is_sibling_handled(cp)


def is_nnbsp(cp: int) -> bool:
    return cp == 0x202F


def is_word_joiner(cp: int) -> bool:
    return cp == 0x2060


def is_annotation(cp: int) -> bool:
    return 0xFFF9 <= cp <= 0xFFFB


def is_zwj_or_zwsp(cp: int) -> bool:
    return cp in (0x200B, 0x200D)


@dataclass(frozen=True, slots=True)
class AnnotationMisuse:
    count: int


@dataclass(frozen=True, slots=True)
class WordJoinerInjection:
    count: int


@dataclass(frozen=True, slots=True)
class AiWatermarkNNBSP:
    count: int


@dataclass(frozen=True, slots=True)
class BinaryPayload:
    pair_count: int


@dataclass(frozen=True, slots=True)
class BareZeroWidth:
    cp: int


SubThreat = Union[
    AnnotationMisuse,
    WordJoinerInjection,
    AiWatermarkNNBSP,
    BinaryPayload,
    BareZeroWidth,
]


def sub_threat_tag(sub: SubThreat) -> str:
    if isinstance(sub, AnnotationMisuse):
        return "AnnotationMisuse"
    if isinstance(sub, WordJoinerInjection):
        return "WordJoinerInjection"
    if isinstance(sub, AiWatermarkNNBSP):
        return "AiWatermarkNNBSP"
    if isinstance(sub, BinaryPayload):
        return "BinaryPayload"
    return "BareZeroWidth"


@dataclass(slots=True)
class Verdict:
    kind: ClassificationKind
    sub: SubThreat | None = None
    zero_width_positions: list[int] = field(default_factory=list)


def detect(input_cps: list[int]) -> Verdict:
    v = Verdict(kind=ClassificationKind.CLEAR)
    annotation_count = 0
    word_joiner_count = 0
    nnbsp_count = 0
    zwj_zwsp_count = 0

    for i, cp in enumerate(input_cps):
        if not is_zero_width(cp):
            continue
        v.zero_width_positions.append(i)
        if is_annotation(cp):
            annotation_count += 1
        elif is_word_joiner(cp):
            word_joiner_count += 1
        elif is_nnbsp(cp):
            nnbsp_count += 1
        elif is_zwj_or_zwsp(cp):
            zwj_zwsp_count += 1

    if not v.zero_width_positions:
        return v

    v.kind = ClassificationKind.HAZARD
    if annotation_count > 0:
        v.sub = AnnotationMisuse(count=annotation_count)
    elif word_joiner_count > 0:
        v.sub = WordJoinerInjection(count=word_joiner_count)
    elif nnbsp_count >= 2:
        v.sub = AiWatermarkNNBSP(count=nnbsp_count)
    elif zwj_zwsp_count >= 2:
        v.sub = BinaryPayload(pair_count=zwj_zwsp_count // 2)
    else:
        v.sub = BareZeroWidth(cp=input_cps[v.zero_width_positions[0]])
    return v


__all__ = [
    "AiWatermarkNNBSP",
    "AnnotationMisuse",
    "BareZeroWidth",
    "BinaryPayload",
    "SubThreat",
    "Verdict",
    "WordJoinerInjection",
    "detect",
    "is_annotation",
    "is_nnbsp",
    "is_word_joiner",
    "is_zero_width",
    "is_zwj_or_zwsp",
    "sub_threat_tag",
]
