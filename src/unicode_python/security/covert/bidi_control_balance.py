"""Detection of Trojan-Source-class bidi-control balance hazards
(CVE-2021-42574 / CVE-2021-42694).

Threat model.  Tier A1.  Adversary embeds Unicode bidi format-
control characters (LRE / RLE / LRO / RLO / PDF / LRI / RLI /
FSI / PDI) inside source code or identifier-bearing text to
reorder the visible glyph stream away from the byte order that
compilers and runtime tokenizers see.

Detection walks the input with a per-type stack and produces
four independent sub-threats:

    * DepthExceeded        — nesting > 125 (UAX #9 §3.3.2 cap)
    * OrphanPop            — PDF or PDI with no matching opener
    * UnbalancedEmbedding  — LRE/RLE/LRO opens unclosed at end
    * UnbalancedIsolate    — LRI/RLI/FSI opens unclosed at end

An input that has bidi controls but is properly balanced and
within depth produces a ``CLEAR`` verdict — legitimate inline-
Arabic or inline-Hebrew text.
"""

from dataclasses import dataclass, field
from typing import Union

from ..calculus import ClassificationKind


UAX_DEPTH_LIMIT = 125


def opens_embedding(cp: int) -> bool:
    # LRE (202A), RLE (202B), LRO (202D), RLO (202E).
    return cp in (0x202A, 0x202B, 0x202D, 0x202E)


def is_pdf(cp: int) -> bool:
    return cp == 0x202C


def opens_isolate(cp: int) -> bool:
    # LRI (2066), RLI (2067), FSI (2068).
    return cp in (0x2066, 0x2067, 0x2068)


def is_pdi(cp: int) -> bool:
    return cp == 0x2069


def is_bidi_format_control(cp: int) -> bool:
    return (
        opens_embedding(cp)
        or is_pdf(cp)
        or opens_isolate(cp)
        or is_pdi(cp)
    )


@dataclass(frozen=True, slots=True)
class DepthExceeded:
    max_depth: int


@dataclass(frozen=True, slots=True)
class OrphanPop:
    positions: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class UnbalancedEmbedding:
    open_count: int
    pop_count: int


@dataclass(frozen=True, slots=True)
class UnbalancedIsolate:
    open_count: int
    pop_count: int


SubThreat = Union[DepthExceeded, OrphanPop, UnbalancedEmbedding, UnbalancedIsolate]


def sub_threat_tag(sub: SubThreat) -> str:
    if isinstance(sub, DepthExceeded):
        return "DepthExceeded"
    if isinstance(sub, OrphanPop):
        return "OrphanPop"
    if isinstance(sub, UnbalancedEmbedding):
        return "UnbalancedEmbedding"
    return "UnbalancedIsolate"


@dataclass(slots=True)
class Verdict:
    kind: ClassificationKind
    sub: SubThreat | None = None
    bidi_positions: list[int] = field(default_factory=list)
    emb_open_count: int = 0
    emb_pop_count: int = 0
    iso_open_count: int = 0
    iso_pop_count: int = 0
    max_depth: int = 0


def detect(input_cps: list[int]) -> Verdict:
    v = Verdict(kind=ClassificationKind.CLEAR)
    emb_stack = 0
    iso_stack = 0
    orphans: list[int] = []

    for i, cp in enumerate(input_cps):
        if not is_bidi_format_control(cp):
            continue
        v.bidi_positions.append(i)
        if opens_embedding(cp):
            emb_stack += 1
            v.emb_open_count += 1
            v.max_depth = max(v.max_depth, emb_stack + iso_stack)
        elif is_pdf(cp):
            v.emb_pop_count += 1
            if emb_stack > 0:
                emb_stack -= 1
            else:
                orphans.append(i)
        elif opens_isolate(cp):
            iso_stack += 1
            v.iso_open_count += 1
            v.max_depth = max(v.max_depth, emb_stack + iso_stack)
        elif is_pdi(cp):
            v.iso_pop_count += 1
            if iso_stack > 0:
                iso_stack -= 1
            else:
                orphans.append(i)

    if not v.bidi_positions:
        return v

    if v.max_depth > UAX_DEPTH_LIMIT:
        v.kind = ClassificationKind.HAZARD
        v.sub = DepthExceeded(max_depth=v.max_depth)
        return v
    if orphans:
        v.kind = ClassificationKind.HAZARD
        v.sub = OrphanPop(positions=tuple(orphans))
        return v
    if emb_stack > 0:
        v.kind = ClassificationKind.HAZARD
        v.sub = UnbalancedEmbedding(
            open_count=v.emb_open_count, pop_count=v.emb_pop_count,
        )
        return v
    if iso_stack > 0:
        v.kind = ClassificationKind.HAZARD
        v.sub = UnbalancedIsolate(
            open_count=v.iso_open_count, pop_count=v.iso_pop_count,
        )
        return v
    # Bidi controls present and balanced.
    return v


__all__ = [
    "DepthExceeded",
    "OrphanPop",
    "SubThreat",
    "UAX_DEPTH_LIMIT",
    "UnbalancedEmbedding",
    "UnbalancedIsolate",
    "Verdict",
    "detect",
    "is_bidi_format_control",
    "is_pdf",
    "is_pdi",
    "opens_embedding",
    "opens_isolate",
    "sub_threat_tag",
]
