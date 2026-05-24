"""Detection of GlassWorm-class invisible payloads encoded in
Unicode variation selectors.

Threat model.  Tier A1.  Adversary crafts an input consisting of
one visible base codepoint followed by a sequence of variation-
selector codepoints (U+FE00..U+FE0F union U+E0100..U+E01EF) that
the receiving renderer treats as a no-op glyph variant but that
a downstream string-processing layer (e.g. an LLM tokenizer or a
clipboard pipeline) preserves byte-for-byte.  Decoding pairs of
VS codepoints back into bytes recovers an arbitrary payload.

This port treats every variation-selector occurrence after a base
codepoint as suspicious.  The Lean reference additionally exempts
(base, VS) pairs that appear in StandardizedVariants.txt and
emoji-presentation pairs — those exemptions require UCD tables.
The coarser port is more conservative: legitimate math / Mongolian
/ Egyptian / CJK Compat / emoji-presentation VS uses will be
flagged.
"""

from dataclasses import dataclass, field
from pathlib import Path
from typing import Union

from ..calculus import ClassificationKind

# ──────────────────────────────────────────────────────────────────────
# Authoritative legal (base, VS) pair set — UCD StandardizedVariants
# + UTS #51 emoji-variation-sequences.  Loaded lazily on first use.
# ──────────────────────────────────────────────────────────────────────

_DATA_DIR = Path(__file__).resolve().parent.parent.parent / "data"


def _parse_legal_variation_pairs() -> set[tuple[int, int]]:
    out: set[tuple[int, int]] = set()
    for fname in (
        "StandardizedVariants.txt",
        "emoji-variation-sequences.txt",
    ):
        path = _DATA_DIR / fname
        with path.open("r", encoding="utf-8") as f:
            for raw_line in f:
                # Strip comment then take up to first ';'.
                hash_idx = raw_line.find("#")
                body = raw_line if hash_idx < 0 else raw_line[:hash_idx]
                semi_idx = body.find(";")
                pair_part = body if semi_idx < 0 else body[:semi_idx]
                tokens = pair_part.split()
                if len(tokens) < 2:
                    continue
                try:
                    base = int(tokens[0], 16)
                    vs = int(tokens[1], 16)
                except ValueError:
                    continue
                out.add((base, vs))
    return out


_LEGAL_PAIRS: set[tuple[int, int]] | None = None


def is_registered_variation_pair(base: int, vs: int) -> bool:
    """True iff ``(base, vs)`` is a registered variation sequence
    per UCD StandardizedVariants.txt or UTS #51
    emoji-variation-sequences.txt.  Used to exempt legitimate
    math / emoji-presentation variants from IllegalTarget
    false-positives."""
    global _LEGAL_PAIRS
    if _LEGAL_PAIRS is None:
        _LEGAL_PAIRS = _parse_legal_variation_pairs()
    return (base, vs) in _LEGAL_PAIRS


def is_variation_selector(cp: int) -> bool:
    if 0xFE00 <= cp <= 0xFE0F:
        return True
    if 0xE0100 <= cp <= 0xE01EF:
        return True
    if 0x180B <= cp <= 0x180D:
        return True
    return False


def vs_to_nibble(cp: int) -> int | None:
    """Decode a single VS codepoint to its nibble value in [0, 255].
    Uses GlassWorm's bit layout: VS1..VS16 → nibbles 0..15,
    VS17..VS256 → nibbles 16..255.  Mongolian FVS codepoints
    (180B..180D) return ``None``."""
    if 0xFE00 <= cp <= 0xFE0F:
        return cp - 0xFE00
    if 0xE0100 <= cp <= 0xE01EF:
        return cp - 0xE0100 + 16
    return None


@dataclass(frozen=True, slots=True)
class DirectPayload:
    decoded: str


@dataclass(frozen=True, slots=True)
class IllegalTarget:
    target_cp: int
    vs_cp: int


@dataclass(frozen=True, slots=True)
class RepeatedBase:
    base_cp: int
    vs_count: int


SubThreat = Union[DirectPayload, IllegalTarget, RepeatedBase]


def sub_threat_tag(sub: SubThreat) -> str:
    if isinstance(sub, DirectPayload):
        return "DirectPayload"
    if isinstance(sub, IllegalTarget):
        return "IllegalTarget"
    return "RepeatedBase"


@dataclass(slots=True)
class Verdict:
    kind: ClassificationKind
    sub: SubThreat | None = None
    vs_positions: list[int] = field(default_factory=list)
    recovered_bytes: bytes = b""


def _decode_vs_run(input_cps: list[int], positions: list[int]) -> bytes:
    out = bytearray()
    high: int | None = None
    for p in positions:
        n = vs_to_nibble(input_cps[p])
        if n is None:
            continue
        if high is None:
            high = n
        else:
            out.append(((high << 4) | n) & 0xFF)
            high = None
    return bytes(out)


def _all_same_vs(input_cps: list[int], positions: list[int]) -> bool:
    if not positions:
        return True
    cp0 = input_cps[positions[0]]
    return all(input_cps[p] == cp0 for p in positions)


def _lossy_ascii(payload: bytes) -> str:
    out = []
    for b in payload:
        if (0x20 <= b <= 0x7E) or b in (0x09, 0x0A, 0x0D):
            out.append(chr(b))
        else:
            out.append("?")
    return "".join(out)


def detect(input_cps: list[int]) -> Verdict:
    v = Verdict(kind=ClassificationKind.CLEAR)
    v.vs_positions = [i for i, cp in enumerate(input_cps) if is_variation_selector(cp)]
    if not v.vs_positions:
        return v

    v.recovered_bytes = _decode_vs_run(input_cps, v.vs_positions)

    # Single-VS exemption: if exactly one VS follows a base AND the
    # (base, VS) pair is registered in StandardizedVariants or
    # emoji-variation-sequences, return Clear (legitimate variant).
    if len(v.vs_positions) == 1:
        p = v.vs_positions[0]
        if p > 0:
            base = input_cps[p - 1]
            vs = input_cps[p]
            if is_registered_variation_pair(base, vs):
                return v  # Clear — registered variant

    v.kind = ClassificationKind.HAZARD

    if len(v.vs_positions) >= 4 and _all_same_vs(input_cps, v.vs_positions):
        p0 = v.vs_positions[0]
        base = 0 if p0 == 0 else input_cps[p0 - 1]
        v.sub = RepeatedBase(base_cp=base, vs_count=len(v.vs_positions))
    elif v.recovered_bytes:
        v.sub = DirectPayload(decoded=_lossy_ascii(v.recovered_bytes))
    else:
        p = v.vs_positions[0]
        target = 0 if p == 0 else input_cps[p - 1]
        v.sub = IllegalTarget(target_cp=target, vs_cp=input_cps[p])
    return v


__all__ = [
    "DirectPayload",
    "IllegalTarget",
    "RepeatedBase",
    "SubThreat",
    "Verdict",
    "detect",
    "is_variation_selector",
    "sub_threat_tag",
    "vs_to_nibble",
]
