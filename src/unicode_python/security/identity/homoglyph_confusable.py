"""Detection of homoglyph / confusable identifier substitution attacks.

Threat model.  Tier A1..A3 (local injector through supply-chain
injector).  An adversary registers a package, identifier, or
domain whose visible glyph stream is indistinguishable from a
canonical target's, but whose byte stream differs at one or more
positions (Cyrillic 'е' posed as Latin 'e', Mathematical Bold 'A'
posed as plain 'A', Fullwidth 'Ａ' posed as 'A').  The motivating
real-world instance is the October 2025 Nethereum NuGet supply-
chain campaign — twelve packages whose names differed from
canonical Web3 / Solana toolchain names by a single Cyrillic
codepoint substitution.

Detection strategy.  Project the input and a curated catalogue of
canonical targets through the UTS #39 §4 confusable-skeleton
mapping, iterate to a fixed point, and test equality.  Hazard
when the input's iterated skeleton matches a target's iterated
skeleton while the literal codepoint sequences differ.  Layered
with two range-based predicates:

  - Mathematical Alphanumeric Symbols (U+1D400..U+1D7FF) —
    Mathematical Bold / Italic / Fraktur / Script / Sans-Serif /
    Double-Struck Latin and digit letters that render as their
    plain-ASCII counterparts.
  - Halfwidth and Fullwidth Forms (U+FF01..U+FFEF) — fullwidth
    Latin variants that render at full character-cell width.

Six sub-threats are evaluated in fixed priority order
(highest first):

  - ``TargetMatch``        — input's iterated skeleton matches a
    canonical target's iterated skeleton.
  - ``MathAlpha``          — input contains Mathematical
    Alphanumeric Symbols.
  - ``WidthClass``         — input contains fullwidth / halfwidth
    ASCII variants.
  - ``DecompositionSwap``  — input is not in NFC; ``to_nfc(input)``
    differs at one or more positions.
  - ``CrossScriptMix``     — input mixes two or more non-Common,
    non-Inherited scripts and is not Highly Restrictive.
  - ``RestrictionLow``     — input's UTS #39 § 5.1 restriction
    level is Minimally Restrictive or Unrestricted.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Union

from ..calculus import ClassificationKind
from . import ucd
from .ucd import RestrictionLevel

# ─────────────────────────────────────────────────────────────────────
# Data loading
# ─────────────────────────────────────────────────────────────────────

_DATA_DIR = Path(__file__).resolve().parent.parent.parent / "data"


def _load_confusables() -> dict[int, list[int]]:
    """Parse confusables.txt into a source-codepoint → skeleton map."""
    path = _DATA_DIR / "confusables.txt"
    out: dict[int, list[int]] = {}
    with path.open("r", encoding="utf-8") as f:
        for raw_line in f:
            stripped = raw_line.split("#", 1)[0].strip()
            if not stripped:
                continue
            parts = stripped.split(";")
            if len(parts) < 2:
                continue
            src_field = parts[0].strip()
            tgt_field = parts[1].strip()
            try:
                src = int(src_field, 16)
            except ValueError:
                continue
            tgt: list[int] = []
            for hex_token in tgt_field.split():
                try:
                    tgt.append(int(hex_token, 16))
                except ValueError as err:
                    raise ValueError(
                        f"confusables.txt: malformed target codepoint "
                        f"{hex_token!r} for source U+{src:04X}"
                    ) from err
            if not tgt:
                continue
            out[src] = tgt
    return out


def _load_known_attack_targets() -> list[str]:
    """Parse the curated attack-target list into a list of names."""
    path = _DATA_DIR / "KnownAttackTargets.txt"
    out: list[str] = []
    with path.open("r", encoding="utf-8") as f:
        for raw_line in f:
            trimmed = raw_line.strip()
            if not trimmed or trimmed.startswith("#"):
                continue
            out.append(trimmed)
    return out


_CONFUSABLES_MAP: dict[int, list[int]] | None = None
_KNOWN_ATTACK_TARGETS: list[str] | None = None


def confusables_map() -> dict[int, list[int]]:
    """Return the parsed confusables map (cached after first call)."""
    global _CONFUSABLES_MAP
    if _CONFUSABLES_MAP is None:
        _CONFUSABLES_MAP = _load_confusables()
    return _CONFUSABLES_MAP


def known_attack_targets() -> list[str]:
    """Return the parsed attack-target list (cached after first call)."""
    global _KNOWN_ATTACK_TARGETS
    if _KNOWN_ATTACK_TARGETS is None:
        _KNOWN_ATTACK_TARGETS = _load_known_attack_targets()
    return _KNOWN_ATTACK_TARGETS


# ─────────────────────────────────────────────────────────────────────
# Skeleton machinery
# ─────────────────────────────────────────────────────────────────────


def _substitute(input_cps: list[int]) -> list[int]:
    """Inner substitution step of the UTS #39 skeleton — replaces
    each codepoint by its confusables target sequence (codepoints
    absent from the table are kept).  Not the full skeleton; the
    case-folded NFD bracket is applied by ``skeleton``."""
    cmap = confusables_map()
    out: list[int] = []
    for cp in input_cps:
        replacement = cmap.get(cp)
        if replacement is None:
            out.append(cp)
        else:
            out.extend(replacement)
    return out


def skeleton(input_cps: list[int]) -> list[int]:
    """The case-insensitive confusables skeleton per UTS #39 §4 + §5.4:

        skeleton(X) = toNFD(caseFold(substitute(caseFold(toNFD(X)))))

    Bracketing case folding inside the NFD passes lets the detector
    collapse case-variant typosquats on case-insensitive registries
    (npm / PyPI / NuGet package IDs, IDN labels) to a single canonical
    representative.  Mirrors the Lean ``Unicode.Confusables.skeleton``
    definition.
    """
    step1 = ucd.to_nfd(input_cps)
    step2 = ucd.case_fold(step1)
    step3 = _substitute(step2)
    step4 = ucd.case_fold(step3)
    return ucd.to_nfd(step4)


def iterated_skeleton(input_cps: list[int]) -> list[int]:
    """Apply ``skeleton`` until a fixed point.

    In practice 1–3 iterations suffice for every published
    confusable chain.
    """
    current = list(input_cps)
    while True:
        nxt = skeleton(current)
        if nxt == current:
            return current
        current = nxt


def letter_skeleton(input_cps: list[int]) -> list[int]:
    """Stricter "letter" skeleton — ``iterated_skeleton`` followed by
    removal of (a) every codepoint with ``canonicalCombiningClass > 0``,
    (b) every codepoint with the ``Default_Ignorable_Code_Point``
    derived property, AND (c) every whitespace codepoint.

    Catches three adjacent classes of typosquat attack:
      (1) base-letter+combining-mark confusables (U+0247 ɇ → e + ◌̸)
      (2) cascading-substitute confusables (U+2133 ℳ via M → m → rn)
      (3) invisible-codepoint insertion (ZWSP / ZWNJ / ZWJ / WJ /
          BOM / NNBSP / soft hyphen / bidi controls / Mongolian /
          variation selectors / tag block)

    Mirrors the Lean ``Unicode.Confusables.letterSkeleton``.
    """
    return [
        cp
        for cp in iterated_skeleton(input_cps)
        if ucd.ccc(cp) == 0
        and not ucd.is_default_ignorable(cp)
        and not ucd.is_white_space(cp)
    ]


# ─────────────────────────────────────────────────────────────────────
# Range predicates
# ─────────────────────────────────────────────────────────────────────


def is_math_alphanumeric(cp: int) -> bool:
    """U+1D400..U+1D7FF — Mathematical Alphanumeric Symbols block."""
    return 0x1D400 <= cp <= 0x1D7FF


def is_fullwidth_halfwidth(cp: int) -> bool:
    """U+FF01..U+FFEF — Halfwidth and Fullwidth Forms block."""
    return 0xFF01 <= cp <= 0xFFEF


# ─────────────────────────────────────────────────────────────────────
# Sub-threat ADT + verdict
# ─────────────────────────────────────────────────────────────────────


@dataclass(frozen=True, slots=True)
class TargetMatch:
    target: str


@dataclass(frozen=True, slots=True)
class MathAlpha:
    first_cp: int
    count: int


@dataclass(frozen=True, slots=True)
class WidthClass:
    first_cp: int
    count: int


@dataclass(frozen=True, slots=True)
class DecompositionSwap:
    first_diff_pos: int


@dataclass(frozen=True, slots=True)
class CrossScriptMix:
    script_count: int


@dataclass(frozen=True, slots=True)
class RestrictionLow:
    level: RestrictionLevel


SubThreat = Union[
    TargetMatch,
    MathAlpha,
    WidthClass,
    DecompositionSwap,
    CrossScriptMix,
    RestrictionLow,
]


def sub_threat_tag(sub: SubThreat) -> str:
    if isinstance(sub, TargetMatch):
        return "TargetMatch"
    if isinstance(sub, MathAlpha):
        return "MathAlpha"
    if isinstance(sub, WidthClass):
        return "WidthClass"
    if isinstance(sub, DecompositionSwap):
        return "DecompositionSwap"
    if isinstance(sub, CrossScriptMix):
        return "CrossScriptMix"
    if isinstance(sub, RestrictionLow):
        return "RestrictionLow"
    raise TypeError(f"sub_threat_tag: unknown SubThreat variant {sub!r}")


@dataclass(frozen=True, slots=True)
class Verdict:
    kind: ClassificationKind
    sub: SubThreat | None
    skeleton: list[int]
    iterated_skeleton: list[int]
    restriction_level: RestrictionLevel
    matched_targets: list[str] = field(default_factory=list)


# ─────────────────────────────────────────────────────────────────────
# Detection
# ─────────────────────────────────────────────────────────────────────


def _ascii_codepoints(s: str) -> list[int]:
    return [ord(c) for c in s]


def _ct_slice_eq(a: list[int], b: list[int]) -> int:
    """Constant-time int-list equality.  Returns 1 if equal, 0 if
    not.  No early break on first inequality (when lengths match).
    Length-dependent branch is permitted because target names are
    public and input length is observable from the API.

    Used by `_find_target_match` to eliminate the timing side
    channel that would let an attacker fingerprint the curated
    target list by observing detector latency.
    """
    if len(a) != len(b):
        return 0
    acc = 0
    for x, y in zip(a, b):
        acc |= x ^ y
    # acc == 0 iff all elements equal — collapse to 0/1 without
    # a comparison branch.  Mask to 32 bits since we accumulate
    # u32 codepoints; Python ints are bignum but the relevant
    # bits are confined.
    z = acc & 0xFFFFFFFF
    z |= z >> 16
    z |= z >> 8
    z |= z >> 4
    z |= z >> 2
    z |= z >> 1
    return 1 - (z & 1)


def _find_target_match(
    input_cps: list[int], _iterated: list[int]
) -> str | None:
    """Constant-time variant of target match (Move 4 of state-level
    red-team plan).  Walks the entire curated target list every
    call; captures FIRST matching index but continues iterating to
    completion.  letter_skeleton handles combining-mark + cascading-
    substitute confusables (Hole 4) and Default_Ignorable + White_Space
    invisible insertion (Hole 5).
    """
    input_letters = letter_skeleton(input_cps)
    targets = known_attack_targets()
    first_match: int | None = None
    for idx, target in enumerate(targets):
        t_cps = _ascii_codepoints(target)
        if t_cps == input_cps:
            # Self-match guard — input is literally the target.
            continue
        t_letters = letter_skeleton(t_cps)
        is_match = _ct_slice_eq(t_letters, input_letters) == 1
        # Capture first match index but do NOT break — keep loop
        # work independent of which target (if any) fires.
        if is_match and first_match is None:
            first_match = idx
    if first_match is None:
        return None
    return targets[first_match]


def _first_decomposition_diff_pos(
    input_cps: list[int], nfc: list[int]
) -> int:
    """Precondition: ``input_cps != nfc``.  Returns the first
    codepoint position at which the two sequences disagree, or
    the length of the shorter sequence when the difference is a
    tail-only extension."""
    shorter = min(len(input_cps), len(nfc))
    for i in range(shorter):
        if input_cps[i] != nfc[i]:
            return i
    return shorter


def detect(input_cps: list[int]) -> Verdict:
    """Run the HomoglyphConfusable detector over a codepoint sequence."""
    skel = skeleton(input_cps)
    iskel = iterated_skeleton(input_cps)
    rl = ucd.restriction_level(input_cps)

    # Priority 1: target match.
    target = _find_target_match(input_cps, iskel)
    if target is not None:
        return Verdict(
            kind=ClassificationKind.HAZARD,
            sub=TargetMatch(target=target),
            skeleton=skel,
            iterated_skeleton=iskel,
            restriction_level=rl,
            matched_targets=[target],
        )

    # Priority 2: Math Alphanumeric.
    math_positions = [cp for cp in input_cps if is_math_alphanumeric(cp)]
    if math_positions:
        return Verdict(
            kind=ClassificationKind.HAZARD,
            sub=MathAlpha(
                first_cp=math_positions[0], count=len(math_positions)
            ),
            skeleton=skel,
            iterated_skeleton=iskel,
            restriction_level=rl,
        )

    # Priority 3: Fullwidth/Halfwidth.
    fw_positions = [cp for cp in input_cps if is_fullwidth_halfwidth(cp)]
    if fw_positions:
        return Verdict(
            kind=ClassificationKind.HAZARD,
            sub=WidthClass(
                first_cp=fw_positions[0], count=len(fw_positions)
            ),
            skeleton=skel,
            iterated_skeleton=iskel,
            restriction_level=rl,
        )

    # Priority 4: DecompositionSwap.
    nfc = ucd.to_nfc(input_cps)
    if nfc != input_cps:
        return Verdict(
            kind=ClassificationKind.HAZARD,
            sub=DecompositionSwap(
                first_diff_pos=_first_decomposition_diff_pos(input_cps, nfc)
            ),
            skeleton=skel,
            iterated_skeleton=iskel,
            restriction_level=rl,
        )

    # Priority 5: CrossScriptMix.
    union = ucd.string_script_union(input_cps)
    if len(union) >= 2 and not ucd.is_highly_restrictive(input_cps):
        return Verdict(
            kind=ClassificationKind.HAZARD,
            sub=CrossScriptMix(script_count=len(union)),
            skeleton=skel,
            iterated_skeleton=iskel,
            restriction_level=rl,
        )

    # Priority 6: RestrictionLow.
    if rl in (
        RestrictionLevel.MINIMALLY_RESTRICTIVE,
        RestrictionLevel.UNRESTRICTED,
    ):
        return Verdict(
            kind=ClassificationKind.HAZARD,
            sub=RestrictionLow(level=rl),
            skeleton=skel,
            iterated_skeleton=iskel,
            restriction_level=rl,
        )

    return Verdict(
        kind=ClassificationKind.CLEAR,
        sub=None,
        skeleton=skel,
        iterated_skeleton=iskel,
        restriction_level=rl,
    )
