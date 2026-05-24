"""UCD-table-backed support module for the identity-spoofing
detector family — NFC normalization, script lookup, UTS #39
identifier-status / restriction-level classification.

All data is loaded once on first access from the bundled UCD
files under ``src/unicode_python/data/``.  No catchall fallback:
parser failures raise rather than silently falling through, and
the spec's ``@missing`` defaults (e.g. CCC = 0 for unlisted
codepoints, UAX #44 §5.7.4) are written as explicit
``None``-branch returns rather than ``.get(..., default)``.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from pathlib import Path

# ─────────────────────────────────────────────────────────────────────
# Bundled-data location
# ─────────────────────────────────────────────────────────────────────

_DATA_DIR = Path(__file__).resolve().parent.parent.parent / "data"


def _read_data_file(name: str) -> str:
    with (_DATA_DIR / name).open("r", encoding="utf-8") as f:
        return f.read()


def _strip_comment_and_trim(line: str) -> str:
    """Return the portion of ``line`` before the first ``#`` (or
    the whole line if absent), with leading and trailing ASCII
    whitespace removed."""
    hash_idx = line.find("#")
    body = line if hash_idx < 0 else line[:hash_idx]
    return body.strip()


def _parse_hex(s: str) -> int:
    return int(s.strip(), 16)


def _parse_range_field(s: str) -> tuple[int, int]:
    """Parse a ``<hex>`` or ``<hex>..<hex>`` UCD range field."""
    s = s.strip()
    dots = s.find("..")
    if dots < 0:
        cp = _parse_hex(s)
        return (cp, cp)
    return (_parse_hex(s[:dots]), _parse_hex(s[dots + 2 :]))


# ─────────────────────────────────────────────────────────────────────
# UnicodeData.txt — CCC + canonical decomposition
# ─────────────────────────────────────────────────────────────────────


@dataclass(frozen=True, slots=True)
class UcdEntry:
    ccc: int
    canonical_decomp: tuple[int, ...] | None


def _parse_unicode_data() -> dict[int, UcdEntry]:
    text = _read_data_file("UnicodeData.txt")
    out: dict[int, UcdEntry] = {}
    for line in text.splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split(";")
        if len(fields) < 6:
            continue
        cp = _parse_hex(fields[0])
        ccc_field = fields[3].strip()
        try:
            ccc = int(ccc_field)
        except ValueError as err:
            raise ValueError(
                f"UnicodeData.txt: CCC field {ccc_field!r} for "
                f"U+{cp:04X} is not an integer"
            ) from err
        decomp_field = fields[5].strip()
        if not decomp_field:
            canonical_decomp: tuple[int, ...] | None = None
        elif decomp_field.startswith("<"):
            # Compatibility decomposition — skip for NFC.
            canonical_decomp = None
        else:
            canonical_decomp = tuple(
                _parse_hex(tok) for tok in decomp_field.split()
            )
            if not canonical_decomp:
                canonical_decomp = None
        out[cp] = UcdEntry(ccc=ccc, canonical_decomp=canonical_decomp)
    return out


_UCD_TABLE: dict[int, UcdEntry] | None = None


def ucd_table() -> dict[int, UcdEntry]:
    global _UCD_TABLE
    if _UCD_TABLE is None:
        _UCD_TABLE = _parse_unicode_data()
    return _UCD_TABLE


def ccc(cp: int) -> int:
    """Canonical Combining Class of ``cp``.

    UAX #44 § 5.7.4 specifies CCC = 0 (Not_Reordered) as the
    ``@missing`` default for codepoints absent from the listed
    ranges — the ``None`` branch below encodes that spec default
    explicitly, not a fallback for unrecognised input.
    """
    entry = ucd_table().get(cp)
    if entry is None:
        return 0
    return entry.ccc


# ─────────────────────────────────────────────────────────────────────
# CompositionExclusions.txt — codepoints that must not recompose
# ─────────────────────────────────────────────────────────────────────


def _parse_composition_exclusions() -> set[int]:
    text = _read_data_file("CompositionExclusions.txt")
    out: set[int] = set()
    for line in text.splitlines():
        stripped = _strip_comment_and_trim(line)
        if not stripped:
            continue
        out.add(_parse_hex(stripped))
    return out


_EXCLUSIONS: set[int] | None = None


def composition_exclusions() -> set[int]:
    global _EXCLUSIONS
    if _EXCLUSIONS is None:
        _EXCLUSIONS = _parse_composition_exclusions()
    return _EXCLUSIONS


# ─────────────────────────────────────────────────────────────────────
# Composition table — inverse of canonical decomposition minus
# CompositionExclusions and non-starter-led decompositions.
# ─────────────────────────────────────────────────────────────────────


def _build_composition_table() -> dict[tuple[int, int], int]:
    table = ucd_table()
    exclusions = composition_exclusions()
    out: dict[tuple[int, int], int] = {}
    for cp, entry in table.items():
        decomp = entry.canonical_decomp
        if decomp is None or len(decomp) != 2:
            continue
        if cp in exclusions:
            continue
        a, b = decomp
        if ccc(a) != 0:
            continue
        out[(a, b)] = cp
    return out


_COMP_TABLE: dict[tuple[int, int], int] | None = None


def composition_table() -> dict[tuple[int, int], int]:
    global _COMP_TABLE
    if _COMP_TABLE is None:
        _COMP_TABLE = _build_composition_table()
    return _COMP_TABLE


# ─────────────────────────────────────────────────────────────────────
# Hangul algorithmic decomposition + composition (UAX #15 §1.3)
# ─────────────────────────────────────────────────────────────────────

HANGUL_S_BASE = 0xAC00
HANGUL_L_BASE = 0x1100
HANGUL_V_BASE = 0x1161
HANGUL_T_BASE = 0x11A7
HANGUL_L_COUNT = 19
HANGUL_V_COUNT = 21
HANGUL_T_COUNT = 28
HANGUL_N_COUNT = HANGUL_V_COUNT * HANGUL_T_COUNT
HANGUL_S_COUNT = HANGUL_L_COUNT * HANGUL_N_COUNT


def _hangul_decompose(cp: int, out: list[int]) -> bool:
    if not (HANGUL_S_BASE <= cp < HANGUL_S_BASE + HANGUL_S_COUNT):
        return False
    s_index = cp - HANGUL_S_BASE
    l = HANGUL_L_BASE + s_index // HANGUL_N_COUNT
    v = HANGUL_V_BASE + (s_index % HANGUL_N_COUNT) // HANGUL_T_COUNT
    t_index = s_index % HANGUL_T_COUNT
    out.append(l)
    out.append(v)
    if t_index != 0:
        out.append(HANGUL_T_BASE + t_index)
    return True


def _hangul_compose(a: int, b: int) -> int | None:
    if (
        HANGUL_L_BASE <= a < HANGUL_L_BASE + HANGUL_L_COUNT
        and HANGUL_V_BASE <= b < HANGUL_V_BASE + HANGUL_V_COUNT
    ):
        l_index = a - HANGUL_L_BASE
        v_index = b - HANGUL_V_BASE
        return HANGUL_S_BASE + (
            l_index * HANGUL_V_COUNT + v_index
        ) * HANGUL_T_COUNT
    if (
        HANGUL_S_BASE <= a < HANGUL_S_BASE + HANGUL_S_COUNT
        and (a - HANGUL_S_BASE) % HANGUL_T_COUNT == 0
        and HANGUL_T_BASE + 1 <= b < HANGUL_T_BASE + HANGUL_T_COUNT
    ):
        return a + (b - HANGUL_T_BASE)
    return None


# ─────────────────────────────────────────────────────────────────────
# NFC pipeline: canonical decompose → canonical reorder → compose
# ─────────────────────────────────────────────────────────────────────


def _decompose_one(cp: int, out: list[int]) -> None:
    if _hangul_decompose(cp, out):
        return
    entry = ucd_table().get(cp)
    if entry is not None and entry.canonical_decomp is not None:
        for child in entry.canonical_decomp:
            _decompose_one(child, out)
        return
    out.append(cp)


def _canonical_decompose(input_cps: list[int]) -> list[int]:
    out: list[int] = []
    for cp in input_cps:
        _decompose_one(cp, out)
    return out


def _canonical_reorder(seq: list[int]) -> None:
    """Stable-sort each non-starter run (CCC ≠ 0) by CCC in place."""
    n = len(seq)
    i = 0
    while i < n:
        if ccc(seq[i]) == 0:
            i += 1
            continue
        j = i
        while j < n and ccc(seq[j]) != 0:
            j += 1
        run = seq[i:j]
        run.sort(key=ccc)
        seq[i:j] = run
        i = j


def _canonical_compose(seq: list[int]) -> list[int]:
    if not seq:
        return []
    comp = composition_table()
    out: list[int] = []
    starter_idx: int | None = None
    last_ccc: int = -1
    for cp in seq:
        cp_ccc = ccc(cp)
        if starter_idx is not None:
            starter = out[starter_idx]
            composed = _hangul_compose(starter, cp)
            if composed is None:
                composed = comp.get((starter, cp))
            blocked = (
                cp_ccc != 0 and last_ccc != 0 and last_ccc >= cp_ccc
            )
            if not blocked and composed is not None:
                out[starter_idx] = composed
                continue
        out.append(cp)
        if cp_ccc == 0:
            starter_idx = len(out) - 1
            last_ccc = 0
        else:
            last_ccc = cp_ccc
    return out


def to_nfc(input_cps: list[int]) -> list[int]:
    """The full UAX #15 NFC pipeline applied to a codepoint sequence."""
    decomposed = _canonical_decompose(input_cps)
    _canonical_reorder(decomposed)
    return _canonical_compose(decomposed)


def to_nfd(input_cps: list[int]) -> list[int]:
    """UAX #15 NFD — canonical decompose + canonical reorder, without
    the recomposition pass.  Required by the UTS #39 §4 + §5.4
    confusable-skeleton bracket."""
    decomposed = _canonical_decompose(input_cps)
    _canonical_reorder(decomposed)
    return decomposed


# ─────────────────────────────────────────────────────────────────────
# CaseFolding.txt — default full case folding (RFC 8265 § 5.2.4)
# ─────────────────────────────────────────────────────────────────────


def _parse_case_folding() -> dict[int, list[int]]:
    text = _read_data_file("CaseFolding.txt")
    out: dict[int, list[int]] = {}
    for line in text.splitlines():
        stripped = _strip_comment_and_trim(line)
        if not stripped:
            continue
        parts = [p.strip() for p in stripped.split(";")]
        if len(parts) < 3:
            continue
        status = parts[1]
        # Keep only status C (Common) and F (Full) entries — the
        # union RFC 8265 §5.2.4 calls "default full case folding".
        # Status S (Simple) is redundant with C/F; status T is
        # Turkic-locale-specific.
        if status not in ("C", "F"):
            continue
        src = _parse_hex(parts[0])
        tgt = [_parse_hex(t) for t in parts[2].split() if t]
        if not tgt:
            continue
        out[src] = tgt
    return out


_CASE_FOLDING: dict[int, list[int]] | None = None


def case_folding_table() -> dict[int, list[int]]:
    global _CASE_FOLDING
    if _CASE_FOLDING is None:
        _CASE_FOLDING = _parse_case_folding()
    return _CASE_FOLDING


def case_fold(input_cps: list[int]) -> list[int]:
    """Default full case folding of a codepoint sequence per RFC 8265
    §5.2.4 / UCD CaseFolding.txt status C ∪ F.  Codepoints absent
    from the table fold to themselves."""
    table = case_folding_table()
    out: list[int] = []
    for cp in input_cps:
        replacement = table.get(cp)
        if replacement is None:
            out.append(cp)
        else:
            out.extend(replacement)
    return out


# ─────────────────────────────────────────────────────────────────────
# PropertyValueAliases.txt — Script long-name ↔ 4-letter abbrev
# ─────────────────────────────────────────────────────────────────────


def _parse_script_name_to_abbrev() -> dict[str, str]:
    text = _read_data_file("PropertyValueAliases.txt")
    out: dict[str, str] = {}
    for line in text.splitlines():
        stripped = _strip_comment_and_trim(line)
        if not stripped:
            continue
        parts = [p.strip() for p in stripped.split(";")]
        if len(parts) < 3 or parts[0] != "sc":
            continue
        short = parts[1]
        long_name = parts[2]
        out[long_name] = short
    return out


_SCRIPT_NAME_TO_ABBREV: dict[str, str] | None = None


def _script_name_to_abbrev() -> dict[str, str]:
    global _SCRIPT_NAME_TO_ABBREV
    if _SCRIPT_NAME_TO_ABBREV is None:
        _SCRIPT_NAME_TO_ABBREV = _parse_script_name_to_abbrev()
    return _SCRIPT_NAME_TO_ABBREV


def _script_long_to_abbrev(name: str) -> str:
    table = _script_name_to_abbrev()
    if name in table:
        return table[name]
    raise KeyError(
        f"script_long_to_abbrev: {name!r} not in PropertyValueAliases.txt"
    )


# ─────────────────────────────────────────────────────────────────────
# Scripts.txt — codepoint → primary script (long name)
# ─────────────────────────────────────────────────────────────────────


@dataclass(frozen=True, slots=True)
class _ScriptRange:
    start: int
    end: int
    value: str


def _parse_scripts() -> list[_ScriptRange]:
    text = _read_data_file("Scripts.txt")
    out: list[_ScriptRange] = []
    for line in text.splitlines():
        stripped = _strip_comment_and_trim(line)
        if not stripped:
            continue
        parts = stripped.split(";", 1)
        if len(parts) < 2:
            continue
        start, end = _parse_range_field(parts[0])
        value = parts[1].strip()
        out.append(_ScriptRange(start=start, end=end, value=value))
    out.sort(key=lambda r: r.start)
    return out


_SCRIPTS_TABLE: list[_ScriptRange] | None = None


def _scripts_table() -> list[_ScriptRange]:
    global _SCRIPTS_TABLE
    if _SCRIPTS_TABLE is None:
        _SCRIPTS_TABLE = _parse_scripts()
    return _SCRIPTS_TABLE


def _partition_point(items: list, key, target: int) -> int:
    lo, hi = 0, len(items)
    while lo < hi:
        mid = (lo + hi) // 2
        if key(items[mid]) <= target:
            lo = mid + 1
        else:
            hi = mid
    return lo


def script_of(cp: int) -> str:
    table = _scripts_table()
    idx = _partition_point(table, lambda r: r.start, cp)
    if idx > 0:
        entry = table[idx - 1]
        if cp <= entry.end:
            return entry.value
    return "Unknown"


# ─────────────────────────────────────────────────────────────────────
# ScriptExtensions.txt — codepoint → multi-script abbrev list
# ─────────────────────────────────────────────────────────────────────


@dataclass(frozen=True, slots=True)
class _ScriptExtRange:
    start: int
    end: int
    value: tuple[str, ...]


def _parse_script_extensions() -> list[_ScriptExtRange]:
    text = _read_data_file("ScriptExtensions.txt")
    out: list[_ScriptExtRange] = []
    for line in text.splitlines():
        stripped = _strip_comment_and_trim(line)
        if not stripped:
            continue
        parts = stripped.split(";", 1)
        if len(parts) < 2:
            continue
        start, end = _parse_range_field(parts[0])
        scripts = tuple(parts[1].strip().split())
        if scripts:
            out.append(_ScriptExtRange(start=start, end=end, value=scripts))
    out.sort(key=lambda r: r.start)
    return out


_SCRIPT_EXT_TABLE: list[_ScriptExtRange] | None = None


def _script_extensions_table() -> list[_ScriptExtRange]:
    global _SCRIPT_EXT_TABLE
    if _SCRIPT_EXT_TABLE is None:
        _SCRIPT_EXT_TABLE = _parse_script_extensions()
    return _SCRIPT_EXT_TABLE


def resolve_scripts(cp: int) -> list[str]:
    """Return the resolved-script abbreviations for ``cp``.

    Uses ScriptExtensions when the codepoint has one; otherwise
    returns the single primary script from Scripts.txt mapped
    through PropertyValueAliases.txt to its 4-letter abbreviation.
    """
    ext_table = _script_extensions_table()
    idx = _partition_point(ext_table, lambda r: r.start, cp)
    if idx > 0:
        entry = ext_table[idx - 1]
        if cp <= entry.end:
            return list(entry.value)
    return [_script_long_to_abbrev(script_of(cp))]


def is_common_script(cp: int) -> bool:
    return script_of(cp) == "Common"


def is_inherited_script(cp: int) -> bool:
    return script_of(cp) == "Inherited"


def is_ignored_for_intersection(cp: int) -> bool:
    return is_common_script(cp) or is_inherited_script(cp)


def string_script_union(input_cps: list[int]) -> list[str]:
    acc: list[str] = []
    for cp in input_cps:
        if is_ignored_for_intersection(cp):
            continue
        for s in resolve_scripts(cp):
            if s not in acc:
                acc.append(s)
    return acc


# ─────────────────────────────────────────────────────────────────────
# IdentifierStatus.txt — UTS #39 General-Security-Profile Allowed set
# ─────────────────────────────────────────────────────────────────────


def _parse_identifier_status() -> list[tuple[int, int]]:
    text = _read_data_file("IdentifierStatus.txt")
    out: list[tuple[int, int]] = []
    for line in text.splitlines():
        stripped = _strip_comment_and_trim(line)
        if not stripped:
            continue
        parts = stripped.split(";", 1)
        if len(parts) < 2:
            continue
        status = parts[1].strip()
        if status != "Allowed":
            continue
        out.append(_parse_range_field(parts[0]))
    out.sort(key=lambda r: r[0])
    return out


_ID_ALLOWED: list[tuple[int, int]] | None = None


def _id_allowed_ranges() -> list[tuple[int, int]]:
    global _ID_ALLOWED
    if _ID_ALLOWED is None:
        _ID_ALLOWED = _parse_identifier_status()
    return _ID_ALLOWED


def is_id_allowed(cp: int) -> bool:
    table = _id_allowed_ranges()
    idx = _partition_point(table, lambda r: r[0], cp)
    if idx > 0:
        entry = table[idx - 1]
        if cp <= entry[1]:
            return True
    return False


# ─────────────────────────────────────────────────────────────────────
# DerivedCoreProperties.txt — Default_Ignorable_Code_Point ranges
# ─────────────────────────────────────────────────────────────────────


def _parse_default_ignorable() -> list[tuple[int, int]]:
    text = _read_data_file("DerivedCoreProperties.txt")
    out: list[tuple[int, int]] = []
    for line in text.splitlines():
        stripped = _strip_comment_and_trim(line)
        if not stripped:
            continue
        parts = stripped.split(";", 1)
        if len(parts) < 2:
            continue
        if parts[1].strip() != "Default_Ignorable_Code_Point":
            continue
        out.append(_parse_range_field(parts[0]))
    out.sort(key=lambda r: r[0])
    return out


_DEFAULT_IGNORABLE: list[tuple[int, int]] | None = None


def _default_ignorable_ranges() -> list[tuple[int, int]]:
    global _DEFAULT_IGNORABLE
    if _DEFAULT_IGNORABLE is None:
        _DEFAULT_IGNORABLE = _parse_default_ignorable()
    return _DEFAULT_IGNORABLE


def is_default_ignorable(cp: int) -> bool:
    """UAX #44 Default_Ignorable_Code_Point — covers invisible /
    format-control characters (ZWSP, ZWNJ, ZWJ, WJ, BOM, soft hyphen,
    bidi controls, Mongolian / variation selectors, tag block, etc.).
    Used by `letter_skeleton` to close the invisible-insertion bypass."""
    table = _default_ignorable_ranges()
    idx = _partition_point(table, lambda r: r[0], cp)
    if idx > 0:
        entry = table[idx - 1]
        if cp <= entry[1]:
            return True
    return False


def is_white_space(cp: int) -> bool:
    """UCD PropList.txt White_Space — covers ASCII tab/newline/space,
    NBSP (U+00A0), NNBSP (U+202F — often abused for invisibility),
    space-separator U+2000..U+200A, line/paragraph separators,
    medium math space, ideographic space.  Hardcoded since the
    range table is small and stable.

    Used by `letter_skeleton` to strip whitespace from typosquat
    comparison — whitespace inside an identifier is universally
    attacker abuse, never legitimate."""
    return (
        (0x0009 <= cp <= 0x000D)
        or cp == 0x0020
        or cp == 0x0085
        or cp == 0x00A0
        or cp == 0x1680
        or (0x2000 <= cp <= 0x200A)
        or (0x2028 <= cp <= 0x2029)
        or cp == 0x202F
        or cp == 0x205F
        or cp == 0x3000
    )


# ─────────────────────────────────────────────────────────────────────
# UTS #39 § 5.1 Restriction-level classification
# ─────────────────────────────────────────────────────────────────────


class RestrictionLevel(Enum):
    ASCII_ONLY = "ASCIIOnly"
    SINGLE_SCRIPT = "SingleScript"
    HIGHLY_RESTRICTIVE = "HighlyRestrictive"
    MODERATELY_RESTRICTIVE = "ModeratelyRestrictive"
    MINIMALLY_RESTRICTIVE = "MinimallyRestrictive"
    UNRESTRICTED = "Unrestricted"


def is_ascii_only(cps: list[int]) -> bool:
    return all(cp < 0x80 for cp in cps)


def _intersect_many(sets: list[list[str]]) -> list[str]:
    if not sets:
        return []
    acc = list(sets[0])
    for s in sets[1:]:
        acc = [x for x in acc if x in s]
    return acc


def string_resolved_scripts(cps: list[int]) -> list[str]:
    non_ignored = [cp for cp in cps if not is_ignored_for_intersection(cp)]
    if not non_ignored:
        return []
    sets = [resolve_scripts(cp) for cp in non_ignored]
    return _intersect_many(sets)


def is_single_script(cps: list[int]) -> bool:
    return (
        not is_ascii_only(cps)
        and len(string_resolved_scripts(cps)) > 0
    )


_COVERED_JAPANESE = ["Latn", "Hani", "Hira", "Kana"]
_COVERED_CHINESE = ["Latn", "Hani", "Bopo"]
_COVERED_KOREAN = ["Latn", "Hani", "Hang"]


def _intersects(a: list[str], b: list[str]) -> bool:
    return any(x in b for x in a)


def _all_within_covered(cps: list[int], covered: list[str]) -> bool:
    for cp in cps:
        if is_ignored_for_intersection(cp):
            continue
        r = resolve_scripts(cp)
        if not r or not _intersects(r, covered):
            return False
    return True


def is_covered_cjk(cps: list[int]) -> bool:
    return (
        _all_within_covered(cps, _COVERED_JAPANESE)
        or _all_within_covered(cps, _COVERED_CHINESE)
        or _all_within_covered(cps, _COVERED_KOREAN)
    )


def is_highly_restrictive(cps: list[int]) -> bool:
    return is_single_script(cps) or is_covered_cjk(cps)


def is_moderately_restrictive_shape(cps: list[int]) -> bool:
    other: str | None = None
    for cp in cps:
        if is_ignored_for_intersection(cp):
            continue
        r = resolve_scripts(cp)
        if not r:
            return False
        if "Latn" in r:
            continue
        s = r[0]
        if s in ("Cyrl", "Grek"):
            return False
        if other is None:
            other = s
        elif s != other:
            return False
    return other is not None


def is_minimally_restrictive(cps: list[int]) -> bool:
    return all(is_id_allowed(cp) for cp in cps)


def restriction_level(cps: list[int]) -> RestrictionLevel:
    if is_ascii_only(cps):
        return RestrictionLevel.ASCII_ONLY
    if is_single_script(cps):
        return RestrictionLevel.SINGLE_SCRIPT
    if is_highly_restrictive(cps):
        return RestrictionLevel.HIGHLY_RESTRICTIVE
    if is_moderately_restrictive_shape(cps):
        return RestrictionLevel.MODERATELY_RESTRICTIVE
    if is_minimally_restrictive(cps):
        return RestrictionLevel.MINIMALLY_RESTRICTIVE
    return RestrictionLevel.UNRESTRICTED
