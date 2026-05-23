# unicode-python

Strict Unicode security-conformance library for Python 3.11+.
Pure Python, no third-party runtime dependencies, frozen
dataclasses, fully type-annotated.  Suited to identifier
validators, supply-chain scanners, log-line ingest, AI/data
tooling that touches user-supplied text.

## What it ships

**Codec layer**

- Strict RFC 3629 UTF-8 codec with a six-variant reject taxonomy —
  `OverlongEncoding`, `SurrogateCodepoint`, `CodepointBeyondMax`,
  `TruncatedSequence`, `InvalidStartByte`, `InvalidContinuationByte`.
  No silent replacement, no U+FFFD substitution; malformed input is
  rejected with the exact reason and byte offset.
- UTF-16 / UTF-32 / BOM detection.
- Refinement types — `ValidatedUtf8`, `Utf8Blob`, `IdentifierUtf8`
  with smart constructors that fail rather than admit malformed
  input.
- Noncharacter and scalar-value validation.

**Security Conformance Layer**

- Shared verdict vocabulary — `Family`, `Severity`, `AdversaryTier`,
  `ClassificationKind`, `HazardPosition`, `KeyValueAttribution`.
- Covert-channel detector family (4 detectors)
  - `TagBlockPayload` — GoodSide-class invisible-glyph injection in
    the Unicode tag block U+E0000..U+E007F.
  - `VariationSelectorPayload` — GlassWorm-class hidden binary
    payload encoded into the variation-selector ranges
    U+FE00..U+FE0F and U+E0100..U+E01EF.
  - `ZeroWidthPayload` — zero-width / no-glyph injection,
    word-joiner spoofing, and the AI-watermark NNBSP pattern.
  - `BidiControlBalance` — Trojan Source class (CVE-2021-42574 /
    CVE-2021-42694), full per-type stack walker with the UAX #9
    §3.3.2 depth cap.
- Identity-spoofing detector family
  - `HomoglyphConfusable` — six sub-threats in fixed priority order:
    `TargetMatch` / `MathAlpha` / `WidthClass` / `DecompositionSwap`
    / `CrossScriptMix` / `RestrictionLow`.  Catches the Nethereum
    October-2025 NuGet supply-chain attack class (Cyrillic 'е'
    U+0435 swapped for Latin 'e' inside published package names),
    Mathematical-Alphanumeric Latin posing, fullwidth Latin posing,
    decomposition-form drift, cross-script mixing, and identifiers
    that fall below the UTS #39 Highly-Restrictive bar.
- Full UAX #15 NFC normalization pipeline (canonical decompose +
  reorder + compose, with Hangul algorithmic decomposition and
  composition).
- UTS #39 § 5.1 restriction-level classifier (ASCII-Only,
  Single-Script, Highly-Restrictive, Moderately-Restrictive,
  Minimally-Restrictive, Unrestricted).

**Bundled UCD 17.0.0 data**

SHA-256 pinned in `data/SHA256SUMS`.  The package ships a working
copy inside `src/unicode_python/data/` for runtime loading via
`importlib.resources`.

- `KnownAttackTargets.txt` — curated catalogue of canonical names
  with published incident evidence (CVE / vendor advisory /
  peer-reviewed paper).
- `confusables.txt` — UTS #39 §4 skeleton mappings (6 355 entries).
- `UnicodeData.txt` — canonical combining class + canonical
  decomposition.
- `CompositionExclusions.txt`.
- `Scripts.txt`, `ScriptExtensions.txt`.
- `IdentifierStatus.txt`.
- `PropertyValueAliases.txt` — long-name ↔ four-letter abbreviation
  mapping.

## Install

```sh
pip install .
```

Build with `hatchling` (already declared in `pyproject.toml`);
runtime requires Python 3.11+ for `Self`/`Union` syntax and
`importlib.resources.files`.

## Test

```sh
pytest
```

Covers codec, covert-channel detectors, and the full six-sub-threat
`HomoglyphConfusable` (NFC, cross-script, restriction-level).

## Use

```python
from unicode_python.security import ClassificationKind
from unicode_python.security.identity import homoglyph_confusable

# "Nethereum" with the second 'e' replaced by Cyrillic SMALL
# LETTER IE (U+0435) — the Oct-2025 NuGet supply-chain pattern.
input_cps = [
    0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D,
]
v = homoglyph_confusable.detect(input_cps)

assert v.kind is ClassificationKind.HAZARD
assert homoglyph_confusable.sub_threat_tag(v.sub) == "TargetMatch"
assert v.sub.target == "Nethereum"
```

## Data integrity

```sh
./scripts/check-ucd-hashes.sh
```

Verifies the bundled UCD source files against the SHA-256 manifest
in `data/SHA256SUMS`.  Recommended as a CI gate; a mismatch indicates
either an unintentional edit to vendored data or an attacker-induced
table swap that would otherwise allow malformed verdicts.

## License

MIT.
