# unicode

Machine-checked specifications for the Unicode standard, pinned at
**UCD 17.0.0** and **Lean 4.28.0**. Self-contained: no Mathlib, no
external Lean dependencies.

## Pillars

| Pillar | Reference | Headline theorem |
|---|---|---|
| Normalization | UAX #15 | `Normalization.QuickCheckSoundnessTheorem.quickCheck_sound` — `isNFCQuickCheck cps = true → toNFC cps = cps` |
| PRECIS | RFC 8264 / 8265 | `Precis.Preparation.precis_idempotent` — preparation pipeline is a fixed point on its image |
| Bidirectional Algorithm | UAX #9 | `Bidi.Algorithm.bidiParagraph` — P / X / W / N / I / L1 / L4 phases |
| Confusables | UTS #39 §4 | `Confusables.areConfusable_trans` — confusable-skeleton equivalence relation |

## Workflow

```bash
# enter dev shell (installs Lean 4.28.0 via elan on first entry)
nix develop

# build the whole library (slow on first build because of native_decide
# table elaboration; fast incremental thereafter)
nix build

# status report (file / theorem / sorry counts, per-pillar progress)
nix run

# CI check (build + zero-sorry / zero-admit guard)
nix flake check
```

Or directly with `lake` inside the dev shell:

```bash
lake build
lake build Unicode.Normalization.QuickCheckSoundnessTheorem
```

## Layout

```
unicode/
├── flake.nix                          # nix integration
├── lakefile.lean                      # lake config
├── lean-toolchain                     # pinned Lean version
├── Unicode.lean                       # root import
├── Unicode/
│   ├── Bidi/
│   │   └── Algorithm.lean             # UAX #9 P/X/W/N/I/L1/L4
│   ├── Generated/                     # UCD-derived tables
│   │   ├── BidiBrackets.lean
│   │   ├── BidiMirroring.lean
│   │   ├── CaseFolding.lean
│   │   ├── CompatDecomp.lean
│   │   ├── CompositionExclusions.lean
│   │   ├── Confusables.lean
│   │   ├── DerivedBidiClass.lean
│   │   ├── DerivedCoreProperties.lean
│   │   ├── DerivedGeneralCategory.lean
│   │   ├── DerivedNormalizationProps.lean
│   │   ├── EastAsianWidth.lean
│   │   ├── IdentifierStatus.lean
│   │   ├── IdentifierType.lean
│   │   ├── IdnaMapping.lean
│   │   ├── PropList.lean
│   │   ├── ScriptExtensions.lean
│   │   ├── Scripts.lean
│   │   ├── UnicodeData.lean
│   │   └── WidthCompatMappings.lean
│   ├── Normalization/                 # UAX #15
│   │   ├── Compose.lean
│   │   ├── ComposeBlockAdditive.lean
│   │   ├── ComposeBufferStructure.lean
│   │   ├── ComposeInversion.lean
│   │   ├── ComposeKernelSupport.lean
│   │   ├── ComposeNonstarterSlide.lean
│   │   ├── CompatDecompose.lean
│   │   ├── Decomposability.lean
│   │   ├── Decompose.lean
│   │   ├── Distribute.lean
│   │   ├── Hangul.lean
│   │   ├── Invertibility.lean
│   │   ├── Lookup.lean
│   │   ├── NFC.lean
│   │   ├── NFD.lean
│   │   ├── NFKC.lean
│   │   ├── NFKD.lean
│   │   ├── QuickCheckFacts.lean
│   │   ├── QuickCheckHangulFacts.lean
│   │   ├── QuickCheckSoundness.lean
│   │   ├── QuickCheckSoundnessFact4.lean
│   │   ├── QuickCheckSoundnessMaster.lean
│   │   ├── QuickCheckSoundnessSingletonTable.lean
│   │   ├── QuickCheckSoundnessSnoc.lean
│   │   ├── QuickCheckSoundnessSnocClosure.lean
│   │   ├── QuickCheckSoundnessTheorem.lean
│   │   ├── Reorder.lean
│   │   ├── ReorderAppend.lean
│   │   └── ToNFDAppend.lean
│   ├── Precis/                        # RFC 8264 / 8265
│   │   ├── BidiRule.lean
│   │   ├── CaseMapping.lean
│   │   ├── Categories.lean
│   │   ├── IdentifierClass.lean
│   │   ├── OpaqueString.lean
│   │   ├── Preparation.lean
│   │   ├── WidthMapping.lean
│   │   └── ZsPreservation.lean
│   ├── Ucd/                           # UCD 17.0.0 source data
│   │   └── *.txt
│   ├── CaseFoldCommutation.lean       # UAX #15 + UAX #44 §5.18
│   ├── CaseFoldRoundtrip.lean
│   ├── Confusables.lean               # UTS #39 §4
│   ├── Invariants.lean
│   └── Refined.lean
└── scripts/
    ├── check-sorry.sh                # zero sorry / admit
    ├── check-no-axiom.sh             # zero axiom / unsafe / runtime escape
    ├── check-orphan-files.sh         # every .lean transitively imported
    └── check-ucd-hashes.sh           # UCD source files match SHA-256
```

## Verification properties

* **Zero `sorry`, zero `admit`** — proven, not assumed.
* **Zero project-local `axiom`** — only Lean 4 core's three axioms
  (`propext`, `Quot.sound`, `Classical.choice`) are in the trusted
  base; no `unsafe`, no `unsafePerformIO`, no `Lean.ofReduceBool`,
  no `Lean.reduceBool` runtime escapes.
* **Zero Mathlib dependency** — Lean 4 core only. No external proof
  libraries. Auditable from first principles.
* **Pinned UCD version** — UCD 17.0.0 source files vendored under
  `Unicode/Ucd/`; `include_str` embeds the exact bytes at build time;
  `Unicode/Ucd/SHA256SUMS` pins them by SHA-256 and CI rejects drift.
* **`autoImplicit := false`** — explicit universes, explicit types,
  no implicit-argument inference at type-class boundaries.
* **Reproducible build** — two consecutive `lake build` runs produce
  byte-identical `.olean` artefacts; verified nightly by the
  `reproducibility` workflow.

The four guards are scripted under `scripts/` and run on every push
and pull request by the `ci / hardening` workflow.

## Adding a downstream consumer

To depend on this package from another Lake project:

```lean
require unicode from git
  "https://github.com/jpyxal-straylight/unicode-lean" @ "v0.1.0"
```

Then:

```lean
import Unicode

-- or import a specific theorem path
import Unicode.Normalization.QuickCheckSoundnessTheorem
```

## License

Apache License 2.0. See [`LICENSE`](LICENSE).

The bundled UCD 17.0.0 source files under `Unicode/Ucd/` are
redistributed under the [Unicode License v3](https://www.unicode.org/license.txt);
see [`NOTICE`](NOTICE) for attribution.
