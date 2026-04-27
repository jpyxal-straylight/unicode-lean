# unicode-lean

Unicode normalization (UAX #15), the bidirectional algorithm
(UAX #9), PRECIS identifier preparation (RFC 8264 / 8265), and
confusable-skeleton equivalence (UTS #39 §4) — machine-checked in
Lean 4.28.0 against UCD 17.0.0. Lean core only — no Mathlib, no
external dependencies. Zero `sorry`, zero `admit`, zero
project-local `axiom`, zero runtime escape.

## Pillars

| Pillar | Reference | Headline theorem |
|---|---|---|
| Normalization | UAX #15 | `Normalization.QuickCheckSoundnessTheorem.quickCheck_sound` — `isNFCQuickCheck cps = true → toNFC cps = cps` |
| PRECIS | RFC 8264 / 8265 | `Precis.Preparation.precis_idempotent` — preparation pipeline is idempotent on its image |
| Bidirectional Algorithm | UAX #9 | `Bidi.Algorithm.bidiParagraph` — P / X / W / N / I / L1 / L4 phases |
| Confusables | UTS #39 §4 | `Confusables.areConfusable_trans` — confusable-skeleton equivalence relation |

## Workflow

```bash
nix develop          # dev shell with the pinned Lean toolchain
nix build            # full library; cold rebuilds elaborate every native_decide table
nix run              # status report — file / theorem / sorry counts, per pillar
nix flake check      # build + zero-sorry / zero-admit guard
```

Or with `lake` directly inside the dev shell:

```bash
lake build
lake build Unicode.Normalization.QuickCheckSoundnessTheorem
```

## Layout

```
unicode-lean/
├── flake.nix                    # nix integration
├── lakefile.lean                # lake config
├── lean-toolchain               # pinned Lean version
├── Unicode.lean                 # root import
├── Unicode/
│   ├── Bidi/Algorithm.lean      # UAX #9
│   ├── CaseFoldCommutation.lean # UAX #15 + UAX #44 §5.18
│   ├── CaseFoldRoundtrip.lean
│   ├── Confusables.lean         # UTS #39 §4
│   ├── Generated/               # 19 files — UCD-derived tables
│   ├── Invariants.lean
│   ├── Normalization/           # 29 files — NFC/NFKC/NFD/NFKD + soundness kernel
│   ├── Precis/                  # 8 files — RFC 8264 / 8265
│   ├── Refined.lean
│   └── Ucd/                     # UCD 17.0.0 source data + SHA256SUMS
├── scripts/                     # CI hardening (see Guarantees)
└── .github/                     # CI workflows + governance
```

`nix run` prints the live file / theorem inventory.

## Guarantees

* **Zero `sorry`, zero `admit`** — proven, not assumed.
* **Zero project-local `axiom`** — only Lean 4 core's `propext`,
  `Quot.sound`, and `Classical.choice` are in the trusted base.
* **Zero runtime escape** — no `unsafe`, `unsafePerformIO`,
  `unsafeCast`, `Lean.ofReduceBool`, or `Lean.reduceBool`.
* **Zero Mathlib dependency** — Lean 4 core only; auditable from
  first principles.
* **Pinned UCD source** — UCD 17.0.0 files vendored under
  `Unicode/Ucd/` and SHA-256-pinned in `Unicode/Ucd/SHA256SUMS`.
  `include_str` embeds the bytes at build time; CI rejects drift.
* **`autoImplicit := false`** — explicit universes, explicit types,
  no implicit-argument inference at type-class boundaries.
* **Reproducible** — back-to-back `lake build` runs produce
  byte-identical `.olean` files. The nightly `reproducibility`
  workflow verifies this and publishes the SHA-256 manifest as an
  `oleans-sha256-<commit-sha>` build artifact for downstream
  auditors.

The four source-level guards (`check-sorry.sh`, `check-no-axiom.sh`,
`check-orphan-files.sh`, `check-ucd-hashes.sh`) live under `scripts/`
and run on every push and pull request via the `ci / hardening`
workflow.

## Generated tables — provenance

Every file under `Unicode/Generated/` is self-contained and
auditable end-to-end without reference to any external code
generator. The pattern, identical across all 19 generated tables:

1. The corresponding UCD source file (e.g. `Unicode/Ucd/CaseFolding.txt`)
   is byte-pinned in `Unicode/Ucd/SHA256SUMS` and verified by
   `scripts/check-ucd-hashes.sh`.
2. A Lean parser for that file's grammar lives **inline** in the
   Generated module — `parseHex`, `parseRange`, `parse<Row>`, etc.
3. The raw `.txt` is embedded into the module via
   `include_str "../Ucd/<file>.txt"`, producing a `String` constant
   at compile time.
4. The typed table (`mappings`, `ranges`, etc.) is computed by
   running the inline parser over the embedded raw string at module
   load.

There is no separate code-generation step, no external tool, no
pre-commit hook that emits the tables — the parser, the input
bytes, and the resulting typed data all live in the same file and
are verified together by the build. To audit how a given table was
derived, open the corresponding `Unicode/Generated/*.lean` file.

## Use it from another Lake project

```lean
require unicode from git
  "https://github.com/jpyxal-straylight/unicode-lean" @ "v0.1.0"
```

```lean
import Unicode

-- or pin to a specific theorem
import Unicode.Normalization.QuickCheckSoundnessTheorem
```

## License

Apache License 2.0. See [`LICENSE`](LICENSE).

The bundled UCD 17.0.0 source files under `Unicode/Ucd/` are
redistributed under the
[Unicode License v3](https://www.unicode.org/license.txt); see
[`NOTICE`](NOTICE) for attribution.
