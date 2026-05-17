# unicode-hs

Haskell port of [unicode-lean][1] — strict UTF-8 / UTF-16 / UTF-32
codecs, BOM detection, noncharacter detection, UAX #31 default
identifiers, and RFC 8264 / 8265 PRECIS profiles, all pinned to UCD
17.0.0 (UCA 16.0.0).

This port lives on the `haskell-port` branch of `unicode-lean`, in this
`unicode-hs/` subdirectory. The Lean reference is one directory up.

[1]: ../

## What this library is

unicode-lean (on the `main` branch) is the reference: machine-checked
in Lean 4, zero `sorry` / `admit` / project-local `axiom`, every
algorithm proven against the published UCD conformance fixtures.
unicode-hs is the Haskell re-implementation of those same algorithms.

Both ports share the same source of truth — the upstream UCD `.txt`
files at UCD 17.0.0 vendored under `../Unicode/Ucd/` — and are kept in
lockstep by running the same conformance fixtures (`BidiTest.txt`,
`IdnaTestV2.txt`, `GraphemeBreakTest.txt`, `CollationTest_*.txt`, …)
through both implementations. Bytewise equivalence on every fixture row
is the contract.

The Haskell port does not vendor or import anything from the Lean
side. The trust anchor is the UCD files and the conformance test data,
not the Lean source.

## Phase status

| Phase | Surface | Status |
|---|---|---|
| 1 | Strict UTF-8 codec — validator, decoder, encoder, roundtrip | shipped |
| 2 | Remaining table-free codecs — UTF-16 BE/LE, UTF-32 BE/LE, BOM detection, noncharacter predicate + enumeration, strict-ASCII identifier predicate, `ValidatedUtf8` / `Utf8Blob` / `IdentifierUtf8` refinement types | shipped |
| 3 | UAX #31 default identifier — needs UCD tables (ID_Start, ID_Continue, XID_Start, XID_Continue, Pattern_Syntax, Pattern_White_Space) | not started |
| 4 | RFC 8264 PRECIS IdentifierClass / FreeformClass + RFC 8265 UsernameCasePreserved / UsernameCaseMapped / OpaqueString | not started |
| 5 | Printable-UTF-8 profile (`Unicode/Codec/Printable.lean` — needs DerivedCoreProperties for default-ignorable filtering) | not started |

Future phases (normalization, bidi, segmentation, collation, IDNA,
confusables) ship when a specific downstream consumer asks for them.
They do not exist as types in this library until that happens.

Phase 1 ships exactly what its type surface claims — no stubs, no
deferred constructors, no commented-out atoms. Subsequent phases follow
the same discipline.

## Build

```sh
cabal build
cabal test
```

The test suite mirrors the closed-form theorems in
`../Unicode/Codec/Utf8Roundtrip.lean`:

* concrete unit tests — one per `theorem step_*` and `*_rejected`
* per-byte-class QuickCheck roundtrips
* exhaustive roundtrip across every valid scalar codepoint
  (0..0x10FFFF excluding the surrogate block) — the Haskell counterpart
  of the Lean `decode_encode_codepoint` theorem

## Consuming unicode-hs from lemma

Two options.

### Source-repository-package, pinned by commit

In `lemma/cabal.project`:

```cabal
source-repository-package
  type:     git
  location: https://github.com/jpyxal-straylight/unicode-lean
  tag:      <commit-sha-on-haskell-port-branch>
  subdir:   unicode-hs

-- Or, while developing locally:
packages:
  .
  ../unicode/unicode-hs
```

### Nix flake input

In `lemma/flake.nix`:

```nix
inputs.unicode-hs.url = "path:../unicode/unicode-hs";
-- Or, pinned to the haskell-port branch:
-- inputs.unicode-hs.url = "github:jpyxal-straylight/unicode-lean/haskell-port?dir=unicode-hs";
```

The flake exports `packages.unicode-hs` and a `devShells.default` with
GHC + cabal + HLS.

## UCD source of truth

`data/UCD-VERSION` pins the UCD release. Once Phase 3 lands and table
data is vendored or referenced under `data/`, `data/SHA256SUMS` will
pin each file by hash; `scripts/check-ucd-hashes.sh` enforces the
manifest at build time. The same hashes are committed on the `main`
branch under `Unicode/Ucd/SHA256SUMS`, so version drift between the
Lean and Haskell ports is structurally hard to miss: a PR that updates
one side without the other shows up plainly in the branch diff.

## Why this layout

unicode-lean (on `main`) is the spec + reference + test oracle.
unicode-hs (on `haskell-port`) is the production Haskell runtime for
everything in the [jpyxal/lemma](../../lemma) substrate that touches
protocol-boundary strings. The two live in the same repo on different
branches so spec/runtime drift is structurally hard to miss.

Consumers depend on the `haskell-port` branch (or a pinned commit on
it) and never need a Lean toolchain to build. The C++ port, when it
lands, will be a third branch on the same repo using the same
conformance fixtures.
