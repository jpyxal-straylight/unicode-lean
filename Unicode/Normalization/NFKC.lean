/-
  Unicode.Normalization.NFKC

  Normalization Form KC (compatibility decomposition + canonical
  reordering + canonical composition) per UAX #15 §1.3:

    toNFKC = compose ∘ toNFKD = compose ∘ reorder ∘ compatDecomposeSequence

  Parallel to `Unicode.Normalization.NFC` with the compatibility
  decomposition pipeline as the first stage. Composition is canonical
  in both NFC and NFKC: only canonical decompositions recompose under
  primary composition. Compatibility decomposition targets that have
  no canonical recomposition stay in their decomposed form.

  Quick-check is keyed off `DerivedNormalizationProps.nfkcQC`:

    * `isNFKCQuickCheck` — returns `true` when every codepoint has
      `NFKC_QC = Y` AND combining marks are in non-decreasing CCC
      order within each non-starter run; proves the sequence is
      already in NFKC without running the full pipeline.
    * `isNFKC`           — the definitive check: `toNFKC cps = cps`.
      Used when the quick check is inconclusive (any codepoint with
      `NFKC_QC = M`) or when a caller wants the full round-trip
      guarantee.
-/

import Unicode.Normalization.NFKD
import Unicode.Normalization.NFC
import Unicode.Normalization.Compose
import Unicode.Generated.DerivedNormalizationProps

namespace Unicode.Normalization.NFKC

open Unicode.Normalization
open Unicode.Generated

/-- Apply the full NFKC pipeline to a codepoint sequence. -/
def toNFKC (cps : Array Nat) : Array Nat :=
  Compose.compose (NFKD.toNFKD cps)

/-- Look up a codepoint's `NFKC_QuickCheck` value. Falls back to the
    source file's `@missing` default (`Y`) when the codepoint is not
    covered by any explicit range. -/
def nfkcQCValue (cp : Nat) : DerivedNormalizationProps.NFC_QC :=
  match DerivedNormalizationProps.nfkcQC.findSome?
          (fun ⟨min, max, v⟩ => if min ≤ cp ∧ cp ≤ max then some v else none) with
  | some v => v
  | none   => DerivedNormalizationProps.defaultNfkcQC

/-- Quick check per UAX #15 Annex 8: a sequence is guaranteed to be in
    NFKC when (a) every codepoint has `NFKC_QC = Y` AND (b) CCC values
    are non-decreasing within non-starter runs. Returns `true` on a
    YES-verdict, `false` otherwise (inconclusive `M` or out-of-order
    cases). The HSR check reuses `NFC.hasSortedRunsBool` because the
    canonical reorder stage is identical to NFC's. -/
def isNFKCQuickCheck (cps : Array Nat) : Bool :=
  cps.all (fun cp => decide (nfkcQCValue cp = .Y)) &&
  NFC.hasSortedRunsBool cps.toList

/-- Definitive NFKC check: a sequence is in NFKC iff applying the NFKC
    pipeline to it is a no-op. -/
def isNFKC (cps : Array Nat) : Bool :=
  toNFKC cps = cps

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty sequence. -/
theorem toNFKC_empty : toNFKC #[] = #[] := by native_decide

/-- Pure ASCII is in NFKC unchanged. -/
theorem toNFKC_ascii :
    toNFKC #[0x0048, 0x0069] = #[0x0048, 0x0069] := by native_decide  -- "Hi"

/-- Decomposed → precomposed under canonical composition (same as NFC). -/
theorem toNFKC_composes_A_grave :
    toNFKC #[0x0041, 0x0300] = #[0x00C0] := by native_decide

/-- SUPERSCRIPT TWO U+00B2 → U+0032 under NFKC. The compat decomposition
    target (DIGIT TWO) has no canonical composition back to U+00B2, so
    the output stays decomposed. -/
theorem toNFKC_super_2 :
    toNFKC #[0x00B2] = #[0x0032] := by native_decide

/-- NO-BREAK SPACE U+00A0 → SPACE U+0020 under NFKC. -/
theorem toNFKC_nbsp :
    toNFKC #[0x00A0] = #[0x0020] := by native_decide

/-- LATIN SMALL LIGATURE FF (U+FB00) → "ff" (lowercase) under NFKC. -/
theorem toNFKC_ligature_ff :
    toNFKC #[0xFB00] = #[0x0066, 0x0066] := by native_decide

/-- HANGUL: decomposed jamo LV recompose to the precomposed syllable. -/
theorem toNFKC_hangul :
    toNFKC #[0x1100, 0x1161] = #[0xAC00] := by native_decide

/-- `isNFKCQuickCheck` is conservative: pure ASCII has `NFKC_QC = Y`
    and the quick check returns `true`. -/
theorem isNFKCQuickCheck_ascii :
    isNFKCQuickCheck #[0x0048, 0x0069] = true := by native_decide

/-- `isNFKCQuickCheck` returns `false` for an `NFKC_QC = N` codepoint.
    NO-BREAK SPACE U+00A0 has `NFKC_QC = N` per the pinned table. -/
theorem isNFKCQuickCheck_nbsp :
    isNFKCQuickCheck #[0x00A0] = false := by native_decide

/-- `nfkcQCValue` default: `A` has `NFKC_QC = Y` (not in the explicit
    table; falls back to `defaultNfkcQC`). -/
theorem nfkcQC_default_ascii : nfkcQCValue 0x0041 = .Y := by native_decide

/-- `nfkcQCValue` explicit: U+00A0 is listed with `NFKC_QC = N`. -/
theorem nfkcQC_explicit_N : nfkcQCValue 0x00A0 = .N := by native_decide

end Unicode.Normalization.NFKC
