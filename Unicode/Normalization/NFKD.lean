/-
  Unicode.Normalization.NFKD

  Normalization Form KD (compatibility decomposition + canonical
  reordering) per UAX #15 §1.3:

    toNFKD = reorder ∘ compatDecomposeSequence

  Differs from NFD only in the decomposition stage: NFD applies just
  canonical decomposition; NFKD applies both canonical and
  compatibility decompositions. The reorder stage is identical (both
  forms canonically order combining marks within each non-starter run).
-/

import Unicode.Normalization.CompatDecompose
import Unicode.Normalization.NFC
import Unicode.Normalization.Reorder
import Unicode.Generated.DerivedNormalizationProps

namespace Unicode.Normalization.NFKD

open Unicode.Normalization
open Unicode.Generated

/-- Apply the compatibility decomposition + canonical reorder pipeline. -/
def toNFKD (cps : Array Nat) : Array Nat :=
  Reorder.reorder (CompatDecompose.compatDecomposeSequence cps)

/-- Look up a codepoint's `NFKD_QuickCheck` value. Falls back to the
    source file's `@missing` default (`Y`). -/
def nfkdQCValue (cp : Nat) : DerivedNormalizationProps.NFC_QC :=
  match DerivedNormalizationProps.nfkdQC.findSome?
          (fun ⟨min, max, v⟩ => if min ≤ cp ∧ cp ≤ max then some v else none) with
  | some v => v
  | none   => DerivedNormalizationProps.defaultNfkdQC

/-- Quick check per UAX #15 §A.1 NFKD: a sequence is guaranteed to be in
    NFKD when every codepoint has `NFKD_QC = Y` AND combining marks are
    in canonical CCC order. The HSR check reuses
    `NFC.hasSortedRunsBool` because the canonical reorder stage is
    identical between NFKD and the canonical forms. -/
def isNFKDQuickCheck (cps : Array Nat) : Bool :=
  cps.all (fun cp => decide (nfkdQCValue cp = .Y)) &&
  NFC.hasSortedRunsBool cps.toList

/-- Definitive NFKD check: a sequence is in NFKD iff applying the NFKD
    pipeline to it is a no-op. -/
def isNFKD (cps : Array Nat) : Bool :=
  toNFKD cps = cps

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty sequence. -/
theorem toNFKD_empty : toNFKD #[] = #[] := by native_decide

/-- Pure ASCII is in NFKD unchanged. -/
theorem toNFKD_ascii :
    toNFKD #[0x0048, 0x0069] = #[0x0048, 0x0069] := by native_decide  -- "Hi"

/-- A precomposed letter with a canonical decomposition: NFKD reaches
    it through the canonical branch (same output as NFD). -/
theorem toNFKD_decomposes_A_grave :
    toNFKD #[0x00C0] = #[0x0041, 0x0300] := by native_decide

/-- SUPERSCRIPT TWO U+00B2 has only a compatibility decomposition;
    NFKD applies it where NFD would not. -/
theorem toNFKD_decomposes_super_2 :
    toNFKD #[0x00B2] = #[0x0032] := by native_decide

/-- NO-BREAK SPACE U+00A0 → U+0020 under NFKD. -/
theorem toNFKD_nbsp :
    toNFKD #[0x00A0] = #[0x0020] := by native_decide

/-- DIAERESIS U+00A8 → SPACE + COMBINING DIAERESIS under NFKD. The
    output's combining-mark order is already canonical (single mark). -/
theorem toNFKD_diaeresis :
    toNFKD #[0x00A8] = #[0x0020, 0x0308] := by native_decide

/-- LATIN SMALL LIGATURE FF (U+FB00) decomposes via compatibility to two
    lowercase f's (U+0066 U+0066). -/
theorem toNFKD_ligature_ff :
    toNFKD #[0xFB00] = #[0x0066, 0x0066] := by native_decide

/-- HANGUL precomposed syllable decomposes algorithmically (canonical
    path; compat path is unused). -/
theorem toNFKD_hangul :
    toNFKD #[0xAC00] = #[0x1100, 0x1161] := by native_decide

/-- `isNFKD` returns `true` for ASCII. -/
theorem isNFKD_ascii : isNFKD #[0x0048, 0x0069] = true := by native_decide

/-- `isNFKD` returns `false` for SUPERSCRIPT TWO (decomposes). -/
theorem isNFKD_super_2 : isNFKD #[0x00B2] = false := by native_decide

end Unicode.Normalization.NFKD
