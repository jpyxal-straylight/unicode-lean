/-
  Unicode.Normalization.Lookup

  Thin accessors that bridge the Generated/* UCD tables and the NFC
  algorithms in this Normalization/* namespace. Keeps table-shape
  concerns out of the algorithm implementations.

  Lookup is linear-scan. The `Generated` tables are pre-sorted by
  codepoint, leaving room for binary-search or packed lookup as
  optimizations when `#eval` budgets demand it.
-/

import Unicode.Generated.UnicodeData
import Unicode.Generated.CompositionExclusions
import Unicode.Generated.DerivedNormalizationProps

namespace Unicode.Normalization.Lookup

open Unicode.Generated

/-- Find the `UnicodeDataRow` for a codepoint, if one is present in the
    pinned NFC-relevant subset. Returns `none` for codepoints that are
    both `CCC = 0` and have no canonical decomposition. -/
def lookupRow (cp : Nat) : Option UnicodeData.UnicodeDataRow :=
  UnicodeData.rows.find? (fun r => r.codepoint = cp)

/-- Canonical_Combining_Class for a codepoint. Unlisted codepoints have
    `CCC = 0` per the UCD's implicit default for the NFC-relevant
    filter. -/
def canonicalCombiningClass (cp : Nat) : Nat :=
  match lookupRow cp with
  | some r => r.canonicalCombiningClass
  | none   => 0

/-- Canonical decomposition target sequence for a codepoint. Returns
    the empty array when the codepoint has no canonical decomposition
    (every codepoint outside the pinned subset, and many inside it). -/
def canonicalDecomposition (cp : Nat) : Array Nat :=
  match lookupRow cp with
  | some r => r.canonicalDecomposition
  | none   => #[]

/-- Whether a codepoint appears in CompositionExclusions.txt. When
    `true`, the codepoint decomposes canonically but must NOT recompose
    during NFC synthesis. -/
def isCompositionExclusion (cp : Nat) : Bool :=
  CompositionExclusions.codepoints.contains cp

/-- Whether a codepoint is marked `Full_Composition_Exclusion` in
    DerivedNormalizationProps. Strictly broader than
    `isCompositionExclusion`: includes singleton and non-starter
    decompositions in addition to the CompositionExclusions set. The
    NFC algorithm uses this broader test when deciding which canonical
    decompositions may recompose. -/
def isFullCompositionExclusion (cp : Nat) : Bool :=
  DerivedNormalizationProps.fullCompositionExclusion.any
    (fun ⟨min, max⟩ => decide (min ≤ cp ∧ cp ≤ max))

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- Concrete lookups that anchor the table bindings. Each closes by
-- `native_decide` — the array scans execute as compiled code.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `A` (0x0041) is NFC-inert: CCC = 0, no canonical decomposition. -/
theorem latin_A_ccc : canonicalCombiningClass 0x0041 = 0 := by native_decide

theorem latin_A_decomp : canonicalDecomposition 0x0041 = #[] := by native_decide

/-- COMBINING GRAVE ACCENT (0x0300) has CCC = 230 (above). -/
theorem combining_grave_ccc : canonicalCombiningClass 0x0300 = 230 := by native_decide

/-- LATIN CAPITAL LETTER A WITH GRAVE (0x00C0) decomposes canonically
    to `A` + combining grave. -/
theorem latin_A_grave_decomp :
    canonicalDecomposition 0x00C0 = #[0x0041, 0x0300] := by native_decide

/-- ANGSTROM SIGN (0x212B) decomposes to LATIN CAPITAL LETTER A WITH RING
    ABOVE (0x00C5), which in turn decomposes to `A` + combining ring. -/
theorem angstrom_decomp : canonicalDecomposition 0x212B = #[0x00C5] := by native_decide

/-- DEVANAGARI LETTER QA (0x0958) is a CompositionExclusion. -/
theorem devanagari_qa_is_exclusion : isCompositionExclusion 0x0958 = true := by native_decide

/-- `A` is not a CompositionExclusion. -/
theorem latin_A_not_exclusion : isCompositionExclusion 0x0041 = false := by native_decide

/-- The CompositionExclusions set is a subset of the FullCompositionExclusion
    set. Sanity-check at a known overlap point. -/
theorem devanagari_qa_is_full_exclusion :
    isFullCompositionExclusion 0x0958 = true := by native_decide

end Unicode.Normalization.Lookup
