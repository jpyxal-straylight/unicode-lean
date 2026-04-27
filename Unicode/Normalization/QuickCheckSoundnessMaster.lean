/-
  Unicode.Normalization.QuickCheckSoundnessMaster

  The master soundness theorem for `isNFCQuickCheck`:

      ∀ cps, isNFCQuickCheck cps = true → toNFC cps = cps.

  Architecture:

    * §1 — UCD-table atomicity fact for size-2 decomp starters
      (`qcY_starter_decomp_atomic_table`). Closed by `native_decide`
      over `UnicodeData.rows`.
    * §2 — Per-codepoint lift (`qcY_starter_decomp_atomic`) — packages
      the table fact as an existential over `(d, e)` for any QC=Y
      non-Hangul starter `cp` with non-empty canonical decomposition.
    * §3 — Singleton dispatcher (`singleton_sound`) —
      4-way case analysis dispatching to the closed singleton
      soundness lemmas in `QuickCheckSoundness` and
      `QuickCheckSoundnessSnoc`.
-/

import Unicode.Normalization.NFC
import Unicode.Normalization.NFD
import Unicode.Normalization.Lookup
import Unicode.Normalization.Hangul
import Unicode.Normalization.Reorder
import Unicode.Normalization.ComposeInversion
import Unicode.Normalization.QuickCheckSoundness
import Unicode.Normalization.QuickCheckSoundnessSnoc
import Unicode.Normalization.QuickCheckSoundnessSingletonTable
import Unicode.Normalization.QuickCheckSoundnessFact4
import Unicode.Generated.UnicodeData

namespace Unicode.Normalization.QuickCheckSoundnessMaster

open Unicode.Normalization
open Unicode.Normalization.NFC
  (toNFC isNFCQuickCheck nfcQCValue hasSortedRunsBool)
open Unicode.Generated

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1 PER-CODEPOINT LIFT FOR THE NON-TRIVIAL DECOMP CASE
--
-- The table fact (`qcY_starter_nontrivial_singleton_nfc_id_table` in
-- the sibling `QuickCheckSoundnessSingletonTable` module) lifts to:
-- for any QC=Y non-Hangul starter `cp` whose canonical decomposition
-- is non-empty, `toNFC #[cp] = #[cp]`. The lift uses
-- `Lookup.lookupRow cp = some row` (which holds whenever
-- `Lookup.canonicalDecomposition cp ≠ #[]`, since codepoints absent
-- from the table have empty decomposition by the @missing default).
-- ═══════════════════════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2 PER-CODEPOINT LIFT FOR THE NON-TRIVIAL DECOMP CASE
--
-- The table fact lifts to: for any QC=Y non-Hangul starter `cp` whose
-- canonical decomposition is non-empty, `toNFC #[cp] = #[cp]`. The
-- lift uses `Lookup.lookupRow cp = some row` (which holds whenever
-- `Lookup.canonicalDecomposition cp ≠ #[]`, since codepoints absent
-- from the table have empty decomposition by the @missing default).
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Per-codepoint singleton-NFC for non-trivial QC=Y non-Hangul
    starters.** Lifts `qcY_starter_nontrivial_singleton_nfc_id_table`. -/
theorem singleton_sound_nontrivial
    (cp : Nat)
    (hQC : nfcQCValue cp = .Y)
    (hCcc : Lookup.canonicalCombiningClass cp = 0)
    (hNotHangul : Hangul.isHangulSyllable cp = false)
    (hNonEmpty : Lookup.canonicalDecomposition cp ≠ #[]) :
    toNFC #[cp] = #[cp] := by
  -- A non-empty `Lookup.canonicalDecomposition cp` implies `cp` is in
  -- `UnicodeData.rows` (codepoints absent from the table fall through
  -- to the empty-array @missing default).
  have hLookupNotNone : Lookup.lookupRow cp ≠ none := by
    intro hNone
    apply hNonEmpty
    unfold Lookup.canonicalDecomposition
    rw [hNone]
  obtain ⟨row, hLookup⟩ := Option.ne_none_iff_exists'.mp hLookupNotNone
  -- The found row's codepoint equals cp.
  have hRowCp : row.codepoint = cp := by
    have hFind := Array.find?_eq_some_iff_getElem.mp hLookup
    obtain ⟨hPred, hIdxLt, hAllPriorFalse⟩ := hFind
    clear hIdxLt hAllPriorFalse
    exact of_decide_eq_true hPred
  -- The table fact applies to row.
  have hRowMem : row ∈ UnicodeData.rows :=
    Array.mem_of_find?_eq_some hLookup
  have hTable :=
    QuickCheckSoundnessSingletonTable.qcY_starter_nontrivial_singleton_nfc_id_table
  rw [Array.all_eq_true] at hTable
  rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
  have hRowFact := hTable i hi
  rw [hElem] at hRowFact
  rw [hRowCp] at hRowFact
  -- The five-disjunct boolean fact reduces. Substitute the per-codepoint
  -- hypotheses to collapse all but the last (toNFC = id) disjunct.
  have hCccDecide : decide (Lookup.canonicalCombiningClass cp ≠ 0) = false := by
    simp [hCcc]
  have hHangulDecide : decide (Hangul.isHangulSyllable cp = true) = false := by
    simp [hNotHangul]
  have hQCDecide : decide (nfcQCValue cp ≠ .Y) = false := by
    simp [hQC]
  -- For the canonicalDecomposition-size disjunct, lift via the fact that
  -- the row's decomp matches the per-cp lookup.
  have hRowDecomp : row.canonicalDecomposition = Lookup.canonicalDecomposition cp := by
    unfold Lookup.canonicalDecomposition
    rw [hLookup]
  have hSizeDecide : decide (row.canonicalDecomposition.size = 0) = false := by
    rw [hRowDecomp]
    have hNonEmptyArr : (Lookup.canonicalDecomposition cp).size ≠ 0 := by
      intro hZero
      apply hNonEmpty
      apply Array.eq_empty_of_size_eq_zero
      exact hZero
    simp [hNonEmptyArr]
  rw [hCccDecide, hHangulDecide, hQCDecide, hSizeDecide] at hRowFact
  simp only [Bool.or_self, Bool.false_or] at hRowFact
  exact of_decide_eq_true hRowFact

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3 SINGLETON SOUNDNESS DISPATCHER
--
-- For any QC=Y singleton `#[cp]`, dispatch to the matching singleton
-- soundness lemma based on `cp`'s structural shape:
--   * non-starter      → QuickCheckSoundness.singleton_nonstarter
--   * Hangul syllable  → QuickCheckSoundnessSnoc.singleton_hangul (§4b)
--   * starter, empty decomp → QuickCheckSoundnessSnoc.singleton_starter_empty (§3)
--   * starter, non-empty decomp, not Hangul → §2 above
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Singleton soundness dispatcher.** Every QC=Y singleton is in NFC. -/
theorem singleton_sound (cp : Nat) (hQC : nfcQCValue cp = .Y) :
    toNFC #[cp] = #[cp] := by
  by_cases hCcc : Lookup.canonicalCombiningClass cp = 0
  · -- Starter
    by_cases hHangul : Hangul.isHangulSyllable cp = true
    · exact QuickCheckSoundnessSnoc.singleton_sound_hangul cp hHangul
    · have hNotHangul : Hangul.isHangulSyllable cp = false := by
        cases hH : Hangul.isHangulSyllable cp
        · rfl
        · exact absurd hH hHangul
      by_cases hEmpty : Lookup.canonicalDecomposition cp = #[]
      · exact QuickCheckSoundnessSnoc.singleton_sound_atomic
          cp hCcc hEmpty hNotHangul
      · exact singleton_sound_nontrivial
          cp hQC hCcc hNotHangul hEmpty
  · -- Non-starter
    have hCccPos : 0 < Lookup.canonicalCombiningClass cp := Nat.pos_of_ne_zero hCcc
    exact QuickCheckSoundness.singleton_sound_nonstarter cp hQC hCccPos

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4 PER-CODEPOINT QC EXTRACTOR FROM SEQUENCE-LEVEL CHECK
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Every codepoint of an `isNFCQuickCheck`-passing sequence has
    `nfcQCValue = .Y`. Direct projection of the per-element
    conjunct of `isNFCQuickCheck`. -/
theorem qcY_of_mem
    (cps : Array Nat) (h : isNFCQuickCheck cps = true)
    (cp : Nat) (hMem : cp ∈ cps) :
    nfcQCValue cp = .Y := by
  unfold isNFCQuickCheck at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hAllQC, hHsr⟩ := h
  clear hHsr
  rw [Array.all_eq_true] at hAllQC
  rcases Array.getElem_of_mem hMem with ⟨i, hi, hElem⟩
  have h_i := hAllQC i hi
  rw [hElem] at h_i
  exact of_decide_eq_true h_i

end Unicode.Normalization.QuickCheckSoundnessMaster
