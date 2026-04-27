/-
  Unicode.Normalization.QuickCheckSoundness

  Soundness of `NFC.isNFCQuickCheck` per UAX #15 §A.1: a YES verdict
  implies the input sequence is already in NFC form.

      isNFCQuickCheck cps = true  →  toNFC cps = cps

  # Strategy

  Snoc induction on `cps.toList`. `ToNFDAppend.toNFD_absorbing_right`
  factors `toNFD (xs ++ #[cp])` via `toNFD (xs ++ toNFD #[cp])`,
  concrete for each shape of `cp` (nonstarter with empty decomp via
  Fact 1, starter with empty decomp, starter with 2-decomp [d, e]
  via Fact 2, or Hangul syllable).

  The compose-side argument closes per sub-case using:
    · Fact 1 lift (`qcY_nonstarter_cp_no_decomp`) — QC=Y nonstarters
      have empty canonical decomposition, so they pass through
      decompose unchanged.
    · Fact 2 lift (`qcY_starter_2decomp_cp_composes`) — QC=Y starters
      with 2-decomp `[d, e]` recompose via `primaryComposite?(d, e)
      = some cp`.
    · Fact 3 lift (`primaryComposite_none_of_qcY_nonstarter`, proven
      below) — no primary composition fires with a QC=Y nonstarter as
      the trailing element.

  Fact 3's per-codepoint lift sits in this module; the other two
  come from `QuickCheckFacts`. The row-level `native_decide` of
  Fact 3 sits in `QuickCheckFacts.qcY_nonstarter_not_decomp_target`.
-/

import Unicode.Normalization.NFC
import Unicode.Normalization.NFD
import Unicode.Normalization.Compose
import Unicode.Normalization.Decompose
import Unicode.Normalization.Reorder
import Unicode.Normalization.Hangul
import Unicode.Normalization.Distribute
import Unicode.Normalization.ToNFDAppend
import Unicode.Normalization.ComposeInversion
import Unicode.Normalization.QuickCheckFacts
import Unicode.Normalization.QuickCheckHangulFacts
import Unicode.Generated.UnicodeData

namespace Unicode.Normalization.QuickCheckSoundness

open Unicode.Normalization
open Unicode.Normalization.NFC
  (toNFC toNFD isNFCQuickCheck hasSortedRunsBool
   hasSortedRunsBool_iff_HasSortedRuns nfcQCValue)
open Unicode.Normalization.QuickCheckFacts
  (qcY_nonstarter_rows_no_decomp qcY_nonstarter_not_decomp_target)
open Unicode.Normalization.QuickCheckHangulFacts
  (vJamo_ccc_zero tJamo_ccc_zero hangulSyllable_ccc_zero)
open Unicode.Generated

-- ═══════════════════════════════════════════════════════════════════════════════
-- §0 PER-CODEPOINT LIFT OF FACT 1
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Per-codepoint fact 1: QC=Y non-starters have no canonical
    decomposition. Lifts `qcY_nonstarter_rows_no_decomp` by case-
    analysis on `Lookup.lookupRow cp`. -/
theorem qcY_nonstarter_cp_no_decomp
    (cp : Nat) (hQC : NFC.nfcQCValue cp = .Y)
    (hCcc : Lookup.canonicalCombiningClass cp > 0) :
    Lookup.canonicalDecomposition cp = #[] := by
  unfold Lookup.canonicalDecomposition
  match hLookup : Lookup.lookupRow cp with
  | none   => rfl
  | some r =>
    have hRowCp : r.codepoint = cp := by
      unfold Lookup.lookupRow at hLookup
      have hFind := Array.find?_eq_some_iff_getElem.mp hLookup
      obtain ⟨hPred, hIdxLt, hAllPriorFalse⟩ := hFind
      clear hIdxLt hAllPriorFalse
      exact of_decide_eq_true hPred
    have hCccEq : r.canonicalCombiningClass = Lookup.canonicalCombiningClass cp := by
      unfold Lookup.canonicalCombiningClass
      rw [hLookup]
    have hRccc : r.canonicalCombiningClass > 0 := by rw [hCccEq]; exact hCcc
    have hRQC : NFC.nfcQCValue r.codepoint = .Y := by rw [hRowCp]; exact hQC
    have hMem : r ∈ UnicodeData.rows := by
      unfold Lookup.lookupRow at hLookup
      exact Array.mem_of_find?_eq_some hLookup
    have hAll : UnicodeData.rows.all (fun r =>
      (! (decide (NFC.nfcQCValue r.codepoint = .Y) &&
          decide (r.canonicalCombiningClass > 0))) ||
      decide (r.canonicalDecomposition = #[])) = true :=
      qcY_nonstarter_rows_no_decomp
    rw [Array.all_eq_true] at hAll
    rcases Array.getElem_of_mem hMem with ⟨i, hi, hIEq⟩
    have hThis := hAll i hi
    rw [hIEq] at hThis
    simp only [Bool.or_eq_true] at hThis
    rcases hThis with hNot | hEmpty
    · -- hNot : (! (decide qcY && decide cccPos)) = true. Both decides are
      -- true (by hRQC and hRccc), so the inner conjunction is `true`,
      -- making `! true = false` — contradicting hNot.
      exfalso
      have h1 : decide (NFC.nfcQCValue r.codepoint = .Y) = true :=
        decide_eq_true hRQC
      have h2 : decide (r.canonicalCombiningClass > 0) = true :=
        decide_eq_true hRccc
      rw [h1, h2] at hNot
      exact Bool.noConfusion hNot
    · exact of_decide_eq_true hEmpty

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1 HANGUL HELPERS FOR FACT 3 PER-CODEPOINT LIFT
--
-- The `primaryComposite?` function dispatches on `Hangul.composePair?`
-- first. When the trailing element `e` is a nonstarter (CCC > 0), the
-- Hangul branch must return `none` because Hangul composition only
-- fires with V-jamo or T-jamo as the trailing element, and both those
-- classes are starters (CCC = 0). The three table-scale `native_decide`
-- facts (V-jamo, T-jamo, Hangul syllable) live in the sibling module
-- `QuickCheckHangulFacts` so the heavy compilation isolates cleanly
-- under `LEAN_NUM_THREADS=1`. The pointwise lifts below consume those
-- facts.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Pointwise lift of `vJamo_ccc_zero`. -/
theorem vJamo_ccc_zero_cp (cp : Nat) (h : Hangul.isVJamo cp = true) :
    Lookup.canonicalCombiningClass cp = 0 := by
  have hRange : Hangul.VBase ≤ cp ∧ cp < Hangul.VBase + Hangul.VCount := by
    unfold Hangul.isVJamo at h
    exact of_decide_eq_true h
  have hIdxLt : cp - Hangul.VBase < Hangul.VCount := by omega
  have hCpEq : Hangul.VBase + (cp - Hangul.VBase) = cp := by omega
  have hTable := vJamo_ccc_zero
  rw [List.all_eq_true] at hTable
  have hMem : cp - Hangul.VBase ∈ List.range Hangul.VCount :=
    List.mem_range.mpr hIdxLt
  have hAt := hTable (cp - Hangul.VBase) hMem
  rw [hCpEq] at hAt
  exact of_decide_eq_true hAt

/-- Pointwise lift of `tJamo_ccc_zero`. -/
theorem tJamo_ccc_zero_cp (cp : Nat) (h : Hangul.isTJamo cp = true) :
    Lookup.canonicalCombiningClass cp = 0 := by
  have hRange : Hangul.TBase < cp ∧ cp < Hangul.TBase + Hangul.TCount := by
    unfold Hangul.isTJamo at h
    exact of_decide_eq_true h
  have hIdxLt : cp - (Hangul.TBase + 1) < Hangul.TCount - 1 := by omega
  have hCpEq : Hangul.TBase + 1 + (cp - (Hangul.TBase + 1)) = cp := by omega
  have hTable := tJamo_ccc_zero
  rw [List.all_eq_true] at hTable
  have hMem : cp - (Hangul.TBase + 1) ∈ List.range (Hangul.TCount - 1) :=
    List.mem_range.mpr hIdxLt
  have hAt := hTable (cp - (Hangul.TBase + 1)) hMem
  rw [hCpEq] at hAt
  exact of_decide_eq_true hAt

/-- Pointwise lift of `hangulSyllable_ccc_zero`: every Hangul syllable
    has CCC = 0. Consequence: a QC=Y nonstarter (CCC > 0) cannot be
    a Hangul syllable. -/
theorem hangulSyllable_ccc_zero_cp (cp : Nat)
    (h : Hangul.isHangulSyllable cp = true) :
    Lookup.canonicalCombiningClass cp = 0 := by
  have hRange : Hangul.SBase ≤ cp ∧ cp < Hangul.SBase + Hangul.SCount := by
    unfold Hangul.isHangulSyllable at h
    exact of_decide_eq_true h
  have hIdxLt : cp - Hangul.SBase < Hangul.SCount := by omega
  have hCpEq : Hangul.SBase + (cp - Hangul.SBase) = cp := by omega
  have hTable := hangulSyllable_ccc_zero
  rw [List.all_eq_true] at hTable
  have hMem : cp - Hangul.SBase ∈ List.range Hangul.SCount :=
    List.mem_range.mpr hIdxLt
  have hAt := hTable (cp - Hangul.SBase) hMem
  rw [hCpEq] at hAt
  exact of_decide_eq_true hAt

/-- Hangul composition never fires with a nonstarter trailing element.
    `composePair?` succeeds only on (L, V) or (LV-syllable, T) pairs;
    V-jamo and T-jamo are both starters (CCC = 0), contradicting the
    hypothesis `0 < CCC(e)`. -/
theorem hangul_composePair_none_of_nonstarter
    (st e : Nat) (hCcc : 0 < Lookup.canonicalCombiningClass e) :
    Hangul.composePair? st e = none := by
  unfold Hangul.composePair?
  split
  · next hLV =>
    exfalso
    have hV : Hangul.isVJamo e = true := hLV.2
    have hCccZero : Lookup.canonicalCombiningClass e = 0 := vJamo_ccc_zero_cp e hV
    omega
  · split
    · next hLVT =>
      exfalso
      have hT : Hangul.isTJamo e = true := hLVT.2
      have hCccZero : Lookup.canonicalCombiningClass e = 0 := tJamo_ccc_zero_cp e hT
      omega
    · rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2 FACT 3 PER-CODEPOINT LIFT
--
-- Canonical composition never fires when the trailing element is a
-- QC=Y nonstarter. The per-codepoint form of the row-level
-- `qcY_nonstarter_not_decomp_target`.
--
-- Same proof idiom as `Compose.compose_preserves_non_widthCompatSource`
-- at `Compose.lean:298-310`: case-split on the `findSome?` result;
-- the `some` branch contradicts the row-level fact.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Fact 3 per-codepoint lift.** No canonical composition fires with
    a QC=Y nonstarter as the trailing element. -/
theorem primaryComposite_none_of_qcY_nonstarter
    (st e : Nat)
    (hQC : nfcQCValue e = .Y)
    (hCcc : 0 < Lookup.canonicalCombiningClass e) :
    Compose.primaryComposite? st e = none := by
  unfold Compose.primaryComposite?
  rw [hangul_composePair_none_of_nonstarter st e hCcc]
  -- The `match none with ...` reduces to the `none` branch: the findSome?
  -- call. Force that reduction with `show` so the subsequent case split
  -- is over an Option at the surface, not inside a match wrapper.
  show UnicodeData.rows.findSome? (fun r =>
      if r.canonicalDecomposition = #[st, e]
         ∧ ¬ Lookup.isFullCompositionExclusion r.codepoint then
        some r.codepoint
      else none) = none
  -- Case-split: either findSome? already returned `none` (closed
  -- immediately), or it returned `some p` — in which case Fact 3's
  -- row-level fact yields a contradiction.
  generalize hFind : UnicodeData.rows.findSome? (fun r =>
      if r.canonicalDecomposition = #[st, e]
         ∧ ¬ Lookup.isFullCompositionExclusion r.codepoint then
        some r.codepoint
      else none) = result
  cases result with
  | none => rfl
  | some p =>
    exfalso
    obtain ⟨row, hRowMem, hFEq⟩ := Array.exists_of_findSome?_eq_some hFind
    have hAll := qcY_nonstarter_not_decomp_target
    rw [Array.all_eq_true] at hAll
    rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
    have hRow := hAll i hi
    rw [hElem] at hRow
    split at hFEq
    · next hCond =>
      obtain ⟨hDecomp, hNotExc⟩ := hCond
      -- The 3-disjunct boolean fact (! size=2) || (excl=true) || (! qcY) = true.
      -- After substituting hDecomp (so size and the trailing element reduce to
      -- closed forms 2 and e) and hQC (so nfcQCValue at e is .Y), the first and
      -- third disjuncts collapse to `false`. The remaining disjunct is
      -- `decide (excl = true) = true`, which yields `excl = true` via
      -- `of_decide_eq_true`, contradicting hNotExc.
      simp [hDecomp, hQC] at hRow
      exact hNotExc hRow
    · nomatch hFEq

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3 MAIN SOUNDNESS PROOF — EMPTY CASE + SINGLETON NONSTARTER CASE
--
-- Base-case building blocks of the full soundness induction. They
-- cover `cps = #[]` and `cps = #[cp]` where cp is a QC=Y nonstarter.
-- Both follow directly from `decomposeSequence` unfolds, `reorder`'s
-- identity on ≤1-element input, and Fact 3 for `compose` in the
-- nonstarter case.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Empty case of soundness.** Trivial; every stage maps `#[]` to `#[]`. -/
theorem empty_sound :
    toNFC (#[] : Array Nat) = #[] := by
  native_decide

/-- **Singleton nonstarter case.** A single QC=Y nonstarter codepoint is in
    NFC form. `decomposeSequence #[cp] = fullCanonicalDecompose cp = #[cp]`
    by Fact 1. `reorder #[cp] = #[cp]` on a single element. `compose #[cp]`
    treats cp as a leading nonstarter (no prior starter), emitting it to
    `emitted` unchanged. -/
theorem singleton_sound_nonstarter
    (cp : Nat)
    (hQC : nfcQCValue cp = .Y)
    (hCcc : 0 < Lookup.canonicalCombiningClass cp) :
    toNFC #[cp] = #[cp] := by
  -- Decompose: Fact 1 gives empty canonical decomposition, and cp is
  -- not a Hangul syllable (Hangul syllables have CCC = 0, contradicting
  -- the nonstarter hypothesis).
  have hDecomp : Lookup.canonicalDecomposition cp = #[] :=
    qcY_nonstarter_cp_no_decomp cp hQC hCcc
  have hNotHangul : Hangul.isHangulSyllable cp = false := by
    -- Hangul syllables have CCC = 0 (hangulSyllable_ccc_zero_cp), which
    -- contradicts the nonstarter hypothesis.
    cases h : Hangul.isHangulSyllable cp with
    | false => rfl
    | true =>
      exfalso
      have := hangulSyllable_ccc_zero_cp cp h
      omega
  -- fullCanonicalDecompose cp reduces to #[cp] under empty decomp + not Hangul.
  have hFCD : Decompose.fullCanonicalDecompose cp = #[cp] := by
    have hDsyl : Hangul.decomposeSyllable? cp = none := by
      unfold Hangul.decomposeSyllable?
      rw [hNotHangul]
      simp
    show Decompose.fullCanonicalDecomposeFuel Decompose.maxDepth cp = #[cp]
    unfold Decompose.maxDepth Decompose.fullCanonicalDecomposeFuel
    rw [hDsyl]
    simp [hDecomp]
  -- Pipeline: decomposeSequence #[cp] = #[cp].
  have hDS : Decompose.decomposeSequence #[cp] = #[cp] := by
    rw [Distribute.decomposeSequence_singleton]
    exact hFCD
  -- Reorder: #[cp] → #[cp] (single element, trivially HSR).
  have hR : Reorder.reorder #[cp] = #[cp] := by
    apply Reorder.reorder_id_on_HasSortedRuns
    show Reorder.HasSortedRuns [cp]
    trivial
  -- Compose on a single nonstarter: no active starter, CCC > 0 → emit to
  -- `emitted`, then flush the empty `starter` + empty buffer.
  show Compose.compose (toNFD #[cp]) = #[cp]
  unfold toNFD
  rw [hDS, hR]
  -- compose #[cp] folds stepCompose once from initialState. The CCC>0
  -- hypothesis selects the nonstarter branch of the `starter=none` case:
  -- emit cp, state becomes { emitted := #[cp], starter := none, ... }.
  -- flushCompose with starter=none returns emitted ++ buffer.reverse = #[cp].
  unfold Compose.compose Compose.flushCompose Compose.stepCompose Compose.initialState
  have hCccNe : ¬ Lookup.canonicalCombiningClass cp = 0 := by omega
  simp [hCccNe]

end Unicode.Normalization.QuickCheckSoundness
