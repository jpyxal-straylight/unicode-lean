/-
  Unicode.Normalization.QuickCheckSoundnessSnocClosure

  Closes the master soundness theorem of `isNFCQuickCheck` (UAX
  #15 §A.1) via a two-shape dispatcher over the snoc element's CCC
  class.

    * Starter (CCC = 0): `nfc_snoc_qcY_starter` — `singleton_sound`
      gives `toNFC #[cp] = #[cp]` for any QC=Y starter regardless
      of decomposition shape (atomic, Hangul, size-2, or
      recursively-chained size-2);
      `compose_qcY_starter_block_additive` factors `compose` over
      the snoc boundary; `reorder_append_starter_middle` factors
      `toNFD` over the same boundary.
    * Non-starter (CCC > 0):
      `nfc_snoc_qcY_nonstarter_structural` — `compose_slide_qcY`
      (`ComposeNonstarterSlide`) discharges the swap step via state-
      machine equivariance; the buffer-bound
      `compose_buffer_ccc_bound` and chain-validity
      `chain_fires_via_buffer_bound` come from
      `ComposeBufferStructure`.

  Two `native_decide` UCD tables establish the structural premise
  that for any QC=Y starter `cp`, the head of `decomposeSequence
  #[cp]` is a starter and the head of `toNFD #[cp]` is a QC=Y
  starter — the precondition of `compose_qcY_starter_block_additive`:

    * `qcY_starter_toNFD_head_table` covers explicit UCD rows.
    * `hangul_singleton_toNFD_head_table` covers the 11172
      precomposed Hangul syllables (which are filtered out of
      `UnicodeData.rows` since their decomposition is algorithmic).
-/

import Unicode.Normalization.QuickCheckSoundnessSnoc
import Unicode.Normalization.QuickCheckSoundness
import Unicode.Normalization.QuickCheckSoundnessMaster
import Unicode.Normalization.ComposeBlockAdditive
import Unicode.Normalization.ComposeNonstarterSlide
import Unicode.Normalization.ComposeBufferStructure
import Unicode.Normalization.ComposeKernelSupport
import Unicode.Normalization.NFC
import Unicode.Normalization.ReorderAppend
import Unicode.Normalization.Distribute
import Unicode.Generated.UnicodeData

namespace Unicode.Normalization.QuickCheckSoundnessSnocClosure

open Unicode.Normalization
open Unicode.Normalization.NFC (toNFC toNFD isNFCQuickCheck nfcQCValue)
open Unicode.Normalization.QuickCheckSoundness
  (qcY_nonstarter_cp_no_decomp hangulSyllable_ccc_zero_cp)
open Unicode.Normalization.QuickCheckSoundnessMaster (singleton_sound)
open Unicode.Normalization.ComposeBlockAdditive
  (compose_qcY_starter_block_additive compose_qcY_linear)
open Unicode.Normalization.ComposeNonstarterSlide
  (PrimaryFiresChain compose_slide_qcY)
open Unicode.Normalization.ComposeBufferStructure
  (compose_buffer_ccc_bound chain_fires_via_buffer_bound)
open Unicode.Normalization.ComposeKernelSupport
  (foldl_stepCompose_starter_isSome_persists
   foldl_stepCompose_starter_isSome_of_member
   getLast?_concat_singleton
   decomp_atomic_id
   trailingLow trailingHigh
   trailingLow_append_trailingHigh
   trailingHigh_all_gt
   trailingHigh_all_pos
   trailingLow_last_le_when_high_nonempty
   HasSortedRuns_left_of_concat
   HasSortedRuns_right_of_concat
   HasSortedRuns_append_singleton
   HasSortedRuns_concat
   trailingHigh_nonempty_in_swap_case
   lowL_has_starter_in_swap_case
   nfc_snoc_atomic_nonstarter_hsr_preserves)
open Unicode.Generated

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1 UCD TABLE: NON-HANGUL toNFD HEAD IS QC=Y STARTER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- For every QC=Y starter row in `UnicodeData.rows`, the head of
    `decomposeSequence #[cp]` is a starter and the head of `toNFD
    #[cp]` is a QC=Y starter. Closed by `native_decide`; the two
    early-exit disjuncts skip rows outside the QC=Y starter sub-class. -/
theorem qcY_starter_toNFD_head_table :
    UnicodeData.rows.all (fun row =>
      decide (row.canonicalCombiningClass ≠ 0) ||
      decide (nfcQCValue row.codepoint ≠ .Y) ||
      (decide (Lookup.canonicalCombiningClass
                  (Decompose.decomposeSequence #[row.codepoint])[0]! = 0) &&
       decide (Lookup.canonicalCombiningClass
                  (toNFD #[row.codepoint])[0]! = 0) &&
       decide (nfcQCValue (toNFD #[row.codepoint])[0]! = .Y) &&
       decide ((Decompose.decomposeSequence #[row.codepoint]).size > 0) &&
       decide ((toNFD #[row.codepoint]).size > 0))) = true := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2 HANGUL TABLE: PRECOMPOSED-SYLLABLE toNFD HEAD IS QC=Y STARTER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- For every Hangul precomposed syllable `cp` in `[SBase, SBase +
    SCount)`, the head of `decomposeSequence #[cp]` is a starter
    (the L jamo) and the head of `toNFD #[cp]` is a QC=Y starter.
    Hangul syllables are excluded from `UnicodeData.rows` (their
    decomposition is algorithmic, handled via `decomposeSyllable?`),
    so this table covers the dispatcher's Hangul branch. -/
theorem hangul_singleton_toNFD_head_table :
    (List.range Hangul.SCount).all (fun i =>
      decide (Lookup.canonicalCombiningClass
                (Decompose.decomposeSequence #[Hangul.SBase + i])[0]! = 0) &&
      decide (Lookup.canonicalCombiningClass
                (toNFD #[Hangul.SBase + i])[0]! = 0) &&
      decide (nfcQCValue (toNFD #[Hangul.SBase + i])[0]! = .Y) &&
      decide ((Decompose.decomposeSequence #[Hangul.SBase + i]).size > 0) &&
      decide ((toNFD #[Hangul.SBase + i]).size > 0))
    = true := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3 PER-CODEPOINT LIFT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- For any QC=Y starter `cp`, `decomposeSequence #[cp]` is non-empty
    and starter-led, and `toNFD #[cp]` is non-empty with a QC=Y
    starter head. Three sources cover the cases:

      * Hangul precomposed syllables — `hangul_singleton_toNFD_head_table`.
      * Non-Hangul starters in `UnicodeData.rows` —
        `qcY_starter_toNFD_head_table`.
      * Non-Hangul atomic starters (codepoints absent from the pinned
        UCD subset, with implicit empty canonical decomposition) —
        direct: `decomposeSequence #[cp] = #[cp] = toNFD #[cp]`. -/
theorem qcY_starter_toNFD_head
    (cp : Nat)
    (hQC : nfcQCValue cp = .Y)
    (hCcc : Lookup.canonicalCombiningClass cp = 0) :
    Lookup.canonicalCombiningClass
        (Decompose.decomposeSequence #[cp])[0]! = 0 ∧
    Lookup.canonicalCombiningClass (toNFD #[cp])[0]! = 0 ∧
    nfcQCValue (toNFD #[cp])[0]! = .Y ∧
    (Decompose.decomposeSequence #[cp]).size > 0 ∧
    (toNFD #[cp]).size > 0 := by
  by_cases hHangul : Hangul.isHangulSyllable cp = true
  · have hRange : Hangul.SBase ≤ cp ∧ cp < Hangul.SBase + Hangul.SCount := by
      unfold Hangul.isHangulSyllable at hHangul
      exact of_decide_eq_true hHangul
    have hIdxLt : cp - Hangul.SBase < Hangul.SCount := by omega
    have hCpEq : Hangul.SBase + (cp - Hangul.SBase) = cp := by omega
    have hTable := hangul_singleton_toNFD_head_table
    rw [List.all_eq_true] at hTable
    have hMem : cp - Hangul.SBase ∈ List.range Hangul.SCount :=
      List.mem_range.mpr hIdxLt
    have hAt := hTable (cp - Hangul.SBase) hMem
    rw [hCpEq] at hAt
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        Bool.and_eq_true] at hAt
    obtain ⟨⟨⟨⟨hDsHead, hNfdHead⟩, hNfdQC⟩, hDsNonEmpty⟩, hNfdNonEmpty⟩ := hAt
    exact ⟨of_decide_eq_true hDsHead, of_decide_eq_true hNfdHead,
           of_decide_eq_true hNfdQC, of_decide_eq_true hDsNonEmpty,
           of_decide_eq_true hNfdNonEmpty⟩
  · have hNotHangul : Hangul.isHangulSyllable cp = false := by
      cases hH : Hangul.isHangulSyllable cp
      · rfl
      · exact absurd hH hHangul
    cases hLookup : Lookup.lookupRow cp with
    | none =>
      have hDecomp : Lookup.canonicalDecomposition cp = #[] := by
        unfold Lookup.canonicalDecomposition; rw [hLookup]
      have hDsyl : Hangul.decomposeSyllable? cp = none := by
        unfold Hangul.decomposeSyllable?
        rw [hNotHangul]
        simp
      have hFCD : Decompose.fullCanonicalDecompose cp = #[cp] := by
        show Decompose.fullCanonicalDecomposeFuel Decompose.maxDepth cp = #[cp]
        unfold Decompose.maxDepth Decompose.fullCanonicalDecomposeFuel
        rw [hDsyl]
        simp [hDecomp]
      have hDS : Decompose.decomposeSequence #[cp] = #[cp] := by
        rw [Distribute.decomposeSequence_singleton]
        exact hFCD
      have hToNFD : toNFD #[cp] = #[cp] := by
        unfold toNFD
        rw [hDS]
        apply Reorder.reorder_id_on_HasSortedRuns
        show Reorder.HasSortedRuns [cp]
        trivial
      refine ⟨?h1, ?h2, ?h3, ?h4, ?h5⟩
      · rw [hDS]; simp; exact hCcc
      · rw [hToNFD]; simp; exact hCcc
      · rw [hToNFD]; simp; exact hQC
      · rw [hDS]; simp
      · rw [hToNFD]; simp
    | some row =>
      have hRowCp : row.codepoint = cp := by
        have hFind := Array.find?_eq_some_iff_getElem.mp hLookup
        obtain ⟨hPred, hIdxLt, hAllPriorFalse⟩ := hFind
        clear hIdxLt hAllPriorFalse
        exact of_decide_eq_true hPred
      have hRccc :
          row.canonicalCombiningClass = Lookup.canonicalCombiningClass cp := by
        unfold Lookup.canonicalCombiningClass; rw [hLookup]
      have hRowMem : row ∈ UnicodeData.rows :=
        Array.mem_of_find?_eq_some hLookup
      have hTable := qcY_starter_toNFD_head_table
      rw [Array.all_eq_true] at hTable
      rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
      have hRowFact := hTable i hi
      rw [hElem] at hRowFact
      have hCccDecide : decide (row.canonicalCombiningClass ≠ 0) = false := by
        rw [hRccc]; simp [hCcc]
      have hQCDecide : decide (nfcQCValue row.codepoint ≠ .Y) = false := by
        rw [hRowCp]; simp [hQC]
      rw [hCccDecide, hQCDecide] at hRowFact
      simp only [Bool.or_self, Bool.false_or] at hRowFact
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
          Bool.and_eq_true] at hRowFact
      obtain ⟨⟨⟨⟨hDsHead, hNfdHead⟩, hNfdQC⟩, hDsNonEmpty⟩, hNfdNonEmpty⟩ :=
        hRowFact
      rw [hRowCp] at hDsHead hNfdHead hNfdQC hDsNonEmpty hNfdNonEmpty
      exact ⟨of_decide_eq_true hDsHead, of_decide_eq_true hNfdHead,
             of_decide_eq_true hNfdQC, of_decide_eq_true hDsNonEmpty,
             of_decide_eq_true hNfdNonEmpty⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4 REORDER FACTORS OVER A STARTER-LED RIGHT BLOCK
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `reorder` distributes over `X ++ Y` when `Y` is non-empty with a
    starter head: factoring `Y = #[Y[0]] ++ Y_tail` and applying
    `reorder_append_starter_middle` once to the (X, head, tail)
    triple and once to the (∅, head, tail) triple. -/
theorem reorder_append_starter_led
    (X : Array Nat) (head : Nat) (tail : List Nat)
    (hHead : Lookup.canonicalCombiningClass head = 0) :
    Reorder.reorder (X ++ (head :: tail).toArray) =
      Reorder.reorder X ++ Reorder.reorder (head :: tail).toArray := by
  have hYEq : ((head :: tail).toArray : Array Nat) = #[head] ++ tail.toArray := by
    apply Array.toList_inj.mp
    rw [List.toList_toArray]
    rw [Array.toList_append, List.toList_toArray]
    rfl
  have hReorderEmpty : Reorder.reorder (#[] : Array Nat) = #[] := by
    apply Reorder.reorder_id_on_HasSortedRuns
    show Reorder.HasSortedRuns []
    trivial
  -- The right block reorder factors at its leading starter.
  have hReorderRight :
      Reorder.reorder (#[head] ++ tail.toArray)
        = #[head] ++ Reorder.reorder tail.toArray := by
    have hStep := ReorderAppend.reorder_append_starter_middle
                    (#[] : Array Nat) head tail.toArray hHead
    -- hStep: reorder (∅ ++ #[head] ++ tail.toArray)
    --        = reorder ∅ ++ #[head] ++ reorder tail.toArray.
    rw [Array.empty_append, hReorderEmpty, Array.empty_append] at hStep
    exact hStep
  rw [hYEq, hReorderRight]
  rw [← Array.append_assoc]
  rw [ReorderAppend.reorder_append_starter_middle X head tail.toArray hHead]
  rw [Array.append_assoc]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §5 toNFD DISTRIBUTES OVER SNOC AT A STARTER BOUNDARY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- For any QC=Y starter `cp`, `toNFD` distributes over the snoc-
    extension boundary: the decomposition+reorder of `xs ++ #[cp]`
    factors as `toNFD xs ++ toNFD #[cp]`. The factoring uses
    `decomposeSequence_append` (decomposition is array-additive) and
    `reorder_append_starter_led` (starter-led right block). -/
theorem toNFD_snoc_qcY_starter
    (xs : Array Nat) (cp : Nat)
    (hQC : nfcQCValue cp = .Y)
    (hCcc : Lookup.canonicalCombiningClass cp = 0) :
    toNFD (xs ++ #[cp]) = toNFD xs ++ toNFD #[cp] := by
  obtain ⟨hDsHead, _hNfdHead, _hNfdQC, hDsNonEmpty, _hNfdNonEmpty⟩ :=
    qcY_starter_toNFD_head cp hQC hCcc
  cases hL : (Decompose.decomposeSequence #[cp]).toList with
  | nil =>
    exfalso
    have hSize : (Decompose.decomposeSequence #[cp]).size = 0 := by
      rw [← Array.length_toList, hL]; rfl
    omega
  | cons head tail =>
    have hDArr :
        Decompose.decomposeSequence #[cp] = (head :: tail).toArray := by
      apply Array.toList_inj.mp
      rw [hL]
    have hHeadCcc : Lookup.canonicalCombiningClass head = 0 := by
      have hHeadEq : (Decompose.decomposeSequence #[cp])[0]! = head := by
        rw [hDArr]; simp
      rw [← hHeadEq]
      exact hDsHead
    unfold toNFD
    rw [Distribute.decomposeSequence_append xs #[cp]]
    rw [hDArr]
    rw [reorder_append_starter_led (Decompose.decomposeSequence xs)
          head tail hHeadCcc]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §6 STARTER SNOC CLOSURE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Snoc closure for any QC=Y starter `cp` (regardless of decomposition
    shape: atomic, Hangul, size-2, or chained). Uses `toNFD_snoc_qcY_starter`
    to factor `toNFD` over the boundary, then `compose_qcY_starter_block_additive`
    to factor `compose`, and finally `singleton_sound` for the singleton
    round-trip. -/
theorem nfc_snoc_qcY_starter
    (xs : Array Nat) (cp : Nat)
    (hQC : nfcQCValue cp = .Y)
    (hCcc : Lookup.canonicalCombiningClass cp = 0)
    (hPrefix : toNFC xs = xs) :
    toNFC (xs ++ #[cp]) = xs ++ #[cp] := by
  obtain ⟨_hDsHead, hNfdHead, hNfdQC, _hDsNonEmpty, _hNfdNonEmpty⟩ :=
    qcY_starter_toNFD_head cp hQC hCcc
  have hSingleton : toNFC #[cp] = #[cp] := singleton_sound cp hQC
  have hToNFDSnoc : toNFD (xs ++ #[cp]) = toNFD xs ++ toNFD #[cp] :=
    toNFD_snoc_qcY_starter xs cp hQC hCcc
  -- Pattern-match `toNFD #[cp]` via `toList` to expose head + tail in
  -- list form, matching `compose_qcY_starter_block_additive_list`.
  cases hL : (toNFD #[cp]).toList with
  | nil =>
    exfalso
    have hSize : (toNFD #[cp]).size = 0 := by
      rw [← Array.length_toList, hL]; rfl
    have hHeadEq : (toNFD #[cp])[0]! = (default : Nat) := by
      rw [Array.getElem!_eq_getD]
      simp [Array.getD, hSize]
    rw [hHeadEq] at hNfdQC
    -- `default = 0` and `nfcQCValue 0 = .Y`, so this branch is consistent
    -- with the per-cp lift; need a different contradiction route.
    -- Use the explicit `_hNfdNonEmpty` from the lift.
    obtain ⟨_, _, _, _, hNfdSize⟩ := qcY_starter_toNFD_head cp hQC hCcc
    omega
  | cons head tail =>
    have hToNFDArr : toNFD #[cp] = (head :: tail).toArray := by
      apply Array.toList_inj.mp
      rw [hL]
    have hHeadEqBang : (toNFD #[cp])[0]! = head := by
      rw [hToNFDArr]; simp
    rw [hHeadEqBang] at hNfdHead hNfdQC
    show Compose.compose (toNFD (xs ++ #[cp])) = xs ++ #[cp]
    rw [hToNFDSnoc, hToNFDArr]
    -- `compose ((toNFD xs) ++ (head :: tail).toArray)` factors via
    -- `compose_qcY_starter_block_additive_list`.
    show Compose.flushCompose
            ((toNFD xs ++ (head :: tail).toArray).foldl
                Compose.stepCompose Compose.initialState) = xs ++ #[cp]
    rw [Array.foldl_append]
    have hListEq :
        ((head :: tail).toArray.foldl Compose.stepCompose
            ((toNFD xs).foldl Compose.stepCompose Compose.initialState))
        = (head :: tail).foldl Compose.stepCompose
            ((toNFD xs).foldl Compose.stepCompose Compose.initialState) := by
      rw [← Array.foldl_toList]
    rw [hListEq]
    rw [Unicode.Normalization.ComposeBlockAdditive.compose_qcY_starter_block_additive_list
          (toNFD xs) head tail hNfdHead hNfdQC]
    show Compose.compose (toNFD xs)
       ++ Compose.flushCompose
            ((head :: tail).foldl Compose.stepCompose Compose.initialState)
        = xs ++ #[cp]
    -- The right factor reduces to `compose (toNFD #[cp])` via array-list
    -- foldl conversion.
    have hRightEq :
        Compose.flushCompose
            ((head :: tail).foldl Compose.stepCompose Compose.initialState)
        = Compose.compose (toNFD #[cp]) := by
      show Compose.flushCompose
              ((head :: tail).foldl Compose.stepCompose Compose.initialState)
          = Compose.flushCompose
              ((toNFD #[cp]).foldl Compose.stepCompose Compose.initialState)
      rw [hToNFDArr]
      rw [← Array.foldl_toList]
    rw [hRightEq]
    show toNFC xs ++ toNFC #[cp] = xs ++ #[cp]
    rw [hPrefix, hSingleton]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §8 STRUCTURAL ATOMIC-NONSTARTER SNOC
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Atomic-nonstarter snoc closure.** The slide step
    `compose (lowL ++ #[cp] ++ highL) = compose (lowL ++ highL ++
    #[cp])` is discharged by `compose_slide_qcY`
    (`ComposeNonstarterSlide`); chain validity for the high part is
    derived from the buffer-bound on `lowL ++ highL` via
    `chain_fires_via_buffer_bound` (`ComposeBufferStructure`). -/
theorem nfc_snoc_qcY_nonstarter_structural
    (xs : Array Nat) (cp : Nat)
    (hQC : nfcQCValue cp = .Y)
    (hCp_ccc_pos : 0 < Lookup.canonicalCombiningClass cp)
    (hDecomp : Lookup.canonicalDecomposition cp = #[])
    (hNotHangul : Hangul.isHangulSyllable cp = false)
    (hPrefix : toNFC xs = xs)
    (hQCSnoc : NFC.isNFCQuickCheck (xs ++ #[cp]) = true) :
    toNFC (xs ++ #[cp]) = xs ++ #[cp] := by
  have hHSR_outer : NFC.hasSortedRunsBool (xs ++ #[cp]).toList = true := by
    unfold NFC.isNFCQuickCheck at hQCSnoc
    rw [Bool.and_eq_true] at hQCSnoc
    exact hQCSnoc.2
  by_cases hHSR_inner : NFC.hasSortedRunsBool (toNFD xs ++ #[cp]).toList = true
  · have hHSR_prop : Reorder.HasSortedRuns (toNFD xs ++ #[cp]).toList :=
      (NFC.hasSortedRunsBool_iff_HasSortedRuns
        (toNFD xs ++ #[cp]).toList).mp hHSR_inner
    exact nfc_snoc_atomic_nonstarter_hsr_preserves
      xs cp hQC hCp_ccc_pos hDecomp hNotHangul hHSR_prop hPrefix
  · -- Swap variant: partition `toNFD xs` at the cp-CCC threshold,
    -- derive chain validity for the high part, and apply the slide.
    have hCpCcc : Lookup.canonicalCombiningClass cp ≠ 0 :=
      Nat.pos_iff_ne_zero.mp hCp_ccc_pos
    have hFCD : Decompose.fullCanonicalDecompose cp = #[cp] :=
      decomp_atomic_id cp hDecomp hNotHangul
    have hZ_HSR : Reorder.HasSortedRuns (toNFD xs).toList :=
      (NFD.toNFD_output_HSR_and_FullyDecomposed xs).1
    obtain ⟨lowL, hLowEq⟩ :
        ∃ lowL, lowL =
          trailingLow
            (toNFD xs).toList (Lookup.canonicalCombiningClass cp) :=
      ⟨_, rfl⟩
    obtain ⟨highL, hHighEq⟩ :
        ∃ highL, highL =
          trailingHigh
            (toNFD xs).toList (Lookup.canonicalCombiningClass cp) :=
      ⟨_, rfl⟩
    have hPartition : (toNFD xs).toList = lowL ++ highL := by
      rw [hLowEq, hHighEq]
      exact (trailingLow_append_trailingHigh
              (toNFD xs).toList (Lookup.canonicalCombiningClass cp)).symm
    have hHighNonEmpty : highL ≠ [] := by
      rw [hHighEq]
      exact trailingHigh_nonempty_in_swap_case
              xs cp hHSR_inner
    have hHighPos : ∀ b ∈ highL, 0 < Lookup.canonicalCombiningClass b := by
      intros b hb
      rw [hHighEq] at hb
      exact trailingHigh_all_pos
              (toNFD xs).toList (Lookup.canonicalCombiningClass cp) b hb
    have hHighGt : ∀ b ∈ highL,
                      Lookup.canonicalCombiningClass cp
                        < Lookup.canonicalCombiningClass b := by
      intros b hb
      rw [hHighEq] at hb
      exact trailingHigh_all_gt
              (toNFD xs).toList (Lookup.canonicalCombiningClass cp) b hb
    have hLowHasStarter : ∃ s ∈ lowL, Lookup.canonicalCombiningClass s = 0 := by
      rw [hLowEq]
      exact lowL_has_starter_in_swap_case
              xs cp hCp_ccc_pos hPrefix hHSR_outer hHSR_inner
    have hLowStarter :
        (lowL.toArray.foldl Compose.stepCompose Compose.initialState).starter.isSome
          = true := by
      rw [← Array.foldl_toList, List.toList_toArray]
      exact foldl_stepCompose_starter_isSome_of_member
              lowL Compose.initialState hLowHasStarter
    -- Reshape `toNFD xs ++ #[cp]` to `lowL ++ highL ++ #[cp]`, then
    -- commute `cp` past `highL` via reorder's strict-max-multi
    -- lemma so that `reorder` becomes the identity on the inserted
    -- `lowL ++ #[cp] ++ highL`.
    show Compose.compose (toNFD (xs ++ #[cp])) = xs ++ #[cp]
    have hToNFD_snoc : toNFD (xs ++ #[cp])
                      = Reorder.reorder (toNFD xs ++ #[cp]) := by
      unfold toNFD
      rw [Distribute.decomposeSequence_append xs #[cp]]
      rw [Distribute.decomposeSequence_singleton, hFCD]
      exact ReorderAppend.reorder_append_absorbing_nonstarter
              (Decompose.decomposeSequence xs) cp hCp_ccc_pos
    rw [hToNFD_snoc]
    have hZArr : toNFD xs = lowL.toArray ++ highL.toArray := by
      apply Array.toList_inj.mp
      rw [Array.toList_append]
      show (toNFD xs).toList = lowL.toArray.toList ++ highL.toArray.toList
      rw [List.toList_toArray, List.toList_toArray]
      exact hPartition
    have hZsnocReshape : toNFD xs ++ #[cp]
                       = lowL.toArray ++ highL.toArray ++ #[cp] := by
      rw [hZArr]
    rw [hZsnocReshape]
    have hHighArrPos :
        ∀ c ∈ highL.toArray.toList, 0 < Lookup.canonicalCombiningClass c := by
      rw [List.toList_toArray]; exact hHighPos
    have hCpArrPos :
        ∀ y ∈ (#[cp] : Array Nat).toList, 0 < Lookup.canonicalCombiningClass y := by
      intro y hy
      have hYcp : y = cp := by simpa using hy
      rw [hYcp]; exact hCp_ccc_pos
    have hStrictGt :
        ∀ c ∈ highL.toArray.toList, ∀ y ∈ (#[cp] : Array Nat).toList,
          Lookup.canonicalCombiningClass y
            < Lookup.canonicalCombiningClass c := by
      intros c hc y hy
      have hYcp : y = cp := by simpa using hy
      rw [hYcp]
      rw [List.toList_toArray] at hc
      exact hHighGt c hc
    have hCommute :
        Reorder.reorder (lowL.toArray ++ #[cp] ++ highL.toArray)
          = Reorder.reorder (lowL.toArray ++ highL.toArray ++ #[cp]) :=
      ReorderAppend.reorder_commutes_strict_max_multi
        lowL.toArray (#[cp] : Array Nat) highL.toArray
        hHighArrPos hCpArrPos hStrictGt
    rw [← hCommute]
    -- HSR for the inserted form makes `reorder` the identity.
    have hHSR_partitioned : Reorder.HasSortedRuns (lowL ++ highL) :=
      hPartition ▸ hZ_HSR
    have hHSR_lowL :=
      HasSortedRuns_left_of_concat
        lowL highL hHSR_partitioned
    have hHSR_highL :=
      HasSortedRuns_right_of_concat
        lowL highL hHSR_partitioned
    have hSeam_lowL_cp :
        0 < Lookup.canonicalCombiningClass cp
        → ∀ a, lowL.getLast? = some a
            → Lookup.canonicalCombiningClass a
                ≤ Lookup.canonicalCombiningClass cp := by
      intros hCpPosArg a hLast
      clear hCpPosArg
      rw [hLowEq] at hLast
      exact trailingLow_last_le_when_high_nonempty
              (toNFD xs).toList (Lookup.canonicalCombiningClass cp) a hLast
    have hHSR_lowL_cp : Reorder.HasSortedRuns (lowL ++ [cp]) :=
      HasSortedRuns_append_singleton
        lowL cp hHSR_lowL hSeam_lowL_cp
    have hSeam_lowLcp_highL :
        ∀ a b, (lowL ++ [cp]).getLast? = some a → highL.head? = some b
            → 0 < Lookup.canonicalCombiningClass b
            → Lookup.canonicalCombiningClass a
                ≤ Lookup.canonicalCombiningClass b := by
      intros a b hLast hHead hBpos
      clear hBpos
      have hLastEq : (lowL ++ [cp]).getLast? = some cp :=
        getLast?_concat_singleton lowL cp
      rw [hLastEq] at hLast
      have hAcp : a = cp := ((Option.some.injEq cp a).mp hLast).symm
      rw [hAcp]
      have hBmem : b ∈ highL := by
        cases hHigh : highL with
        | nil => exact absurd hHigh hHighNonEmpty
        | cons hd tl =>
          rw [hHigh] at hHead
          have hHeadVal : (hd :: tl).head? = some hd := rfl
          rw [hHeadVal] at hHead
          have hBeq : hd = b := (Option.some.injEq hd b).mp hHead
          rw [← hBeq]
          exact List.mem_cons_self
      have hLt := hHighGt b hBmem
      omega
    have hHSR_inserted : Reorder.HasSortedRuns (lowL ++ [cp] ++ highL) :=
      HasSortedRuns_concat
        (lowL ++ [cp]) highL hHSR_lowL_cp hHSR_highL hSeam_lowLcp_highL
    have hListEq : (lowL.toArray ++ #[cp] ++ highL.toArray).toList
                 = lowL ++ [cp] ++ highL := by
      rw [Array.toList_append, Array.toList_append, List.toList_toArray,
          List.toList_toArray]
    have hHSR_inserted_arr :
        Reorder.HasSortedRuns
            (lowL.toArray ++ #[cp] ++ highL.toArray).toList := by
      rw [hListEq]; exact hHSR_inserted
    rw [Reorder.reorder_id_on_HasSortedRuns _ hHSR_inserted_arr]
    -- Apply the slide. Chain validity is derived from the buffer-
    -- bound on `compose (lowL.toArray ++ highL.toArray)`.
    have hCompZ : Compose.compose (lowL.toArray ++ highL.toArray) = xs := by
      rw [← hZArr]; show toNFC xs = xs; exact hPrefix
    have hFinalStarter :
        ((lowL.toArray ++ highL.toArray).foldl
            Compose.stepCompose Compose.initialState).starter.isSome
          = true := by
      rw [Array.foldl_append, ← Array.foldl_toList]
      exact foldl_stepCompose_starter_isSome_persists
              highL.toArray.toList
              (lowL.toArray.foldl Compose.stepCompose Compose.initialState)
              hLowStarter
    have hHSR_postCompose :
        NFC.hasSortedRunsBool
          (Compose.compose (lowL.toArray ++ highL.toArray) ++ #[cp]).toList
            = true := by
      rw [hCompZ]; exact hHSR_outer
    -- Buffer-bound (`compose_buffer_ccc_bound`) via the trailing-
    -- run-of-output characterization.
    have hFinalBufBound :
        ∀ y ∈ ((lowL.toArray ++ highL.toArray).foldl
                  Compose.stepCompose Compose.initialState).buffer,
          Lookup.canonicalCombiningClass y
            ≤ Lookup.canonicalCombiningClass cp :=
      compose_buffer_ccc_bound (lowL.toArray ++ highL.toArray) cp
        hCp_ccc_pos hFinalStarter hHSR_postCompose
    -- Chain validity (`chain_fires_via_buffer_bound`) via the
    -- buffer-bound + buffer-or-fire dichotomy.
    have hChainFresh : PrimaryFiresChain
          (lowL.toArray.foldl Compose.stepCompose Compose.initialState) highL :=
      chain_fires_via_buffer_bound highL lowL.toArray cp hHighPos hHighGt
        hLowStarter hFinalBufBound
    obtain ⟨stLow, hStLow⟩ :=
      Option.isSome_iff_exists.mp hLowStarter
    have hSlide : Compose.compose
                    (lowL.toArray ++ #[cp] ++ highL.toArray)
                  = Compose.compose
                    (lowL.toArray ++ highL.toArray ++ #[cp]) :=
      compose_slide_qcY lowL.toArray cp highL stLow hStLow hQC hCp_ccc_pos
        hHighGt hChainFresh
    rw [hSlide]
    rw [compose_qcY_linear
          (lowL.toArray ++ highL.toArray) cp hQC]
    rw [hCompZ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §9 UNIFIED SNOC DISPATCHER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Closes the snoc-induction step of the master soundness theorem.
    Dispatches on `cp`'s CCC class:

      * Starter (CCC = 0): `nfc_snoc_qcY_starter` — handles all
        decomposition shapes uniformly via
        `compose_qcY_starter_block_additive`.
      * Non-starter (CCC > 0): `nfc_snoc_qcY_nonstarter_structural`
        — the swap analysis discharged via `compose_slide_qcY` in
        `ComposeNonstarterSlide`. The empty-decomposition and
        not-Hangul premises derive from Fact 1 and
        `hangulSyllable_ccc_zero`. -/
theorem nfc_snoc_qcY
    (xs : Array Nat) (cp : Nat)
    (hQC : nfcQCValue cp = .Y)
    (hPrefix : toNFC xs = xs)
    (hSnocQC : isNFCQuickCheck (xs ++ #[cp]) = true) :
    toNFC (xs ++ #[cp]) = xs ++ #[cp] := by
  by_cases hCcc : Lookup.canonicalCombiningClass cp = 0
  · exact nfc_snoc_qcY_starter xs cp hQC hCcc hPrefix
  · have hCccPos : 0 < Lookup.canonicalCombiningClass cp :=
      Nat.pos_of_ne_zero hCcc
    have hDecomp : Lookup.canonicalDecomposition cp = #[] :=
      qcY_nonstarter_cp_no_decomp cp hQC hCccPos
    have hNotHangul : Hangul.isHangulSyllable cp = false := by
      cases hH : Hangul.isHangulSyllable cp with
      | false => rfl
      | true =>
        exfalso
        have hHangulCcc := hangulSyllable_ccc_zero_cp cp hH
        omega
    exact nfc_snoc_qcY_nonstarter_structural xs cp hQC hCccPos hDecomp
      hNotHangul hPrefix hSnocQC

end Unicode.Normalization.QuickCheckSoundnessSnocClosure
