/-
  Unicode.Normalization.QuickCheckSoundnessFact4

  **Fact 4 — Boundary fact for QC=Y codepoints.** For every QC=Y
  codepoint `c` (regardless of starter / non-starter status),
  `primaryComposite? d c = none` for all `d`. Generalises Fact 3
  (`primaryComposite_none_of_qcY_nonstarter`) to the starter case.

  The proof has two strands corresponding to the two branches of
  `Compose.primaryComposite?`:

    * **Hangul branch** (`Hangul.composePair? d c`): closed via the
      table-derived facts that V jamos and T jamos — the only
      codepoints that can appear as the second component of a Hangul
      composition pair — are NFC_QC=M (not Y).
    * **UCD-table branch** (`UnicodeData.rows.findSome?`): closed via
      `qcY_nonstarter_not_decomp_target` (despite the misleading
      name, that fact applies uniformly to every 2-element canonical
      decomposition target, not just non-starter targets).
-/

import Unicode.Normalization.NFC
import Unicode.Normalization.Lookup
import Unicode.Normalization.Hangul
import Unicode.Normalization.Compose
import Unicode.Normalization.QuickCheckFacts
import Unicode.Generated.UnicodeData

namespace Unicode.Normalization.QuickCheckSoundnessFact4

open Unicode.Normalization
open Unicode.Normalization.NFC (nfcQCValue)
open Unicode.Generated

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1 V/T JAMO RANGES ARE QC=M (TABLE LIFT)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **V jamo NFC_QC = M (range table).** Every codepoint in the Hangul
    V jamo range `[VBase, VBase + VCount)` (= `[0x1161, 0x1175]`) has
    `nfcQCValue = .M`. Closed by `native_decide` over the 21-element
    range. -/
theorem vJamo_qcM_range_table :
    (List.range Hangul.VCount).all
      (fun i => decide (nfcQCValue (Hangul.VBase + i) = .M)) = true := by
  native_decide

/-- **T jamo NFC_QC = M (range table).** Every codepoint in the Hangul
    T jamo range `[TBase + 1, TBase + TCount)` (= `[0x11A8, 0x11C2]`)
    has `nfcQCValue = .M`. The off-by-one (`TBase + 0 = 0x11A7` is NOT
    a valid T jamo) is excluded by starting the range at `TBase + 1`.
    Closed by `native_decide` over the 27-element valid range. -/
theorem tJamo_qcM_range_table :
    (List.range (Hangul.TCount - 1)).all
      (fun i => decide (nfcQCValue (Hangul.TBase + 1 + i) = .M)) = true := by
  native_decide

/-- **V jamo per-codepoint NFC_QC = M.** Lifts `vJamo_qcM_range_table`
    via the structural relationship `Hangul.isVJamo cp = true ↔ cp ∈
    [VBase, VBase + VCount)`. -/
theorem nfcQCValue_vJamo_M (cp : Nat) (h : Hangul.isVJamo cp = true) :
    nfcQCValue cp = .M := by
  have hRange : Hangul.VBase ≤ cp ∧ cp < Hangul.VBase + Hangul.VCount := by
    unfold Hangul.isVJamo Hangul.VBase Hangul.VCount at h
    exact of_decide_eq_true h
  have hIdxLt : cp - Hangul.VBase < Hangul.VCount := by omega
  have hCpEq : Hangul.VBase + (cp - Hangul.VBase) = cp := by omega
  have hTable := vJamo_qcM_range_table
  rw [List.all_eq_true] at hTable
  have hI : cp - Hangul.VBase ∈ List.range Hangul.VCount :=
    List.mem_range.mpr hIdxLt
  have hAt := hTable (cp - Hangul.VBase) hI
  rw [hCpEq] at hAt
  exact of_decide_eq_true hAt

/-- **T jamo per-codepoint NFC_QC = M.** Lifts `tJamo_qcM_range_table`
    via the structural relationship `Hangul.isTJamo cp = true ↔ cp ∈
    [TBase + 1, TBase + TCount)`. -/
theorem nfcQCValue_tJamo_M (cp : Nat) (h : Hangul.isTJamo cp = true) :
    nfcQCValue cp = .M := by
  have hRange : Hangul.TBase < cp ∧ cp < Hangul.TBase + Hangul.TCount := by
    unfold Hangul.isTJamo Hangul.TBase Hangul.TCount at h
    exact of_decide_eq_true h
  have hIdxLt : cp - (Hangul.TBase + 1) < Hangul.TCount - 1 := by omega
  have hCpEq : Hangul.TBase + 1 + (cp - (Hangul.TBase + 1)) = cp := by omega
  have hTable := tJamo_qcM_range_table
  rw [List.all_eq_true] at hTable
  have hI : cp - (Hangul.TBase + 1) ∈ List.range (Hangul.TCount - 1) :=
    List.mem_range.mpr hIdxLt
  have hAt := hTable (cp - (Hangul.TBase + 1)) hI
  rw [hCpEq] at hAt
  exact of_decide_eq_true hAt

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2 V/T JAMO EXCLUSION FOR QC=Y
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **V jamo not QC=Y.** Contrapositive of `nfcQCValue_vJamo_M`. -/
theorem isVJamo_false_of_qcY (cp : Nat) (hQC : nfcQCValue cp = .Y) :
    Hangul.isVJamo cp = false := by
  cases h : Hangul.isVJamo cp with
  | false => rfl
  | true =>
    exfalso
    have hM := nfcQCValue_vJamo_M cp h
    rw [hQC] at hM
    nomatch hM

/-- **T jamo not QC=Y.** Contrapositive of `nfcQCValue_tJamo_M`. -/
theorem isTJamo_false_of_qcY (cp : Nat) (hQC : nfcQCValue cp = .Y) :
    Hangul.isTJamo cp = false := by
  cases h : Hangul.isTJamo cp with
  | false => rfl
  | true =>
    exfalso
    have hM := nfcQCValue_tJamo_M cp h
    rw [hQC] at hM
    nomatch hM

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3 HANGUL COMPOSE-PAIR NONE FOR QC=Y SECOND COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Hangul composePair? returns none for QC=Y second.** A QC=Y `cp`
    cannot be the second component of any Hangul canonical pair: the
    L+V branch requires V jamo (QC=M), the LV+T branch requires T jamo
    (QC=M); both are excluded by `cp` being QC=Y. -/
theorem hangul_composePair_none_of_qcY (st cp : Nat) (hQC : nfcQCValue cp = .Y) :
    Hangul.composePair? st cp = none := by
  unfold Hangul.composePair?
  rw [show Hangul.isVJamo cp = false from isVJamo_false_of_qcY cp hQC]
  rw [show Hangul.isTJamo cp = false from isTJamo_false_of_qcY cp hQC]
  simp

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4 PRIMARY-COMPOSITE NONE FOR QC=Y SECOND COMPONENT (FACT 4)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Fact 4 (general boundary).** For every QC=Y codepoint `cp`,
    `primaryComposite? d cp = none` for all `d`. Generalises Fact 3
    (`primaryComposite_none_of_qcY_nonstarter`) to the starter case;
    the proof has the same shape, with `hangul_composePair_none_of_qcY`
    replacing the nonstarter-specific Hangul fact. -/
theorem primaryComposite_none_of_qcY (st cp : Nat) (hQC : nfcQCValue cp = .Y) :
    Compose.primaryComposite? st cp = none := by
  unfold Compose.primaryComposite?
  rw [hangul_composePair_none_of_qcY st cp hQC]
  show UnicodeData.rows.findSome? (fun r =>
      if r.canonicalDecomposition = #[st, cp]
         ∧ ¬ Lookup.isFullCompositionExclusion r.codepoint then
        some r.codepoint
      else none) = none
  generalize hFind : UnicodeData.rows.findSome? (fun r =>
      if r.canonicalDecomposition = #[st, cp]
         ∧ ¬ Lookup.isFullCompositionExclusion r.codepoint then
        some r.codepoint
      else none) = result
  cases result with
  | none => rfl
  | some p =>
    exfalso
    obtain ⟨row, hRowMem, hFEq⟩ := Array.exists_of_findSome?_eq_some hFind
    have hAll := QuickCheckFacts.qcY_nonstarter_not_decomp_target
    rw [Array.all_eq_true] at hAll
    rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
    have hRow := hAll i hi
    rw [hElem] at hRow
    split at hFEq
    · next hCond =>
      obtain ⟨hDecomp, hNotExc⟩ := hCond
      simp [hDecomp, hQC] at hRow
      exact hNotExc hRow
    · nomatch hFEq

end Unicode.Normalization.QuickCheckSoundnessFact4
