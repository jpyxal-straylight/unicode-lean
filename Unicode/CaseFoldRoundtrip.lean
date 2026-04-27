/-
  Unicode.CaseFoldRoundtrip

  Unconditional discharge of `CaseFoldNfcRoundtripFixed`, the single
  remaining hypothesis for PRECIS idempotence (RFC 8264/8265 §7) after
  `NfcPreservesNonWidthCompatSource` was closed in
  `Unicode.Normalization.NFC`. The universal sequence-level commutation

      toNFD (caseFold x) = toNFD (caseFold (toNFD x))

  proposed in `Unicode.Precis.Preparation` as
  `CaseFoldNfdCommutesSeq` is FALSE over arbitrary inputs — see the
  scratch witness `.tmp/U0345CounterExample.lean`: on input
  `[0x0041, 0x0345, 0x0301]`, Path A yields `[0x61, 0x3B9, 0x301]` and
  Path B yields `[0x61, 0x301, 0x3B9]`. The pathology is U+0345
  (COMBINING GREEK YPOGEGRAMMENI, CCC = 240), whose `caseFold` target
  `U+03B9` (GREEK SMALL LETTER IOTA, CCC = 0) promotes a non-starter
  to a starter, shifting the partition boundary that `reorder` uses
  to delimit CCC-sorted runs.

  The PRECIS proof chain in `Preparation.caseFoldNfcRoundtripFixed_of_
  seq_commutes_and_cancellation` invokes `CaseFoldNfdCommutesSeq` only
  at two x-values, both images of `caseFold` and therefore free of
  U+0345 (or any case-fold source). A strictly weaker statement — the
  RESTRICTED lift gated on a pointwise fixed-point condition — is both
  true and sufficient to close the roundtrip directly. This module
  ships that restricted lift and the downstream `caseFoldNfcRoundtripFixed_holds`.

  # Structure

    1. UCD native_decide facts:
       - Hangul jamo are non-case-fold-source.
       - For every UnicodeData row, non-source codepoint ⇒ all
         canonical-decomposition targets are non-source.
       - Every Hangul syllable decomposes to non-sources.

    2. Pointwise + sequence preservation:
       - `fullCanonicalDecompose` preserves non-case-fold-source.
       - `decomposeSequence` preserves non-case-fold-source.
       - `toNFD` preserves non-case-fold-source.

    3. Structural supporting lemmas:
       - `caseFold` distributes over `++`.
       - `reorder` IN → OUT membership (companion to
         `reorder_preserves_all`, which gives OUT → IN).

    4. The restricted sequence lift:
       - `toNFD_caseFold_pointwise_lift`: under the pointwise
         fixed-point hypothesis, `toNFD (caseFold x) = toNFD x`.

    5. Main theorem `caseFoldNfcRoundtripFixed_holds`.
-/

import Unicode.Normalization.NFC
import Unicode.Normalization.NFD
import Unicode.Normalization.Decompose
import Unicode.Normalization.Decomposability
import Unicode.Normalization.Hangul
import Unicode.Normalization.ToNFDAppend
import Unicode.Normalization.ComposeInversion
import Unicode.CaseFoldCommutation
import Unicode.Precis.CaseMapping

namespace Unicode.CaseFoldRoundtrip

open Unicode.Normalization
open Unicode.Generated
open Unicode.Precis.CaseMapping
  (caseFold caseFoldCodepoint isCaseFoldSource
   caseFold_id_of_all_non_source caseFold_output_all_non_source)

-- ═══════════════════════════════════════════════════════════════════════════════
-- UCD NATIVE_DECIDE FACTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Every Hangul jamo codepoint (the L+V+T range `0x1100..0x11C2`) is a
    non-case-fold-source. Jamo have no case. -/
theorem hangulJamo_non_caseFoldSource :
    ((List.range 195).map (fun i => 0x1100 + i)).all
      (fun cp => !isCaseFoldSource cp) = true := by native_decide

/-- For every row in `UnicodeData.rows`, if the row's codepoint is not a
    case-fold source, every codepoint in its canonical decomposition is
    also not a case-fold source. The conditional form is necessary: the
    unconditional variant fails because e.g. `0x00C1` is a fold source
    whose decomposition contains `0x0041` (also a fold source). -/
theorem nonCaseFoldSource_decomp_all_nonSource :
    UnicodeData.rows.all (fun row =>
      isCaseFoldSource row.codepoint ||
      row.canonicalDecomposition.all (fun d => !isCaseFoldSource d)) = true := by
  native_decide

/-- Every Hangul precomposed syllable in `0xAC00..0xD7A3` decomposes to
    a sequence of non-case-fold-sources. Closed by `native_decide` over
    the entire 11172-syllable range. -/
theorem hangulSyllable_decompose_output_non_caseFoldSource :
    (List.range 11172).all
      (fun i => match Hangul.decomposeSyllable? (0xAC00 + i) with
                | some arr => arr.all (fun j => !isCaseFoldSource j)
                | none     => true) = true := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- POINTWISE LIFTS FROM UCD FACTS TO STRUCTURAL HYPOTHESES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Pointwise consequence of
    `hangulSyllable_decompose_output_non_caseFoldSource`: any successful
    `decomposeSyllable?` output contains only non-case-fold-sources. -/
theorem decomposeSyllable_output_non_caseFoldSource
    (cp : Nat) (arr : Array Nat)
    (h : Hangul.decomposeSyllable? cp = some arr) (j : Nat) (hj : j ∈ arr) :
    isCaseFoldSource j = false := by
  have hSyl : Hangul.isHangulSyllable cp = true := by
    unfold Hangul.decomposeSyllable? at h
    split at h
    · next hYes => exact hYes
    · simp at h
  have hRange : 0xAC00 ≤ cp ∧ cp < 0xAC00 + 11172 := by
    unfold Hangul.isHangulSyllable Hangul.SBase Hangul.SCount
           Hangul.LCount Hangul.NCount Hangul.VCount Hangul.TCount at hSyl
    exact of_decide_eq_true hSyl
  have hiLt : cp - 0xAC00 < 11172 := by omega
  have hCpEq : 0xAC00 + (cp - 0xAC00) = cp := by omega
  have hTable := hangulSyllable_decompose_output_non_caseFoldSource
  rw [List.all_eq_true] at hTable
  have hI : cp - 0xAC00 ∈ List.range 11172 := List.mem_range.mpr hiLt
  have hAtI := hTable (cp - 0xAC00) hI
  rw [hCpEq, h] at hAtI
  rw [Array.all_eq_true] at hAtI
  rcases Array.getElem_of_mem hj with ⟨k, hk, hElem⟩
  have hBool := hAtI k hk
  rw [hElem] at hBool
  simpa using hBool

/-- Pointwise consequence of `nonCaseFoldSource_decomp_all_nonSource`:
    for a non-case-fold-source `cp`, every element of
    `Lookup.canonicalDecomposition cp` is also non-case-fold-source. -/
theorem canonicalDecomposition_output_non_caseFoldSource
    (cp : Nat) (hCp : isCaseFoldSource cp = false)
    (j : Nat) (hj : j ∈ Lookup.canonicalDecomposition cp) :
    isCaseFoldSource j = false := by
  unfold Lookup.canonicalDecomposition at hj
  split at hj
  · next row hRow =>
    have hRowMem : row ∈ UnicodeData.rows := Array.mem_of_find?_eq_some hRow
    have hRowCp : row.codepoint = cp := by
      have hFind : UnicodeData.rows.find? (fun r => r.codepoint = cp) = some row := hRow
      have hP := Array.find?_some hFind
      exact of_decide_eq_true hP
    have hTable := nonCaseFoldSource_decomp_all_nonSource
    rw [Array.all_eq_true] at hTable
    rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
    have hEntry := hTable i hi
    rw [hElem] at hEntry
    simp only [Bool.or_eq_true] at hEntry
    rcases hEntry with hSrcCFS | hTgtAllNonSrc
    · rw [hRowCp, hCp] at hSrcCFS
      exact Bool.noConfusion hSrcCFS
    · rw [Array.all_eq_true] at hTgtAllNonSrc
      rcases Array.getElem_of_mem hj with ⟨k, hk, hElemJ⟩
      have hBool := hTgtAllNonSrc k hk
      rw [hElemJ] at hBool
      simpa using hBool
  · simp at hj

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRUCTURAL LIFT OF CASE-FOLD-STABILITY THROUGH toNFD
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Membership through a `foldl`-with-append over an array. -/
theorem mem_foldl_append (f : Nat → Array Nat) (cps : Array Nat) (cp : Nat)
    (hMem : cp ∈ cps.foldl (fun acc x => acc ++ f x) #[]) :
    ∃ x ∈ cps, cp ∈ f x := by
  rw [← Array.foldl_toList] at hMem
  have key : ∀ (l : List Nat) (init : Array Nat),
      cp ∈ l.foldl (fun acc x => acc ++ f x) init →
      cp ∈ init ∨ ∃ x ∈ l, cp ∈ f x := by
    intro l
    induction l with
    | nil => intro init hM; left; simpa using hM
    | cons hd tl ih =>
      intro init hM
      simp only [List.foldl_cons] at hM
      rcases ih (init ++ f hd) hM with hInit | ⟨x, hxM, hxF⟩
      · rcases Array.mem_append.mp hInit with h1 | h2
        · left; exact h1
        · right; exact ⟨hd, by simp, h2⟩
      · right; exact ⟨x, by simp [hxM], hxF⟩
  rcases key cps.toList #[] hMem with hEmpty | ⟨x, hxM, hxF⟩
  · simp at hEmpty
  · exact ⟨x, by simpa using hxM, hxF⟩

/-- Fuel-bounded preservation of non-case-fold-source through
    `fullCanonicalDecomposeFuel`. Induction on fuel: the zero case
    returns the input as its own decomposition; the successor case
    dispatches on the Hangul / table-lookup / no-decomposition branches,
    each of which preserves the predicate by its respective UCD fact. -/
theorem fullCanonicalDecomposeFuel_preserves_non_caseFoldSource (fuel : Nat) :
    ∀ cp, isCaseFoldSource cp = false →
    ∀ j ∈ Decompose.fullCanonicalDecomposeFuel fuel cp, isCaseFoldSource j = false := by
  induction fuel with
  | zero =>
    intro cp hCp j hj
    unfold Decompose.fullCanonicalDecomposeFuel at hj
    simp at hj
    rw [hj]
    exact hCp
  | succ fuel ih =>
    intro cp hCp j hj
    unfold Decompose.fullCanonicalDecomposeFuel at hj
    split at hj
    · next arr hSome =>
      exact decomposeSyllable_output_non_caseFoldSource cp arr hSome j hj
    · next hNone =>
      generalize hStep : Lookup.canonicalDecomposition cp = step at hj
      change j ∈ (if step.isEmpty = true then #[cp]
                  else step.foldl (fun acc cp' =>
                        acc ++ Decompose.fullCanonicalDecomposeFuel fuel cp') #[]) at hj
      split at hj
      · next hEmpty =>
        simp at hj
        rw [hj]
        exact hCp
      · next hNotEmpty =>
        obtain ⟨x, hxIn, hxF⟩ :=
          mem_foldl_append (Decompose.fullCanonicalDecomposeFuel fuel) step j hj
        rw [← hStep] at hxIn
        have hxNonSource : isCaseFoldSource x = false :=
          canonicalDecomposition_output_non_caseFoldSource cp hCp x hxIn
        exact ih x hxNonSource j hxF

/-- Single-codepoint preservation of non-case-fold-source through
    `fullCanonicalDecompose`. -/
theorem fullCanonicalDecompose_preserves_non_caseFoldSource
    (cp : Nat) (h : isCaseFoldSource cp = false) :
    ∀ j ∈ Decompose.fullCanonicalDecompose cp, isCaseFoldSource j = false := by
  unfold Decompose.fullCanonicalDecompose
  exact fullCanonicalDecomposeFuel_preserves_non_caseFoldSource Decompose.maxDepth cp h

/-- Sequence-level preservation of non-case-fold-source through
    `decomposeSequence`. -/
theorem decomposeSequence_preserves_non_caseFoldSource
    (cps : Array Nat) (h : ∀ cp ∈ cps, isCaseFoldSource cp = false) :
    ∀ j ∈ Decompose.decomposeSequence cps, isCaseFoldSource j = false := by
  intro j hj
  unfold Decompose.decomposeSequence at hj
  obtain ⟨x, hxIn, hxF⟩ := mem_foldl_append Decompose.fullCanonicalDecompose cps j hj
  exact fullCanonicalDecompose_preserves_non_caseFoldSource x (h x hxIn) j hxF

/-- **`toNFD` preserves non-case-fold-source.** Pipelines
    `decomposeSequence` → `reorder`; both have stage-wise preservation.
    Consumed by the main theorem to establish that `toNFD (caseFold cs)`
    is itself caseFold-stable for every input `cs`. -/
theorem toNFD_preserves_non_caseFoldSource
    (cps : Array Nat) (h : ∀ cp ∈ cps, isCaseFoldSource cp = false) :
    ∀ j ∈ NFC.toNFD cps, isCaseFoldSource j = false := by
  unfold NFC.toNFD
  intro j hj
  have hDecAll : ∀ cp ∈ Decompose.decomposeSequence cps,
                   (fun x => !isCaseFoldSource x) cp = true := by
    intro cp hcp
    have := decomposeSequence_preserves_non_caseFoldSource cps h cp hcp
    simpa using this
  have hR := Reorder.reorder_preserves_all (fun x => !isCaseFoldSource x)
               (Decompose.decomposeSequence cps) hDecAll j hj
  simpa using hR

-- ═══════════════════════════════════════════════════════════════════════════════
-- CASEFOLD DISTRIBUTES OVER ++
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Folding `(acc ++ caseFoldCodepoint cp)` over `b` starting from any
    prefix `init` distributes: the result is `init` concatenated with
    the result of folding over `b` from `#[]`. -/
theorem foldl_caseFold_init_distrib (b : Array Nat) (init : Array Nat) :
    b.foldl (fun acc cp => acc ++ caseFoldCodepoint cp) init =
    init ++ b.foldl (fun acc cp => acc ++ caseFoldCodepoint cp) #[] := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  induction b.toList generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih (init ++ caseFoldCodepoint hd), ih (#[] ++ caseFoldCodepoint hd)]
    rw [Array.empty_append]
    rw [Array.append_assoc]

/-- **`caseFold` distributes over `++`.** -/
theorem caseFold_append (a b : Array Nat) :
    caseFold (a ++ b) = caseFold a ++ caseFold b := by
  show (a ++ b).foldl (fun acc cp => acc ++ caseFoldCodepoint cp) #[] =
       a.foldl (fun acc cp => acc ++ caseFoldCodepoint cp) #[] ++
       b.foldl (fun acc cp => acc ++ caseFoldCodepoint cp) #[]
  rw [Array.foldl_append]
  exact foldl_caseFold_init_distrib b _

-- ═══════════════════════════════════════════════════════════════════════════════
-- REORDER MEMBERSHIP (IN → OUT)
--
-- `reorder` is a permutation of its input; every input codepoint appears
-- in the output. The complementary direction OUT → IN is landed
-- as `Reorder.reorder_preserves_all` specialized with a membership predicate.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Inserting `x` into `L` via `insertByCCC` preserves all existing
    elements of `L`. -/
theorem insertByCCC_preserves_mem (x y : Nat) (L : List Nat)
    (h : y ∈ L) : y ∈ Reorder.insertByCCC x L := by
  induction L with
  | nil => cases h
  | cons hd tl ih =>
    unfold Reorder.insertByCCC
    simp only [List.mem_cons] at h
    split
    · simp only [List.mem_cons]
      right
      rcases h with hEq | hRest
      · left; exact hEq
      · right; exact hRest
    · simp only [List.mem_cons]
      rcases h with hEq | hRest
      · left; exact hEq
      · right; exact ih hRest

/-- `insertByCCC x L` contains `x`. -/
theorem insertByCCC_mem_self (x : Nat) (L : List Nat) :
    x ∈ Reorder.insertByCCC x L := by
  induction L with
  | nil => simp [Reorder.insertByCCC]
  | cons hd tl ih =>
    unfold Reorder.insertByCCC
    split
    · simp
    · simp only [List.mem_cons]; right; exact ih

/-- `sortNonStarterRun L` contains every element of `L` (the sort is a
    permutation). -/
theorem sortNonStarterRun_mem
    (L : List Nat) (d : Nat) (hd : d ∈ L) :
    d ∈ Reorder.sortNonStarterRun L := by
  have key : ∀ (l : List Nat) (acc : List Nat),
      (d ∈ acc ∨ d ∈ l) →
      d ∈ l.foldl (fun sorted cp => Reorder.insertByCCC cp sorted) acc := by
    intro l
    induction l with
    | nil =>
      intro acc h
      rcases h with hA | hL
      · simpa using hA
      · cases hL
    | cons hd' tl ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih (Reorder.insertByCCC hd' acc)
      rcases h with hA | hL
      · left; exact insertByCCC_preserves_mem hd' d acc hA
      · rcases List.mem_cons.mp hL with hEq | hRest
        · left; rw [hEq]; exact insertByCCC_mem_self hd' acc
        · right; exact hRest
  unfold Reorder.sortNonStarterRun
  exact key L [] (Or.inr hd)

/-- `flushRun S` contains every element of `S.currentRun`. -/
theorem flushRun_mem (S : Reorder.ReorderState) (d : Nat)
    (h : d ∈ S.currentRun) : d ∈ Reorder.flushRun S := by
  unfold Reorder.flushRun
  rw [List.mem_toArray]
  apply sortNonStarterRun_mem
  exact List.mem_reverse.mpr h

/-- Fold-level preservation of membership: any `d` present in the
    initial `emitted`, `currentRun`, or remaining list shows up in the
    final fold state's `emitted` or `currentRun`. -/
theorem stepReorder_fold_preserves_mem
    (l : List Nat) (S : Reorder.ReorderState) (d : Nat)
    (h : d ∈ S.emitted ∨ d ∈ S.currentRun ∨ d ∈ l) :
    d ∈ (l.foldl Reorder.stepReorder S).emitted ∨
    d ∈ (l.foldl Reorder.stepReorder S).currentRun := by
  induction l generalizing S with
  | nil =>
    rcases h with he | hr | hL
    · left; exact he
    · right; exact hr
    · cases hL
  | cons hd' tl ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold Reorder.stepReorder
    by_cases hCcc : Lookup.canonicalCombiningClass hd' = 0
    · rw [if_pos hCcc]
      simp only [List.mem_cons] at h
      rcases h with he | hr | hEq | hRest
      · left
        rw [Array.mem_append]; left
        rw [Array.mem_append]; left; exact he
      · left
        rw [Array.mem_append]; left
        rw [Array.mem_append]; right
        exact flushRun_mem S d hr
      · left
        rw [Array.mem_append]; right
        simp; exact hEq
      · right; right; exact hRest
    · rw [if_neg hCcc]
      simp only [List.mem_cons] at h
      rcases h with he | hr | hEq | hRest
      · left; exact he
      · right; left
        simp only [List.mem_cons]; right; exact hr
      · right; left
        simp only [List.mem_cons]; left; exact hEq
      · right; right; exact hRest

/-- **Reorder IN → OUT.** Every element of the input array appears in
    the reorder output. Companion to `Reorder.reorder_preserves_all`
    which gives the OUT → IN direction; together they establish that
    `reorder` permutes its input without adding or removing elements. -/
theorem reorder_mem_of_mem (cps : Array Nat) (d : Nat) (hd : d ∈ cps) :
    d ∈ Reorder.reorder cps := by
  unfold Reorder.reorder
  rw [← Array.foldl_toList]
  have hFold := stepReorder_fold_preserves_mem cps.toList Reorder.initState d
    (Or.inr (Or.inr (by simpa using hd)))
  rcases hFold with he | hr
  · rw [Array.mem_append]; left; exact he
  · rw [Array.mem_append]; right
    exact flushRun_mem (cps.toList.foldl Reorder.stepReorder Reorder.initState) d hr

-- ═══════════════════════════════════════════════════════════════════════════════
-- FORWARD MEMBERSHIP IN foldl-WITH-APPEND
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Forward direction of `mem_foldl_append`: given `c ∈ cps` and
    `d ∈ f c`, `d` appears in the `foldl`-with-append output. -/
theorem mem_foldl_append_of (f : Nat → Array Nat) (cps : Array Nat)
    (c : Nat) (hc : c ∈ cps) (d : Nat) (hd : d ∈ f c) :
    d ∈ cps.foldl (fun acc x => acc ++ f x) #[] := by
  rw [← Array.foldl_toList]
  have key : ∀ (l : List Nat) (init : Array Nat),
      (d ∈ init ∨ ∃ c' ∈ l, d ∈ f c') →
      d ∈ l.foldl (fun acc x => acc ++ f x) init := by
    intro l
    induction l with
    | nil =>
      intro init hCase
      rcases hCase with hInit | ⟨c', hc', hdf⟩
      · simpa using hInit
      · cases hc'
    | cons hd' tl ih =>
      intro init hCase
      simp only [List.foldl_cons]
      apply ih (init ++ f hd')
      rcases hCase with hInit | ⟨c', hc', hcf⟩
      · left; exact Array.mem_append.mpr (Or.inl hInit)
      · rcases List.mem_cons.mp hc' with rfl | hRest
        · left; exact Array.mem_append.mpr (Or.inr hcf)
        · right; exact ⟨c', hRest, hcf⟩
  apply key cps.toList #[]
  right
  exact ⟨c, by simpa using hc, hd⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- RESTRICTED SEQUENCE LIFT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Restricted sequence lift for `caseFold` and `toNFD`.** If every
    codepoint in `x` satisfies the pointwise fixed-point
    `toNFD (caseFold #[cp]) = toNFD #[cp]`, then the sequence-level
    equality `toNFD (caseFold x) = toNFD x` holds. The universal form
    — the statement `CaseFoldNfdCommutesSeq` in
    `Unicode.Precis.Preparation` — is FALSE; a concrete counter-example
    lives at `.tmp/U0345CounterExample.lean`. The restricted form here
    is sufficient for the PRECIS roundtrip because the chain only
    invokes the lift on arrays whose codepoints have this pointwise
    fixed-point property. -/
theorem toNFD_caseFold_pointwise_lift (x : Array Nat)
    (h : ∀ cp ∈ x, NFC.toNFD (caseFold #[cp]) = NFC.toNFD #[cp]) :
    NFC.toNFD (caseFold x) = NFC.toNFD x := by
  have key : ∀ (l : List Nat),
      (∀ cp ∈ l, NFC.toNFD (caseFold #[cp]) = NFC.toNFD #[cp]) →
      NFC.toNFD (caseFold l.toArray) = NFC.toNFD l.toArray := by
    refine Reorder.list_snoc_induction ?baseNil ?inductiveSnoc
    · intro hAllNil
      show NFC.toNFD (caseFold (([] : List Nat).toArray)) =
           NFC.toNFD (([] : List Nat).toArray)
      rfl
    · intro xs cp ih hSnoc
      have h_xs : ∀ cp' ∈ xs, NFC.toNFD (caseFold #[cp']) = NFC.toNFD #[cp'] := by
        intro cp' hMem; exact hSnoc cp' (by simp [hMem])
      have h_cp : NFC.toNFD (caseFold #[cp]) = NFC.toNFD #[cp] :=
        hSnoc cp (by simp)
      have hIH := ih h_xs
      show NFC.toNFD (caseFold ((xs ++ [cp]).toArray)) =
           NFC.toNFD ((xs ++ [cp]).toArray)
      have hArrEq : (xs ++ [cp]).toArray = xs.toArray ++ #[cp] := by simp
      rw [hArrEq]
      rw [caseFold_append]
      rw [ToNFDAppend.toNFD_absorbing_left (caseFold xs.toArray) (caseFold #[cp])]
      rw [hIH]
      rw [← ToNFDAppend.toNFD_absorbing_left xs.toArray (caseFold #[cp])]
      rw [ToNFDAppend.toNFD_absorbing_right xs.toArray #[cp]]
      rw [← h_cp]
      rw [← ToNFDAppend.toNFD_absorbing_right xs.toArray (caseFold #[cp])]
  have hListHyp : ∀ cp ∈ x.toList, NFC.toNFD (caseFold #[cp]) = NFC.toNFD #[cp] :=
    fun cp hMem => h cp (by simpa using hMem)
  have hResult := key x.toList hListHyp
  have hToArray : x.toList.toArray = x := Array.toArray_toList
  rw [hToArray] at hResult
  exact hResult

-- ═══════════════════════════════════════════════════════════════════════════════
-- MAIN THEOREM: `CaseFoldNfcRoundtripFixed` UNCONDITIONAL
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **`CaseFoldNfcRoundtripFixed` discharged unconditionally.** For every
    codepoint sequence `cs`:
    `toNFC (caseFold (toNFC (caseFold cs))) = toNFC (caseFold cs)`.

    Proof chain:

      Let `w := caseFold cs`. By `caseFold_output_all_non_source`, `w`
      is caseFold-stable. By `toNFD_preserves_non_caseFoldSource`,
      `toNFD w` is caseFold-stable.

      By `toNFC_eq_of_toNFD_eq` the goal reduces to
      `toNFD (caseFold (toNFC w)) = toNFD w`. We apply
      `toNFD_caseFold_pointwise_lift` to `toNFC w`, establishing for
      each `c ∈ toNFC w` the pointwise fixed-point
      `toNFD (caseFold #[c]) = toNFD #[c]`.

      Per-codepoint: `d ∈ toNFD #[c]` lifts through
      `reorder_preserves_all` (OUT→IN) to `d ∈ decomposeSequence #[c] =
      fullCanonicalDecompose c`, then through `mem_foldl_append_of` to
      `d ∈ decomposeSequence (toNFC w)`, then through
      `reorder_mem_of_mem` (IN→OUT) to `d ∈ toNFD (toNFC w) = toNFD w`
      (via `toNFD_toNFC_eq_toNFD`). Caseful-stability of `toNFD w`
      gives `isCaseFoldSource d = false`. So `toNFD #[c]` is
      caseFold-stable, hence `caseFold (toNFD #[c]) = toNFD #[c]`.
      The pointwise commutation
      `caseFold_commutes_with_NFD_singleton c` then closes the
      pointwise fixed-point.

      After the lift: `toNFD (caseFold (toNFC w)) = toNFD (toNFC w)`.
      `toNFD_toNFC_eq_toNFD` reduces the RHS to `toNFD w`. -/
theorem caseFoldNfcRoundtripFixed_holds :
    ∀ cs : Array Nat,
      NFC.toNFC (caseFold (NFC.toNFC (caseFold cs))) = NFC.toNFC (caseFold cs) := by
  intro cs
  have hwStable : ∀ cp ∈ caseFold cs, isCaseFoldSource cp = false := by
    intro cp hcp
    exact caseFold_output_all_non_source cs cp hcp
  have hToNFDwStable : ∀ cp ∈ NFC.toNFD (caseFold cs), isCaseFoldSource cp = false :=
    toNFD_preserves_non_caseFoldSource (caseFold cs) hwStable
  apply NFD.toNFC_eq_of_toNFD_eq
  have hPointwiseForToNFCw : ∀ c ∈ NFC.toNFC (caseFold cs),
      NFC.toNFD (caseFold #[c]) = NFC.toNFD #[c] := by
    intro c hc
    have hToNFDcStable : ∀ d ∈ NFC.toNFD #[c], isCaseFoldSource d = false := by
      intro d hd
      have hDecSing : d ∈ Decompose.decomposeSequence #[c] := by
        have hPdec : ∀ y ∈ Decompose.decomposeSequence #[c],
            (fun x => decide (x ∈ Decompose.decomposeSequence #[c])) y = true := by
          intro y hy; exact decide_eq_true hy
        have hReorder := Reorder.reorder_preserves_all
          (fun x => decide (x ∈ Decompose.decomposeSequence #[c]))
          (Decompose.decomposeSequence #[c]) hPdec d hd
        exact of_decide_eq_true hReorder
      have hFCDc : d ∈ Decompose.fullCanonicalDecompose c := by
        have hEq : Decompose.decomposeSequence #[c] = Decompose.fullCanonicalDecompose c := by
          unfold Decompose.decomposeSequence
          simp
        rw [hEq] at hDecSing; exact hDecSing
      have hDecAll : d ∈ Decompose.decomposeSequence (NFC.toNFC (caseFold cs)) := by
        unfold Decompose.decomposeSequence
        exact mem_foldl_append_of Decompose.fullCanonicalDecompose (NFC.toNFC (caseFold cs))
          c hc d hFCDc
      have hToNFDall : d ∈ NFC.toNFD (NFC.toNFC (caseFold cs)) :=
        reorder_mem_of_mem (Decompose.decomposeSequence (NFC.toNFC (caseFold cs))) d hDecAll
      rw [ComposeInversion.toNFD_toNFC_eq_toNFD] at hToNFDall
      exact hToNFDwStable d hToNFDall
    have hCaseFoldId : caseFold (NFC.toNFD #[c]) = NFC.toNFD #[c] :=
      caseFold_id_of_all_non_source (NFC.toNFD #[c]) hToNFDcStable
    have hSingleton :=
      Unicode.CaseFoldCommutation.caseFold_commutes_with_NFD_singleton c
    rw [hCaseFoldId] at hSingleton
    rw [hSingleton]
    exact NFD.toNFD_idempotent #[c]
  have hLift := toNFD_caseFold_pointwise_lift
                  (NFC.toNFC (caseFold cs)) hPointwiseForToNFCw
  rw [hLift]
  exact ComposeInversion.toNFD_toNFC_eq_toNFD (caseFold cs)

end Unicode.CaseFoldRoundtrip
