/-
  Unicode.Normalization.ComposeKernelSupport

  Structural support content for the master soundness theorem of
  `isNFCQuickCheck`. Depends only on `ComposeBlockAdditive`,
  `ComposeNonstarterSlide`, `ComposeBufferStructure`, and the
  foundational `Compose` / `Reorder` definitions.

  Three groups of structural facts:

    * **Compose state-machine evolution** —
      `foldl_stepCompose_starter_isSome_persists` and
      `foldl_stepCompose_starter_isSome_of_member` capture two facets
      of starter-presence under the foldl: once a starter is registered,
      it persists; and a member with `ccc = 0` registers a starter.

    * **HSR list-structure** — `HasSortedRuns_concat`,
      `HasSortedRuns_left_of_concat`, `HasSortedRuns_right_of_concat`,
      and `HasSortedRuns_append_singleton` capture how `HasSortedRuns`
      decomposes and reassembles across list concatenation.

    * **Partition at a CCC threshold** — `trailingLow` and
      `trailingHigh` partition a list at its trailing run's CCC
      threshold. The `*_append`, `*_pos`, `*_gt`, `*_nonempty`,
      `*_last_le` lemmas characterize the partition's structure.

  Plus `nfc_snoc_atomic_nonstarter_hsr_preserves` (the HSR-preserves
  variant of the non-starter snoc) via `compose_qcY_linear` and
  `reorder_id_on_HasSortedRuns`.
-/

import Unicode.Normalization.Compose
import Unicode.Normalization.ComposeInversion
import Unicode.Normalization.ComposeBlockAdditive
import Unicode.Normalization.NFC
import Unicode.Normalization.NFD
import Unicode.Normalization.Reorder
import Unicode.Normalization.ReorderAppend
import Unicode.Normalization.Distribute

namespace Unicode.Normalization.ComposeKernelSupport

open Unicode.Normalization
open Unicode.Normalization.NFC (toNFC toNFD nfcQCValue hasSortedRunsBool)
open Unicode.Normalization.ComposeBlockAdditive (compose_qcY_linear)

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1 STARTER PRESENCE PERSISTS THROUGH FOLDL
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Once `starter` is `some _`, it stays `some _`.** A foldl of
    `stepCompose` over any list preserves a non-`none` starter:
    every `stepCompose` branch either keeps `s.starter` or replaces
    it with `some _` (Cases 4, 5, 7 — primary firing or new-starter
    registration), never resetting to `none`. -/
theorem stepCompose_starter_isSome_preserves
    (s : Compose.ComposeState) (cp : Nat)
    (hSt : s.starter.isSome = true) :
    (Compose.stepCompose s cp).starter.isSome = true := by
  obtain ⟨st, hStAct⟩ := Option.isSome_iff_exists.mp hSt
  set_option linter.unusedSimpArgs false in
  unfold Compose.stepCompose
  simp only [hStAct]
  by_cases hCcc : Lookup.canonicalCombiningClass cp = 0
  · rw [if_pos hCcc]
    by_cases hBuf : s.buffer.isEmpty = true
    · rw [if_pos hBuf]
      cases hPC : Compose.primaryComposite? st cp with
      | none => rfl
      | some p => rfl
    · rw [if_neg hBuf]
      rfl
  · rw [if_neg hCcc]
    by_cases hMax : Lookup.canonicalCombiningClass cp ≤ s.maxCCC
    · rw [if_pos hMax]
      rfl
    · rw [if_neg hMax]
      cases hPC : Compose.primaryComposite? st cp with
      | none => rfl
      | some p => rfl

/-- Foldl of `stepCompose` over a list preserves `starter.isSome`. -/
theorem foldl_stepCompose_starter_isSome_persists
    (L : List Nat) (s : Compose.ComposeState)
    (hSt : s.starter.isSome = true) :
    (L.foldl Compose.stepCompose s).starter.isSome = true := by
  induction L generalizing s with
  | nil => exact hSt
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (Compose.stepCompose s hd) (stepCompose_starter_isSome_preserves s hd hSt)

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2 STARTER REGISTRATION ON FIRST CCC=0 ELEMENT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A starter `cp` (`ccc cp = 0`) processed at any state produces a
    `some` starter post-step: blocked or strict-max branches don't
    apply (cp is a starter); Case 5 (starter input from `some` state)
    yields `some p` or `some cp`; Case 4 (starter input from `none`
    state) yields `some cp`. -/
theorem stepCompose_starter_input_isSome
    (s : Compose.ComposeState) (cp : Nat)
    (hCcc : Lookup.canonicalCombiningClass cp = 0) :
    (Compose.stepCompose s cp).starter.isSome = true := by
  set_option linter.unusedSimpArgs false in
  unfold Compose.stepCompose
  cases hSt : s.starter with
  | none =>
    simp only [hSt]
    rw [if_pos hCcc]
    rfl
  | some st =>
    simp only [hSt]
    rw [if_pos hCcc]
    by_cases hBuf : s.buffer.isEmpty = true
    · rw [if_pos hBuf]
      cases hPC : Compose.primaryComposite? st cp with
      | none => rfl
      | some p => rfl
    · rw [if_neg hBuf]
      rfl

/-- **Starter member registers a starter.** If a list `L` contains
    a starter element, the foldl `stepCompose` over `L` from any
    state produces a state with `some` starter. The starter on the
    first such element registers via Case 4 or 5; subsequent steps
    preserve via §1. -/
theorem foldl_stepCompose_starter_isSome_of_member
    (L : List Nat) (s : Compose.ComposeState)
    (hMember : ∃ x ∈ L, Lookup.canonicalCombiningClass x = 0) :
    (L.foldl Compose.stepCompose s).starter.isSome = true := by
  obtain ⟨x, hxMem, hxCcc⟩ := hMember
  induction L generalizing s with
  | nil => exact absurd hxMem List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hxMem with hxHd | hxTl
    · -- x = hd. After processing hd (a starter), starter is some.
      have hHdCcc : Lookup.canonicalCombiningClass hd = 0 := hxHd ▸ hxCcc
      have hPostHd :
          (Compose.stepCompose s hd).starter.isSome = true :=
        stepCompose_starter_input_isSome s hd hHdCcc
      exact foldl_stepCompose_starter_isSome_persists tl
              (Compose.stepCompose s hd) hPostHd
    · exact ih (Compose.stepCompose s hd) hxTl

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3 SMALL LIST UTILITIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The last element of a list extended by a singleton is the singleton's
    element. -/
theorem getLast?_concat_singleton (xs : List Nat) (x : Nat) :
    (xs ++ [x]).getLast? = some x := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    match rest with
    | [] => rfl
    | b :: more => exact ih

/-- Membership in `takeWhile` implies the predicate. -/
theorem mem_takeWhile_imp_pred (p : Nat → Bool) (l : List Nat) :
    ∀ x ∈ l.takeWhile p, p x = true := by
  induction l with
  | nil => intros x hx; exact absurd hx List.not_mem_nil
  | cons a rest ih =>
    intros x hx
    rw [List.takeWhile_cons] at hx
    by_cases hp : p a = true
    · rw [if_pos hp] at hx
      rcases List.mem_cons.mp hx with hHead | hTail
      · rw [hHead]; exact hp
      · exact ih x hTail
    · rw [if_neg hp] at hx
      exact absurd hx List.not_mem_nil

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4 SMALL DECOMPOSE UTILITY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A codepoint with empty canonical decomposition that is not a Hangul
    precomposed syllable has trivial full canonical decomposition. -/
theorem decomp_atomic_id
    (cp : Nat)
    (hDecomp : Lookup.canonicalDecomposition cp = #[])
    (hNotHangul : Hangul.isHangulSyllable cp = false) :
    Decompose.fullCanonicalDecompose cp = #[cp] := by
  have hDsyl : Hangul.decomposeSyllable? cp = none := by
    unfold Hangul.decomposeSyllable?
    rw [hNotHangul]
    simp
  show Decompose.fullCanonicalDecomposeFuel Decompose.maxDepth cp = #[cp]
  unfold Decompose.maxDepth Decompose.fullCanonicalDecomposeFuel
  rw [hDsyl]
  simp [hDecomp]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §5 HSR LIST-STRUCTURE FAMILY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HSR is preserved by taking left-prefix of a concatenation. -/
theorem HasSortedRuns_left_of_concat
    (l1 l2 : List Nat) :
    Reorder.HasSortedRuns (l1 ++ l2) → Reorder.HasSortedRuns l1 := by
  induction l1 with
  | nil =>
    intros hHsrNil
    clear hHsrNil
    show Reorder.HasSortedRuns []
    simp
  | cons x rest ih =>
    intro h
    cases rest with
    | nil =>
      show Reorder.HasSortedRuns [x]
      simp
    | cons y rest2 =>
      show Reorder.HasSortedRuns (x :: y :: rest2)
      rw [Reorder.HasSortedRuns_cons_cons]
      have hCons : Reorder.HasSortedRuns (x :: y :: (rest2 ++ l2)) := h
      rw [Reorder.HasSortedRuns_cons_cons] at hCons
      obtain ⟨hPair, hYRestL2⟩ := hCons
      refine ⟨hPair, ?recHSR⟩
      exact ih hYRestL2

/-- HSR is preserved by taking right-suffix of a concatenation. -/
theorem HasSortedRuns_right_of_concat
    (l1 l2 : List Nat) :
    Reorder.HasSortedRuns (l1 ++ l2) → Reorder.HasSortedRuns l2 := by
  induction l1 with
  | nil =>
    intro h
    show Reorder.HasSortedRuns l2
    simp at h
    exact h
  | cons x rest ih =>
    intro h
    have hTail : Reorder.HasSortedRuns (rest ++ l2) :=
      Reorder.HasSortedRuns_tail h
    exact ih hTail

/-- HSR preserved under `++ [b]` for arbitrary `b`, given the seam
    bound: when `b` is a non-starter, `L`'s last element has CCC ≤
    ccc(b); for starter `b` the seam constraint is vacuous. -/
theorem HasSortedRuns_append_singleton
    (L : List Nat) (b : Nat) :
    Reorder.HasSortedRuns L
    → (0 < Lookup.canonicalCombiningClass b
        → ∀ a, L.getLast? = some a
            → Lookup.canonicalCombiningClass a
                ≤ Lookup.canonicalCombiningClass b)
    → Reorder.HasSortedRuns (L ++ [b]) := by
  induction L with
  | nil =>
    intros hHsrNil hSeamNil
    clear hHsrNil hSeamNil
    show Reorder.HasSortedRuns [b]
    simp
  | cons x rest ih =>
    intros hL_HSR hSeam
    cases rest with
    | nil =>
      show Reorder.HasSortedRuns [x, b]
      rw [Reorder.HasSortedRuns_cons_cons]
      refine ⟨?pairCond, ?singletonHSR⟩
      · intro hBpos
        apply hSeam hBpos x
        rfl
      · simp
    | cons y rest2 =>
      show Reorder.HasSortedRuns (x :: y :: (rest2 ++ [b]))
      rw [Reorder.HasSortedRuns_cons_cons]
      rw [Reorder.HasSortedRuns_cons_cons] at hL_HSR
      obtain ⟨hPair_xy, hHSR_yrest⟩ := hL_HSR
      refine ⟨hPair_xy, ?recHSR⟩
      have hSeamRest :
          0 < Lookup.canonicalCombiningClass b
          → ∀ a, (y :: rest2).getLast? = some a
              → Lookup.canonicalCombiningClass a
                  ≤ Lookup.canonicalCombiningClass b := by
        intros hBpos a hLast
        apply hSeam hBpos a
        show (x :: y :: rest2).getLast? = some a
        have hXcons : (x :: y :: rest2).getLast? = (y :: rest2).getLast? := rfl
        rw [hXcons]
        exact hLast
      exact ih hHSR_yrest hSeamRest

/-- HSR concat across two HSR halves with a seam bound. -/
theorem HasSortedRuns_concat
    (l1 l2 : List Nat) :
    Reorder.HasSortedRuns l1
    → Reorder.HasSortedRuns l2
    → (∀ a b, l1.getLast? = some a → l2.head? = some b
        → 0 < Lookup.canonicalCombiningClass b
        → Lookup.canonicalCombiningClass a
            ≤ Lookup.canonicalCombiningClass b)
    → Reorder.HasSortedRuns (l1 ++ l2) := by
  induction l1 with
  | nil =>
    intros hHsrNil h2 hSeamNil
    clear hHsrNil hSeamNil
    show Reorder.HasSortedRuns ([] ++ l2)
    simp
    exact h2
  | cons x rest ih =>
    intros h1 h2 hSeam
    cases rest with
    | nil =>
      cases l2 with
      | nil =>
        show Reorder.HasSortedRuns [x]
        simp
      | cons b rest2 =>
        show Reorder.HasSortedRuns (x :: b :: rest2)
        rw [Reorder.HasSortedRuns_cons_cons]
        refine ⟨?pair_xb, h2⟩
        intro hBpos
        exact hSeam x b rfl rfl hBpos
    | cons y rest2 =>
      show Reorder.HasSortedRuns (x :: y :: (rest2 ++ l2))
      rw [Reorder.HasSortedRuns_cons_cons]
      rw [Reorder.HasSortedRuns_cons_cons] at h1
      obtain ⟨hPair_xy, hHSR_yrest⟩ := h1
      refine ⟨hPair_xy, ?recHSR⟩
      have hSeamRest :
          ∀ a b, (y :: rest2).getLast? = some a → l2.head? = some b
              → 0 < Lookup.canonicalCombiningClass b
              → Lookup.canonicalCombiningClass a
                  ≤ Lookup.canonicalCombiningClass b := by
        intros a b hLast hHead hBpos
        apply hSeam a b _ hHead hBpos
        have hConsEq : (x :: y :: rest2).getLast? = (y :: rest2).getLast? := rfl
        rw [hConsEq]
        exact hLast
      exact ih hHSR_yrest h2 hSeamRest

-- ═══════════════════════════════════════════════════════════════════════════════
-- §6 PARTITION AT A CCC THRESHOLD
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The high-ccc trailing suffix of a list, partitioned at `cp_ccc`. -/
def trailingHigh (l : List Nat) (cp_ccc : Nat) : List Nat :=
  (l.reverse.takeWhile (fun x =>
    decide (cp_ccc < Lookup.canonicalCombiningClass x))).reverse

/-- The low-ccc prefix complement of `trailingHigh`. -/
def trailingLow (l : List Nat) (cp_ccc : Nat) : List Nat :=
  (l.reverse.dropWhile (fun x =>
    decide (cp_ccc < Lookup.canonicalCombiningClass x))).reverse

/-- The partition reconstructs the original list. -/
theorem trailingLow_append_trailingHigh (l : List Nat) (cp_ccc : Nat) :
    trailingLow l cp_ccc ++ trailingHigh l cp_ccc = l := by
  unfold trailingLow trailingHigh
  rw [← List.reverse_append, List.takeWhile_append_dropWhile]
  exact List.reverse_reverse l

/-- Every element of the high suffix has CCC > `cp_ccc`. -/
theorem trailingHigh_all_gt (l : List Nat) (cp_ccc : Nat) :
    ∀ x ∈ trailingHigh l cp_ccc, cp_ccc < Lookup.canonicalCombiningClass x := by
  intros x hx
  unfold trailingHigh at hx
  rw [List.mem_reverse] at hx
  have hPred : decide (cp_ccc < Lookup.canonicalCombiningClass x) = true :=
    mem_takeWhile_imp_pred
      (fun y => decide (cp_ccc < Lookup.canonicalCombiningClass y))
      l.reverse x hx
  exact of_decide_eq_true hPred

/-- Every element of the high suffix is a non-starter. -/
theorem trailingHigh_all_pos (l : List Nat) (cp_ccc : Nat) :
    ∀ x ∈ trailingHigh l cp_ccc, 0 < Lookup.canonicalCombiningClass x := by
  intros x hx
  have := trailingHigh_all_gt l cp_ccc x hx
  omega

/-- When the high suffix is non-empty, the low prefix's last element
    has CCC ≤ `cp_ccc`. -/
theorem trailingLow_last_le_when_high_nonempty
    (l : List Nat) (cp_ccc : Nat) :
    ∀ x, (trailingLow l cp_ccc).getLast? = some x →
      Lookup.canonicalCombiningClass x ≤ cp_ccc := by
  intros x hLast
  unfold trailingLow at hLast
  rw [List.getLast?_reverse] at hLast
  have hNotP := List.head?_dropWhile_not
                  (fun x => decide (cp_ccc < Lookup.canonicalCombiningClass x)) l.reverse
  rw [hLast] at hNotP
  have hNotLt : ¬ cp_ccc < Lookup.canonicalCombiningClass x := by
    intro hLt
    have hDecide := decide_eq_true hLt
    rw [hNotP] at hDecide
    exact Bool.noConfusion hDecide
  omega

-- ═══════════════════════════════════════════════════════════════════════════════
-- §7 SNOC SEAM HSR BOUND
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The seam pair `(y, cp)` is in the zip-with-tail of `pre ++ [y, cp]`. -/
theorem zip_tail_mem_seam (pre : List Nat) (y cp : Nat) :
    (y, cp) ∈ ((pre ++ [y, cp]).zip (pre ++ [y, cp]).tail) := by
  induction pre with
  | nil =>
    show (y, cp) ∈ ([y, cp].zip [cp])
    simp [List.zip_cons_cons]
  | cons p ps ih =>
    match ps with
    | [] =>
      show (y, cp) ∈ ((p :: [y, cp]).zip [y, cp])
      simp [List.zip_cons_cons]
    | q :: more =>
      show (y, cp) ∈ ((p :: q :: more ++ [y, cp]).zip
                       (p :: q :: more ++ [y, cp]).tail)
      have hT : (p :: q :: more ++ [y, cp]).tail
                = q :: more ++ [y, cp] := rfl
      rw [hT]
      have hZip : (p :: q :: more ++ [y, cp]).zip
                    (q :: more ++ [y, cp])
               = (p, q) :: ((q :: more ++ [y, cp]).zip
                              (more ++ [y, cp])) := rfl
      rw [hZip]
      right
      exact ih

/-- Under HSR snoc-extension `arr ++ #[cp]` with `cp` non-starter,
    `arr`'s last element has CCC bounded above by `ccc cp`. -/
theorem hasSortedRunsBool_snoc_le
    (arr : Array Nat) (cp y : Nat)
    (hHSR : NFC.hasSortedRunsBool (arr ++ #[cp]).toList = true)
    (hLast : arr.toList.getLast? = some y)
    (hCp_pos : 0 < Lookup.canonicalCombiningClass cp) :
    Lookup.canonicalCombiningClass y ≤ Lookup.canonicalCombiningClass cp := by
  rcases List.eq_nil_or_concat arr.toList with hNil | ⟨pre, last, hConcat⟩
  · rw [hNil] at hLast
    exact absurd hLast (by simp)
  · have hConcatApp : arr.toList = pre ++ [last] := by
      rw [hConcat]
      simp
    have hLastEq : y = last := by
      rw [hConcatApp] at hLast
      rw [getLast?_concat_singleton pre last] at hLast
      exact ((Option.some.injEq last y).mp hLast).symm
    rw [hLastEq]
    have hListEq : (arr ++ #[cp]).toList = pre ++ [last, cp] := by
      rw [Array.toList_append, hConcatApp]
      show pre ++ [last] ++ (#[cp] : Array Nat).toList = pre ++ [last, cp]
      have hSingleton : (#[cp] : Array Nat).toList = [cp] := rfl
      rw [hSingleton]
      simp [List.append_assoc]
    rw [hListEq] at hHSR
    have hZipMem : (last, cp) ∈ ((pre ++ [last, cp]).zip (pre ++ [last, cp]).tail) :=
      zip_tail_mem_seam pre last cp
    unfold NFC.hasSortedRunsBool at hHSR
    rw [List.all_eq_true] at hHSR
    have hPair := hHSR (last, cp) hZipMem
    rw [Bool.or_eq_true] at hPair
    rcases hPair with hZ | hLe
    · have hCpZero : Lookup.canonicalCombiningClass cp = 0 :=
        of_decide_eq_true hZ
      omega
    · exact of_decide_eq_true hLe

-- ═══════════════════════════════════════════════════════════════════════════════
-- §8 ALL-NONSTARTER COMPOSE PASSES THROUGH
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Leading non-starter from a `none` starter state appends to
    `emitted`; starter, buffer, maxCCC unchanged. -/
theorem stepCompose_leading_nonstarter
    (S : Compose.ComposeState) (cp : Nat)
    (hSt : S.starter = none)
    (hCp_pos : 0 < Lookup.canonicalCombiningClass cp) :
    Compose.stepCompose S cp
      = { emitted := S.emitted ++ #[cp]
          starter := none
          buffer  := S.buffer
          maxCCC  := S.maxCCC } := by
  unfold Compose.stepCompose
  rw [hSt]
  have hCpNe : Lookup.canonicalCombiningClass cp ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hCp_pos
  simp [hCpNe]

/-- Foldl over an all-non-starter list from a `none` starter state:
    state evolves only via `emitted` accumulation. -/
theorem foldl_all_nonstarter_eq
    (L : List Nat) :
    ∀ (S : Compose.ComposeState),
      S.starter = none
      → (∀ x ∈ L, 0 < Lookup.canonicalCombiningClass x)
      → L.foldl Compose.stepCompose S
        = { emitted := S.emitted ++ L.toArray
            starter := none
            buffer  := S.buffer
            maxCCC  := S.maxCCC } := by
  induction L with
  | nil =>
    intros S hSStarter hAllPos
    clear hAllPos
    show ([] : List Nat).foldl Compose.stepCompose S
       = { emitted := S.emitted ++ ([] : List Nat).toArray
           starter := none
           buffer  := S.buffer
           maxCCC  := S.maxCCC }
    have hListToArr : ([] : List Nat).toArray = (#[] : Array Nat) := rfl
    rw [hListToArr]
    show S = { emitted := S.emitted ++ #[]
               starter := none
               buffer  := S.buffer
               maxCCC  := S.maxCCC }
    have hAppNil : S.emitted ++ #[] = S.emitted := by simp
    rw [hAppNil]
    obtain ⟨E, st, B, M⟩ := S
    simp at hSStarter
    rw [hSStarter]
  | cons x rest ih =>
    intros S hSStarter hAllPos
    have hXpos : 0 < Lookup.canonicalCombiningClass x :=
      hAllPos x List.mem_cons_self
    have hRestPos : ∀ y ∈ rest, 0 < Lookup.canonicalCombiningClass y :=
      fun y hy => hAllPos y (List.mem_cons.mpr (Or.inr hy))
    have hStep := stepCompose_leading_nonstarter S x hSStarter hXpos
    show rest.foldl Compose.stepCompose (Compose.stepCompose S x)
       = { emitted := S.emitted ++ (x :: rest).toArray
           starter := none
           buffer  := S.buffer
           maxCCC  := S.maxCCC }
    rw [hStep]
    have hStepStarter :
        ({ emitted := S.emitted ++ #[x]
           starter := none
           buffer  := S.buffer
           maxCCC  := S.maxCCC } : Compose.ComposeState).starter
          = none := rfl
    have hIhResult := ih
        { emitted := S.emitted ++ #[x]
          starter := none
          buffer  := S.buffer
          maxCCC  := S.maxCCC }
        hStepStarter hRestPos
    rw [hIhResult]
    congr 1
    rw [Array.append_assoc]
    congr 1
    exact (List.toArray_cons x rest).symm

/-- `compose Z = Z` when `Z` is all non-starters. -/
theorem compose_id_when_all_nonstarter
    (Z : Array Nat)
    (hAllPos : ∀ x ∈ Z.toList, 0 < Lookup.canonicalCombiningClass x) :
    Compose.compose Z = Z := by
  unfold Compose.compose
  rw [← Array.foldl_toList]
  have hFold := foldl_all_nonstarter_eq Z.toList Compose.initialState rfl hAllPos
  rw [hFold]
  unfold Compose.flushCompose
  show Compose.initialState.emitted ++ Z.toList.toArray
        ++ ([] : List Nat).reverse.toArray = Z
  show #[] ++ Z.toList.toArray ++ #[] = Z
  simp

-- ═══════════════════════════════════════════════════════════════════════════════
-- §9 SWAP-CASE STRUCTURE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HSR-fail on `toNFD xs ++ #[cp]` forces `trailingHigh` non-empty:
    if it were empty, all elements of `toNFD xs` would have CCC ≤
    ccc(cp), and `HasSortedRuns_append_singleton` would give HSR on
    `(toNFD xs) ++ [cp]`, contradicting the failure. -/
theorem trailingHigh_nonempty_in_swap_case
    (xs : Array Nat) (cp : Nat)
    (hHSR_fail : ¬ NFC.hasSortedRunsBool (toNFD xs ++ #[cp]).toList = true) :
    trailingHigh (toNFD xs).toList (Lookup.canonicalCombiningClass cp) ≠ [] := by
  intro hHighEmpty
  apply hHSR_fail
  have hZ_HSR : Reorder.HasSortedRuns (toNFD xs).toList :=
    (NFD.toNFD_output_HSR_and_FullyDecomposed xs).1
  have hSeam : 0 < Lookup.canonicalCombiningClass cp
              → ∀ a, (toNFD xs).toList.getLast? = some a
                  → Lookup.canonicalCombiningClass a
                      ≤ Lookup.canonicalCombiningClass cp := by
    intros hCpPosLocal a hLast
    clear hCpPosLocal
    rw [List.getLast?_eq_head?_reverse] at hLast
    unfold trailingHigh at hHighEmpty
    rw [List.reverse_eq_nil_iff] at hHighEmpty
    cases hRev : (toNFD xs).toList.reverse with
    | nil =>
      rw [hRev] at hLast
      exact absurd hLast (by simp)
    | cons z zs =>
      rw [hRev] at hLast
      have hHeadVal : (z :: zs).head? = some z := rfl
      rw [hHeadVal] at hLast
      have hZeq : z = a := (Option.some.injEq z a).mp hLast
      rw [hRev] at hHighEmpty
      by_cases hPz : Lookup.canonicalCombiningClass cp
                        < Lookup.canonicalCombiningClass z
      · exfalso
        have hTakeWhileNonEmpty :
            (z :: zs).takeWhile (fun x =>
              decide (Lookup.canonicalCombiningClass cp
                        < Lookup.canonicalCombiningClass x))
              ≠ [] := by
          rw [List.takeWhile_cons]
          have hCondTrue : decide (Lookup.canonicalCombiningClass cp
                                    < Lookup.canonicalCombiningClass z) = true :=
            decide_eq_true hPz
          rw [if_pos hCondTrue]
          simp
        exact hTakeWhileNonEmpty hHighEmpty
      · rw [← hZeq]
        omega
  apply (NFC.hasSortedRunsBool_iff_HasSortedRuns _).mpr
  rw [Array.toList_append]
  have hSingleton : (#[cp] : Array Nat).toList = [cp] := rfl
  rw [hSingleton]
  exact HasSortedRuns_append_singleton (toNFD xs).toList cp hZ_HSR hSeam

/-- In the swap case, `lowL` contains a starter. Contrapositive proof:
    if `lowL` had no starter, `toNFD xs` would be all non-starters
    (since `highL` is also all non-starters), so `compose (toNFD xs)
    = toNFD xs` (pass-through); combined with the IH `compose (toNFD
    xs) = xs`, this gives `xs = toNFD xs`, so `xs.last ∈ highL` with
    `ccc > ccc cp`, contradicting HSR's seam bound. -/
theorem lowL_has_starter_in_swap_case
    (xs : Array Nat) (cp : Nat)
    (hCp_ccc_pos : 0 < Lookup.canonicalCombiningClass cp)
    (hPrefix : toNFC xs = xs)
    (hHSR_outer : NFC.hasSortedRunsBool (xs ++ #[cp]).toList = true)
    (hHSR_inner_fail :
      ¬ NFC.hasSortedRunsBool (toNFD xs ++ #[cp]).toList = true) :
    ∃ s ∈ trailingLow (toNFD xs).toList (Lookup.canonicalCombiningClass cp),
      Lookup.canonicalCombiningClass s = 0 := by
  have hPartition : (toNFD xs).toList
                  = trailingLow (toNFD xs).toList (Lookup.canonicalCombiningClass cp)
                    ++ trailingHigh (toNFD xs).toList (Lookup.canonicalCombiningClass cp) :=
    (trailingLow_append_trailingHigh (toNFD xs).toList
      (Lookup.canonicalCombiningClass cp)).symm
  have hHighNonEmpty :
      trailingHigh (toNFD xs).toList (Lookup.canonicalCombiningClass cp) ≠ [] :=
    trailingHigh_nonempty_in_swap_case xs cp hHSR_inner_fail
  have hHighPos :
      ∀ b ∈ trailingHigh (toNFD xs).toList (Lookup.canonicalCombiningClass cp),
        0 < Lookup.canonicalCombiningClass b :=
    trailingHigh_all_pos (toNFD xs).toList (Lookup.canonicalCombiningClass cp)
  have hHighGt :
      ∀ b ∈ trailingHigh (toNFD xs).toList (Lookup.canonicalCombiningClass cp),
        Lookup.canonicalCombiningClass cp < Lookup.canonicalCombiningClass b :=
    trailingHigh_all_gt (toNFD xs).toList (Lookup.canonicalCombiningClass cp)
  refine Classical.byContradiction (fun hNoStarter => ?contradictionPath)
  have hAllPosLow :
      ∀ x ∈ trailingLow (toNFD xs).toList (Lookup.canonicalCombiningClass cp),
        0 < Lookup.canonicalCombiningClass x := by
    intros x hx
    refine Classical.byContradiction (fun hNotPos => ?innerPath)
    have hCccZero : Lookup.canonicalCombiningClass x = 0 := by omega
    exact hNoStarter ⟨x, hx, hCccZero⟩
  have hAllPosToNFD : ∀ x ∈ (toNFD xs).toList,
                        0 < Lookup.canonicalCombiningClass x := by
    intros x hx
    rw [hPartition] at hx
    rcases List.mem_append.mp hx with hLowMem | hHighMem
    · exact hAllPosLow x hLowMem
    · exact hHighPos x hHighMem
  have hPassThrough : Compose.compose (toNFD xs) = toNFD xs :=
    compose_id_when_all_nonstarter (toNFD xs) hAllPosToNFD
  have hXsEq : xs = toNFD xs :=
    hPrefix.symm.trans hPassThrough
  obtain ⟨hd, tl, hHighEq⟩ :
      ∃ hd tl,
        trailingHigh (toNFD xs).toList (Lookup.canonicalCombiningClass cp)
          = hd :: tl := by
    cases hHigh : trailingHigh (toNFD xs).toList (Lookup.canonicalCombiningClass cp) with
    | nil => exact absurd hHigh hHighNonEmpty
    | cons hd tl => exact ⟨hd, tl, rfl⟩
  have hHighEq_ne_nil : (hd :: tl) ≠ ([] : List Nat) :=
    List.cons_ne_nil hd tl
  have hZHighMem :
      (hd :: tl).getLast hHighEq_ne_nil
        ∈ trailingHigh (toNFD xs).toList (Lookup.canonicalCombiningClass cp) := by
    rw [hHighEq]
    exact List.getLast_mem hHighEq_ne_nil
  have hZHighGt :
      Lookup.canonicalCombiningClass cp
        < Lookup.canonicalCombiningClass ((hd :: tl).getLast hHighEq_ne_nil) :=
    hHighGt _ hZHighMem
  have hXsLast :
      xs.toList.getLast? = some ((hd :: tl).getLast hHighEq_ne_nil) := by
    rw [hXsEq, hPartition]
    rw [List.getLast?_append]
    have hHighGetLast :
        (trailingHigh (toNFD xs).toList
          (Lookup.canonicalCombiningClass cp)).getLast?
          = some ((hd :: tl).getLast hHighEq_ne_nil) := by
      rw [hHighEq]
      exact List.getLast?_eq_some_getLast hHighEq_ne_nil
    rw [hHighGetLast]
    rfl
  have hSeamBound :
      Lookup.canonicalCombiningClass ((hd :: tl).getLast hHighEq_ne_nil)
        ≤ Lookup.canonicalCombiningClass cp :=
    hasSortedRunsBool_snoc_le xs cp ((hd :: tl).getLast hHighEq_ne_nil)
      hHSR_outer hXsLast hCp_ccc_pos
  omega

-- ═══════════════════════════════════════════════════════════════════════════════
-- §10 HSR-PRESERVES VARIANT OF NON-STARTER SNOC
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The HSR-preserves variant of the non-starter snoc closure: when
    `toNFD xs ++ #[cp]` is already HSR, `reorder` is the identity on
    it, so the boundary collapses to `compose_qcY_linear` + IH. -/
theorem nfc_snoc_atomic_nonstarter_hsr_preserves
    (xs : Array Nat) (cp : Nat)
    (hQC : nfcQCValue cp = .Y)
    (hCccPos : 0 < Lookup.canonicalCombiningClass cp)
    (hDecomp : Lookup.canonicalDecomposition cp = #[])
    (hNotHangul : Hangul.isHangulSyllable cp = false)
    (hHsrToNFD : Reorder.HasSortedRuns (toNFD xs ++ #[cp]).toList)
    (hPrefix : toNFC xs = xs) :
    toNFC (xs ++ #[cp]) = xs ++ #[cp] := by
  have hFCD : Decompose.fullCanonicalDecompose cp = #[cp] :=
    decomp_atomic_id cp hDecomp hNotHangul
  show Compose.compose (toNFD (xs ++ #[cp])) = xs ++ #[cp]
  have hToNFDExpand : toNFD (xs ++ #[cp])
                    = Reorder.reorder (toNFD xs ++ #[cp]) := by
    unfold toNFD
    rw [Distribute.decomposeSequence_append xs #[cp]]
    rw [Distribute.decomposeSequence_singleton, hFCD]
    exact ReorderAppend.reorder_append_absorbing_nonstarter
      (Decompose.decomposeSequence xs) cp hCccPos
  rw [hToNFDExpand]
  have hReorderId : Reorder.reorder (toNFD xs ++ #[cp])
                  = toNFD xs ++ #[cp] :=
    Reorder.reorder_id_on_HasSortedRuns (toNFD xs ++ #[cp]) hHsrToNFD
  rw [hReorderId]
  rw [compose_qcY_linear (toNFD xs) cp hQC]
  show Compose.compose (toNFD xs) ++ #[cp] = xs ++ #[cp]
  show toNFC xs ++ #[cp] = xs ++ #[cp]
  rw [hPrefix]

end Unicode.Normalization.ComposeKernelSupport
