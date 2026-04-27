/-
  Unicode.Normalization.ComposeBufferStructure

  Two foundational structural facts about `Compose.compose`'s post-
  fold state and its relation to the output:

    * **Buffer-as-trailing-run** (`compose_output_form_active`) —
      when the post-fold state has `starter = some st`, `compose`'s
      output is `emitted ++ #[st] ++ buffer.reverse`. The trailing
      portion of the output IS the buffer reversed, by direct
      unfolding of `flushCompose`.
    * **Buffer CCC bound under HSR** (`compose_buffer_ccc_bound`) —
      when `compose Z ++ #[cp]` is HSR with `cp` a non-starter, every
      element of the post-fold buffer has `ccc ≤ ccc cp`. The buffer
      reversed appears in the output as the trailing nonstarter run;
      HSR on the snoc forces every trailing-run element to have CCC
      bounded by the snoc element.
    * **Buffer-or-fire dichotomy**
      (`fold_nonstarter_buffer_or_fire`) — a non-starter processed
      at the strict-max branch with `primaryComposite? = none` ends
      up in the final buffer. Equivalently, if a non-starter does
      NOT end up in the final buffer, it must have primary-fired
      (the strict-max-with-some branch).

  Together they discharge the chain-validity precondition required
  by `ComposeNonstarterSlide.compose_slide_qcY` directly from HSR +
  IH `compose Z = xs`. The chain elements have `ccc > ccc cp`, but
  the buffer-bound forces buffered elements to have `ccc ≤ ccc cp`,
  so chain elements cannot end up in the buffer; by the dichotomy,
  they must primary-fire.
-/

import Unicode.Normalization.Compose
import Unicode.Normalization.ComposeInversion
import Unicode.Normalization.ComposeBlockAdditive
import Unicode.Normalization.ComposeNonstarterSlide
import Unicode.Normalization.NFC

namespace Unicode.Normalization.ComposeBufferStructure

open Unicode.Normalization
open Unicode.Normalization.NFC (nfcQCValue hasSortedRunsBool)
open Unicode.Normalization.ComposeInversion (ComposeStateValid)
open Unicode.Normalization.ComposeBlockAdditive (foldl_stepCompose_strongValid_array)
open Unicode.Normalization.ComposeNonstarterSlide (PrimaryFiresChain)

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1 OUTPUT FORM WITH ACTIVE STARTER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Output form (active starter).** When `compose`'s post-fold
    state has `starter = some st`, the output is
    `emitted ++ #[st] ++ buffer.reverse`. Direct from the
    `flushCompose` definition. -/
theorem compose_output_form_active
    (Z : Array Nat) (st : Nat)
    (hSt : (Z.foldl Compose.stepCompose Compose.initialState).starter = some st) :
    Compose.compose Z =
      (Z.foldl Compose.stepCompose Compose.initialState).emitted
        ++ #[st]
        ++ (Z.foldl Compose.stepCompose Compose.initialState).buffer.reverse.toArray := by
  unfold Compose.compose Compose.flushCompose
  rw [hSt]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2 ADJACENT-PAIR HSR EXTRACTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- An adjacent pair `(a, b)` is in the list's `zip-with-tail` for
    any prefix-suffix decomposition `prefix ++ a :: b :: rest`. -/
theorem zip_tail_mem_adjacent
    (prefix_l : List Nat) (a b : Nat) (rest : List Nat) :
    (a, b) ∈ ((prefix_l ++ a :: b :: rest).zip
               (prefix_l ++ a :: b :: rest).tail) := by
  induction prefix_l with
  | nil =>
    show (a, b) ∈ ((a :: b :: rest).zip (b :: rest))
    simp [List.zip_cons_cons]
  | cons p ps ih =>
    match ps with
    | [] =>
      show (a, b) ∈ ((p :: a :: b :: rest).zip (a :: b :: rest))
      simp [List.zip_cons_cons]
    | q :: more =>
      show (a, b) ∈ ((p :: q :: more ++ a :: b :: rest).zip
                      (p :: q :: more ++ a :: b :: rest).tail)
      have hT : (p :: q :: more ++ a :: b :: rest).tail
                = q :: more ++ a :: b :: rest := rfl
      rw [hT]
      have hZip : (p :: q :: more ++ a :: b :: rest).zip
                    (q :: more ++ a :: b :: rest)
               = (p, q) :: ((q :: more ++ a :: b :: rest).zip
                              (more ++ a :: b :: rest)) := rfl
      rw [hZip]
      right
      exact ih

/-- HSR truth on a list with adjacent non-starter pair `(x, y)` (with
    `y` non-starter) gives `ccc x ≤ ccc y`. Direct from the predicate
    definition. -/
theorem hasSortedRunsBool_pair_le
    (l : List Nat) (x y : Nat)
    (hHSR : hasSortedRunsBool l = true)
    (hMem : (x, y) ∈ l.zip l.tail)
    (hYpos : 0 < Lookup.canonicalCombiningClass y) :
    Lookup.canonicalCombiningClass x ≤ Lookup.canonicalCombiningClass y := by
  unfold hasSortedRunsBool at hHSR
  rw [List.all_eq_true] at hHSR
  have hAt := hHSR (x, y) hMem
  rw [Bool.or_eq_true] at hAt
  rcases hAt with hZero | hLe
  · have hYzero : Lookup.canonicalCombiningClass y = 0 := of_decide_eq_true hZero
    omega
  · exact of_decide_eq_true hLe

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3 HSR-RUN BOUND VIA ADJACENT-PAIR INDUCTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Trailing-run CCC bound under HSR.** Every element of a
    non-starter run that sits between an arbitrary prefix and a
    non-starter sentinel `cp` has CCC bounded by `ccc cp`. The
    induction walks adjacent pairs (head, head's-successor) and
    transports the bound through.

    Adjacent-pair induction on the run, transporting the bound
    through. -/
theorem hasSortedRunsBool_run_le_snoc
    (run : List Nat) :
    ∀ (prefix_l : List Nat) (cp : Nat),
      hasSortedRunsBool (prefix_l ++ run ++ [cp]) = true
      → (∀ r ∈ run, 0 < Lookup.canonicalCombiningClass r)
      → 0 < Lookup.canonicalCombiningClass cp
      → ∀ r ∈ run, Lookup.canonicalCombiningClass r
                      ≤ Lookup.canonicalCombiningClass cp := by
  induction run with
  | nil =>
    intros prefix_l cp hHSR hRunPos hCpPos r hr
    clear prefix_l hHSR hRunPos hCpPos
    exact absurd hr List.not_mem_nil
  | cons hd tl ih =>
    intros prefix_l cp hHSR hRunPos hCpPos r hr
    rcases List.mem_cons.mp hr with hRhd | hRtl
    · -- r = hd: extract bound from adjacency.
      cases tl with
      | nil =>
        -- run = [hd]. Adjacent pair (hd, cp).
        have hListEq : prefix_l ++ [hd] ++ [cp] = prefix_l ++ hd :: cp :: [] := by
          simp [List.append_assoc]
        rw [hListEq] at hHSR
        have hMem : (hd, cp) ∈ ((prefix_l ++ hd :: cp :: []).zip
                                  (prefix_l ++ hd :: cp :: []).tail) :=
          zip_tail_mem_adjacent prefix_l hd cp []
        have hLe := hasSortedRunsBool_pair_le
                      (prefix_l ++ hd :: cp :: []) hd cp hHSR hMem hCpPos
        rw [hRhd]; exact hLe
      | cons hd2 tl2 =>
        -- run = hd :: hd2 :: tl2. Adjacent pair (hd, hd2).
        have hHd2Pos : 0 < Lookup.canonicalCombiningClass hd2 :=
          hRunPos hd2 (List.mem_cons.mpr (Or.inr List.mem_cons_self))
        have hListEq : prefix_l ++ (hd :: hd2 :: tl2) ++ [cp]
                     = prefix_l ++ hd :: hd2 :: (tl2 ++ [cp]) := by
          simp [List.append_assoc]
        rw [hListEq] at hHSR
        have hMem : (hd, hd2) ∈ ((prefix_l ++ hd :: hd2 :: (tl2 ++ [cp])).zip
                                   (prefix_l ++ hd :: hd2 :: (tl2 ++ [cp])).tail) :=
          zip_tail_mem_adjacent prefix_l hd hd2 (tl2 ++ [cp])
        have hHdLeHd2 := hasSortedRunsBool_pair_le
                            (prefix_l ++ hd :: hd2 :: (tl2 ++ [cp]))
                            hd hd2 hHSR hMem hHd2Pos
        -- IH on the tail.
        have hHsrIh : hasSortedRunsBool
                          ((prefix_l ++ [hd]) ++ (hd2 :: tl2) ++ [cp]) = true := by
          have hRw : (prefix_l ++ [hd]) ++ (hd2 :: tl2) ++ [cp]
                   = prefix_l ++ hd :: hd2 :: (tl2 ++ [cp]) := by
            simp [List.append_assoc]
          rw [hRw]; exact hHSR
        have hRunTailPos : ∀ x ∈ hd2 :: tl2, 0 < Lookup.canonicalCombiningClass x := by
          intros x hx
          exact hRunPos x (List.mem_cons.mpr (Or.inr hx))
        have hIhResult := ih (prefix_l ++ [hd]) cp hHsrIh hRunTailPos hCpPos
                              hd2 List.mem_cons_self
        rw [hRhd]; omega
    · -- r ∈ tl. IH.
      have hHsrIh : hasSortedRunsBool
                        ((prefix_l ++ [hd]) ++ tl ++ [cp]) = true := by
        have hRw : (prefix_l ++ [hd]) ++ tl ++ [cp]
                 = prefix_l ++ (hd :: tl) ++ [cp] := by
          simp [List.append_assoc]
        rw [hRw]; exact hHSR
      have hRunTailPos : ∀ x ∈ tl, 0 < Lookup.canonicalCombiningClass x := by
        intros x hx
        exact hRunPos x (List.mem_cons.mpr (Or.inr hx))
      exact ih (prefix_l ++ [hd]) cp hHsrIh hRunTailPos hCpPos r hRtl

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4 BUFFER-CCC BOUND UNDER HSR
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Buffer-CCC bound under HSR.** When the post-fold state has an
    active starter and `compose Z ++ #[cp]` is HSR with `cp` a non-
    starter, every buffered element has CCC bounded by `ccc cp`. The
    buffer reversed appears as the trailing nonstarter run of
    `compose Z`; HSR-on-snoc forces every trailing-run element to
    have CCC ≤ ccc cp. -/
theorem compose_buffer_ccc_bound
    (Z : Array Nat) (cp : Nat)
    (hCpPos : 0 < Lookup.canonicalCombiningClass cp)
    (hSt : (Z.foldl Compose.stepCompose Compose.initialState).starter.isSome
              = true)
    (hHSR : hasSortedRunsBool (Compose.compose Z ++ #[cp]).toList = true) :
    ∀ m ∈ (Z.foldl Compose.stepCompose Compose.initialState).buffer,
      Lookup.canonicalCombiningClass m ≤ Lookup.canonicalCombiningClass cp := by
  intros m hMem
  obtain ⟨st, hStAct⟩ := Option.isSome_iff_exists.mp hSt
  -- Express compose Z's output, then rewrite HSR through it.
  have hForm := compose_output_form_active Z st hStAct
  rw [hForm] at hHSR
  -- The buffer's contents (reversed) are the trailing run of the output.
  have hStrongValid := foldl_stepCompose_strongValid_array Z
  have hValid : ComposeStateValid (Z.foldl Compose.stepCompose Compose.initialState) :=
    hStrongValid.1
  have hRevPos :
      ∀ r ∈ (Z.foldl Compose.stepCompose Compose.initialState).buffer.reverse,
        0 < Lookup.canonicalCombiningClass r := by
    intros r hr
    exact (hValid.2 r (List.mem_reverse.mp hr)).1
  -- Re-shape the HSR list to match `prefix ++ run ++ [cp]`.
  have hToList :
      ((Z.foldl Compose.stepCompose Compose.initialState).emitted
        ++ #[st]
        ++ (Z.foldl Compose.stepCompose Compose.initialState).buffer.reverse.toArray
        ++ #[cp]).toList
        = ((Z.foldl Compose.stepCompose Compose.initialState).emitted.toList
            ++ [st])
          ++ (Z.foldl Compose.stepCompose Compose.initialState).buffer.reverse
          ++ [cp] := by
    simp [Array.toList_append, List.append_assoc]
  rw [hToList] at hHSR
  have hRunBound :
      ∀ r ∈ (Z.foldl Compose.stepCompose Compose.initialState).buffer.reverse,
        Lookup.canonicalCombiningClass r ≤ Lookup.canonicalCombiningClass cp :=
    hasSortedRunsBool_run_le_snoc
      (Z.foldl Compose.stepCompose Compose.initialState).buffer.reverse
      ((Z.foldl Compose.stepCompose Compose.initialState).emitted.toList
        ++ [st])
      cp hHSR hRevPos hCpPos
  exact hRunBound m (List.mem_reverse.mpr hMem)

-- ═══════════════════════════════════════════════════════════════════════════════
-- §5 BUFFER-OR-FIRE DICHOTOMY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Buffer-or-fire dichotomy for non-starter input at strict-max.**
    A non-starter `m` arriving at a state with `starter = some st`
    and `ccc m > maxCCC` either primary-fires (post-state has
    `starter := some p`) or goes to the buffer (post-state has
    `buffer := m :: buffer`). The two cases are mutually exclusive
    and cover all of stepCompose's strict-max branch. -/
theorem stepCompose_strictMax_buffer_or_fire
    (s : Compose.ComposeState) (m st : Nat)
    (hSt : s.starter = some st)
    (hCccPos : 0 < Lookup.canonicalCombiningClass m)
    (hMax : ¬ Lookup.canonicalCombiningClass m ≤ s.maxCCC) :
    (∃ p, Compose.stepCompose s m = { s with starter := some p }
            ∧ Compose.primaryComposite? st m = some p) ∨
    (Compose.stepCompose s m =
      { s with
        buffer := m :: s.buffer
        maxCCC := Nat.max s.maxCCC (Lookup.canonicalCombiningClass m) }
        ∧ Compose.primaryComposite? st m = none) := by
  have hCccNe : Lookup.canonicalCombiningClass m ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hCccPos
  set_option linter.unusedSimpArgs false in
  unfold Compose.stepCompose
  simp only [hSt]
  rw [if_neg hCccNe, if_neg hMax]
  cases hPC : Compose.primaryComposite? st m with
  | none =>
    right
    exact ⟨rfl, rfl⟩
  | some p =>
    left
    exact ⟨p, rfl, rfl⟩

/-- **Non-firing non-starter ends up in the buffer.** When `m` is a
    non-starter at strict-max with `primaryComposite? = none`, the
    post-state has `m :: s.buffer` as the buffer. The element stays
    in the buffer through subsequent processing as long as no flush
    occurs (no starter input, no primary firing that resets buffer
    elements — but Case 7 keeps buffer unchanged). -/
theorem stepCompose_strictMax_no_fire_to_buffer
    (s : Compose.ComposeState) (m st : Nat)
    (hSt : s.starter = some st)
    (hCccPos : 0 < Lookup.canonicalCombiningClass m)
    (hMax : ¬ Lookup.canonicalCombiningClass m ≤ s.maxCCC)
    (hNoFire : Compose.primaryComposite? st m = none) :
    Compose.stepCompose s m =
      { s with
        buffer := m :: s.buffer
        maxCCC := Nat.max s.maxCCC (Lookup.canonicalCombiningClass m) } := by
  have hCccNe : Lookup.canonicalCombiningClass m ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hCccPos
  set_option linter.unusedSimpArgs false in
  unfold Compose.stepCompose
  simp only [hSt]
  rw [if_neg hCccNe, if_neg hMax, hNoFire]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §6 NON-STARTER PROCESSING PRESERVES BUFFER MEMBERSHIP
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Buffer is monotone-prepended through non-starter processing.**
    Folding `stepCompose` over a list of non-starters preserves any
    pre-existing buffer membership. Each step either prepends the
    non-starter (blocked or strict-max-no-fire) or leaves the buffer
    unchanged (strict-max-fire); both cases preserve membership. -/
theorem foldl_stepCompose_buffer_monotone_nonstarters
    (L : List Nat) (s : Compose.ComposeState)
    (hAllNs : ∀ b ∈ L, 0 < Lookup.canonicalCombiningClass b) :
    ∀ y ∈ s.buffer, y ∈ (L.foldl Compose.stepCompose s).buffer := by
  induction L generalizing s with
  | nil =>
    intros y hy
    exact hy
  | cons head rest ih =>
    intros y hy
    have hHeadNs : 0 < Lookup.canonicalCombiningClass head :=
      hAllNs head List.mem_cons_self
    have hHeadNe : Lookup.canonicalCombiningClass head ≠ 0 :=
      Nat.pos_iff_ne_zero.mp hHeadNs
    have hBufContains : y ∈ (Compose.stepCompose s head).buffer := by
      set_option linter.unusedSimpArgs false in
      unfold Compose.stepCompose
      cases hSt : s.starter with
      | none =>
        simp only [hSt]
        rw [if_neg hHeadNe]
        exact hy
      | some st =>
        simp only [hSt]
        rw [if_neg hHeadNe]
        by_cases hMax : Lookup.canonicalCombiningClass head ≤ s.maxCCC
        · rw [if_pos hMax]
          show y ∈ head :: s.buffer
          right; exact hy
        · rw [if_neg hMax]
          cases hPC : Compose.primaryComposite? st head with
          | some p =>
            show y ∈ s.buffer
            exact hy
          | none =>
            show y ∈ head :: s.buffer
            right; exact hy
    have hRestNs : ∀ b ∈ rest, 0 < Lookup.canonicalCombiningClass b :=
      fun b hb => hAllNs b (List.mem_cons.mpr (Or.inr hb))
    simp only [List.foldl_cons]
    exact ih (Compose.stepCompose s head) hRestNs y hBufContains

-- ═══════════════════════════════════════════════════════════════════════════════
-- §7 NON-FIRING NON-STARTER ENTERS THE BUFFER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Non-starter blocked branch.** When `m` is a non-starter at a
    state with `starter = some st` and `ccc m ≤ maxCCC`, `stepCompose`
    takes the blocked branch: `m :: s.buffer` becomes the new buffer. -/
theorem stepCompose_nonstarter_blocked_form
    (s : Compose.ComposeState) (m st : Nat)
    (hSt : s.starter = some st)
    (hCccPos : 0 < Lookup.canonicalCombiningClass m)
    (hMax : Lookup.canonicalCombiningClass m ≤ s.maxCCC) :
    Compose.stepCompose s m =
      { s with
        buffer := m :: s.buffer
        maxCCC := Nat.max s.maxCCC (Lookup.canonicalCombiningClass m) } := by
  have hCccNe : Lookup.canonicalCombiningClass m ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hCccPos
  set_option linter.unusedSimpArgs false in
  unfold Compose.stepCompose
  simp only [hSt]
  rw [if_neg hCccNe, if_pos hMax]

/-- A non-starter `m` ends up in the post-step buffer whenever it
    does not primary-fire — i.e., either the strict-max branch with
    `primaryComposite? = none`, or the blocked branch (regardless of
    `primaryComposite?`). -/
theorem stepCompose_nonstarter_no_fire_buffers
    (s : Compose.ComposeState) (m st : Nat)
    (hSt : s.starter = some st)
    (hCccPos : 0 < Lookup.canonicalCombiningClass m)
    (hCondition :
      Lookup.canonicalCombiningClass m ≤ s.maxCCC
      ∨ Compose.primaryComposite? st m = none) :
    m ∈ (Compose.stepCompose s m).buffer := by
  rcases hCondition with hMax | hNoFire
  · rw [stepCompose_nonstarter_blocked_form s m st hSt hCccPos hMax]
    show m ∈ m :: s.buffer
    exact List.mem_cons_self
  · by_cases hMax : Lookup.canonicalCombiningClass m ≤ s.maxCCC
    · rw [stepCompose_nonstarter_blocked_form s m st hSt hCccPos hMax]
      show m ∈ m :: s.buffer
      exact List.mem_cons_self
    · rw [stepCompose_strictMax_no_fire_to_buffer s m st hSt hCccPos hMax hNoFire]
      show m ∈ m :: s.buffer
      exact List.mem_cons_self

-- ═══════════════════════════════════════════════════════════════════════════════
-- §8 CHAIN VALIDITY VIA BUFFER-BOUND CONTRADICTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Chain validity from buffer-bound.** For a list `B` of non-
    starters with `ccc > ccc cp` from a state with active starter,
    if the post-fold buffer's elements all have `ccc ≤ ccc cp`, then
    every element of `B` must primary-fire. The contradiction
    argument: if an element does NOT fire, it enters the buffer at
    its step (`stepCompose_nonstarter_no_fire_buffers`); buffer
    membership is preserved through subsequent non-starter
    processing (`foldl_stepCompose_buffer_monotone_nonstarters`); so
    the element ends up in the final buffer with `ccc > ccc cp`,
    violating the bound. -/
theorem chain_fires_via_buffer_bound
    (B : List Nat) (X : Array Nat) (cp : Nat)
    (hHighPos : ∀ b ∈ B, 0 < Lookup.canonicalCombiningClass b)
    (hHighGt : ∀ b ∈ B, Lookup.canonicalCombiningClass cp
                          < Lookup.canonicalCombiningClass b)
    (hXStarter : (X.foldl Compose.stepCompose Compose.initialState).starter.isSome
                    = true)
    (hBufBound : ∀ y ∈ ((X ++ B.toArray).foldl Compose.stepCompose
                            Compose.initialState).buffer,
                  Lookup.canonicalCombiningClass y
                    ≤ Lookup.canonicalCombiningClass cp) :
    PrimaryFiresChain (X.foldl Compose.stepCompose Compose.initialState) B := by
  -- Convert array foldl to list foldl on B for buffer monotonicity.
  have hBufBoundList :
      ∀ y ∈ (B.foldl Compose.stepCompose
              (X.foldl Compose.stepCompose Compose.initialState)).buffer,
        Lookup.canonicalCombiningClass y
          ≤ Lookup.canonicalCombiningClass cp := by
    intros y hy
    apply hBufBound
    rw [Array.foldl_append, ← Array.foldl_toList, List.toList_toArray]
    exact hy
  -- Induct on B.
  clear hBufBound
  induction B generalizing X with
  | nil =>
    trivial
  | cons head rest ih =>
    have hHeadPos : 0 < Lookup.canonicalCombiningClass head :=
      hHighPos head List.mem_cons_self
    have hHeadGt : Lookup.canonicalCombiningClass cp
                      < Lookup.canonicalCombiningClass head :=
      hHighGt head List.mem_cons_self
    have hRestPos : ∀ b ∈ rest, 0 < Lookup.canonicalCombiningClass b :=
      fun b hb => hHighPos b (List.mem_cons.mpr (Or.inr hb))
    have hRestGt : ∀ b ∈ rest, Lookup.canonicalCombiningClass cp
                      < Lookup.canonicalCombiningClass b :=
      fun b hb => hHighGt b (List.mem_cons.mpr (Or.inr hb))
    obtain ⟨st, hStAct⟩ :=
      Option.isSome_iff_exists.mp hXStarter
    -- Carry-contradiction: any head landing in the post-step buffer
    -- propagates to the final buffer (monotonicity), violating the
    -- bound (head's CCC > cp's CCC).
    have hCarryContradiction :
        head ∈ (Compose.stepCompose
                  (X.foldl Compose.stepCompose Compose.initialState)
                  head).buffer → False := by
      intro hHeadInBuf
      have hHeadInFinal :
          head ∈ (rest.foldl Compose.stepCompose
                    (Compose.stepCompose
                      (X.foldl Compose.stepCompose Compose.initialState)
                      head)).buffer :=
        foldl_stepCompose_buffer_monotone_nonstarters rest
          (Compose.stepCompose
            (X.foldl Compose.stepCompose Compose.initialState) head)
          hRestPos head hHeadInBuf
      have hListFinal :
          head ∈ ((head :: rest).foldl Compose.stepCompose
                    (X.foldl Compose.stepCompose Compose.initialState)).buffer := by
        simp only [List.foldl_cons]
        exact hHeadInFinal
      have hCccLe := hBufBoundList head hListFinal
      omega
    -- Strict-max for head: blocked → head buffers via the blocked-
    -- form lemma → contradiction.
    have hHeadStrictMax :
        ¬ Lookup.canonicalCombiningClass head
            ≤ (X.foldl Compose.stepCompose Compose.initialState).maxCCC := by
      intro hLe
      apply hCarryContradiction
      rw [stepCompose_nonstarter_blocked_form
            (X.foldl Compose.stepCompose Compose.initialState)
            head st hStAct hHeadPos hLe]
      show head ∈ head ::
              (X.foldl Compose.stepCompose Compose.initialState).buffer
      exact List.mem_cons_self
    -- Head primary-fires: case-split on `primaryComposite?`. The
    -- `none` case routes head to the buffer (strict-max-no-fire) →
    -- contradiction.
    have hHeadFires :
        ∃ p, Compose.primaryComposite? st head = some p := by
      cases hPC : Compose.primaryComposite? st head with
      | some p => exact ⟨p, rfl⟩
      | none =>
        exfalso
        apply hCarryContradiction
        exact stepCompose_nonstarter_no_fire_buffers
          (X.foldl Compose.stepCompose Compose.initialState)
          head st hStAct hHeadPos (Or.inr hPC)
    obtain ⟨p, hPC⟩ := hHeadFires
    refine ⟨st, p, hStAct, hHeadPos, hHeadStrictMax, hPC, ?recur⟩
    -- Recursion: re-fold X ++ #[head] gives the post-head state, with
    -- starter updated to `some p` by `stepCompose_primary_fire_form`.
    have hStepEq :
        Compose.stepCompose
            (X.foldl Compose.stepCompose Compose.initialState) head
          = { (X.foldl Compose.stepCompose Compose.initialState) with
              starter := some p } :=
      ComposeNonstarterSlide.stepCompose_primary_fire_form
        (X.foldl Compose.stepCompose Compose.initialState) head st p
        hStAct hHeadPos hHeadStrictMax hPC
    have hXheadFold :
        (X ++ #[head]).foldl Compose.stepCompose Compose.initialState
          = { (X.foldl Compose.stepCompose Compose.initialState) with
              starter := some p } := by
      rw [Array.foldl_append]
      show Compose.stepCompose
              (X.foldl Compose.stepCompose Compose.initialState) head
          = { (X.foldl Compose.stepCompose Compose.initialState) with
              starter := some p }
      exact hStepEq
    have hXheadStarter :
        ((X ++ #[head]).foldl Compose.stepCompose Compose.initialState).starter.isSome
          = true := by
      rw [hXheadFold]; rfl
    have hRestBufBound :
        ∀ y ∈ (rest.foldl Compose.stepCompose
                ((X ++ #[head]).foldl Compose.stepCompose Compose.initialState)).buffer,
          Lookup.canonicalCombiningClass y
            ≤ Lookup.canonicalCombiningClass cp := by
      intros y hy
      apply hBufBoundList
      rw [hXheadFold] at hy
      simp only [List.foldl_cons]
      rw [hStepEq]
      exact hy
    have hRecur := ih (X ++ #[head]) hRestPos hRestGt hXheadStarter hRestBufBound
    rw [hXheadFold] at hRecur
    exact hRecur

end Unicode.Normalization.ComposeBufferStructure
