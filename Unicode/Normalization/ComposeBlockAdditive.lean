/-
  Unicode.Normalization.ComposeBlockAdditive

  Compose-block additivity at a QC=Y starter boundary:

      compose (A ++ B) = compose A ++ compose B

  whenever `B` is non-empty and `B[0]` is a QC=Y starter
  (`canonicalCombiningClass B[0] = 0`, `nfcQCValue B[0] = .Y`).

  A QC=Y starter arriving at any pending compose state forces the
  prior starter+buffer to flush to `emitted`. The post-step state
  contains `flushCompose s_A` as its `emitted` field and
  `(some B[0], [], 0)` as its `(starter, buffer, maxCCC)` triple,
  matching the state produced by `stepCompose initialState B[0]`
  modulo the `emitted` prefix `flushCompose s_A`. Subsequent
  processing of `B[1..]` carries this prefix through unchanged
  because `stepCompose` only appends to `emitted`. The final
  `flushCompose` call distributes the prefix, producing
  `compose A ++ compose B`.
-/

import Unicode.Normalization.Compose
import Unicode.Normalization.ComposeInversion
import Unicode.Normalization.ComposeNonstarterSlide
import Unicode.Normalization.QuickCheckSoundnessFact4

namespace Unicode.Normalization.ComposeBlockAdditive

open Unicode.Normalization
open Unicode.Normalization.NFC (nfcQCValue)
open Unicode.Normalization.ComposeInversion (ComposeStateValid)
open Unicode.Normalization.ComposeNonstarterSlide (stepCompose_qcY_nonstarter_buffer_form)
open Unicode.Normalization.QuickCheckSoundnessFact4 (primaryComposite_none_of_qcY)

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1 STRONG VALIDITY
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `ComposeStateValid` strengthened with the leading-phase invariant:
    `starter = none → maxCCC = 0`. The leading-nonstarter branch of
    `stepCompose` (Case 2) modifies only `emitted`, so `maxCCC` stays
    at its initial value `0` until a starter is registered. -/
def ComposeStateStrongValid (s : Compose.ComposeState) : Prop :=
  ComposeStateValid s ∧ (s.starter = none → s.maxCCC = 0)

theorem initialState_strongValid : ComposeStateStrongValid Compose.initialState := by
  refine ⟨ComposeInversion.initialState_valid, ?starterImpliesMaxZero⟩
  intro hNone
  clear hNone
  rfl

/-- `stepCompose` preserves strong validity. The post-state has
    `starter = none` only when the pre-state has `starter = none` AND
    the input is a non-starter (Case 2). In that branch, `maxCCC` is
    unchanged from the pre-state's `0`. -/
theorem stepCompose_preserves_strongValid
    (s : Compose.ComposeState) (cp : Nat)
    (hValid : ComposeStateStrongValid s) :
    ComposeStateStrongValid (Compose.stepCompose s cp) := by
  obtain ⟨hValidBase, hStarterMax⟩ := hValid
  refine ⟨ComposeInversion.stepCompose_preserves_valid _ _ hValidBase,
          ?starterImpliesMaxZero⟩
  intro hPostNone
  unfold Compose.stepCompose at hPostNone ⊢
  cases hSt : s.starter with
  | none =>
    simp only [hSt] at hPostNone ⊢
    by_cases hCcc : Lookup.canonicalCombiningClass cp = 0
    · simp [hCcc] at hPostNone
    · simp [hCcc]
      exact hStarterMax hSt
  | some st =>
    simp only [hSt] at hPostNone ⊢
    by_cases hCcc : Lookup.canonicalCombiningClass cp = 0
    · simp only [hCcc, ↓reduceIte] at hPostNone
      by_cases hBuf : s.buffer.isEmpty = true
      · simp only [hBuf, ↓reduceIte] at hPostNone
        cases hPC : Compose.primaryComposite? st cp with
        | none => rw [hPC] at hPostNone; simp at hPostNone
        | some p => rw [hPC] at hPostNone; simp at hPostNone
      · simp only [hBuf] at hPostNone
        simp at hPostNone
    · simp only [hCcc, ↓reduceIte] at hPostNone
      by_cases hMax : Lookup.canonicalCombiningClass cp ≤ s.maxCCC
      · simp [hMax] at hPostNone
      · simp only [hMax, ↓reduceIte] at hPostNone
        cases hPC : Compose.primaryComposite? st cp with
        | none => rw [hPC] at hPostNone; simp at hPostNone
        | some p => rw [hPC] at hPostNone; simp at hPostNone

theorem foldl_stepCompose_strongValid
    (L : List Nat) (s : Compose.ComposeState)
    (hValid : ComposeStateStrongValid s) :
    ComposeStateStrongValid (L.foldl Compose.stepCompose s) := by
  induction L generalizing s with
  | nil => exact hValid
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (Compose.stepCompose s hd)
            (stepCompose_preserves_strongValid s hd hValid)

theorem foldl_stepCompose_strongValid_array (A : Array Nat) :
    ComposeStateStrongValid
      (A.foldl Compose.stepCompose Compose.initialState) := by
  rw [← Array.foldl_toList]
  exact foldl_stepCompose_strongValid A.toList Compose.initialState
          initialState_strongValid

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2 EMITTED-PREPEND EQUIVARIANCE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Prepending `Z` to a state's `emitted` commutes with `stepCompose`.
    `emitted` is a passive prefix accumulator: `stepCompose` only
    appends to it and never branches on its value. -/
theorem stepCompose_emitted_prepend
    (Z : Array Nat) (s : Compose.ComposeState) (cp : Nat) :
    Compose.stepCompose { s with emitted := Z ++ s.emitted } cp =
      { Compose.stepCompose s cp with
        emitted := Z ++ (Compose.stepCompose s cp).emitted } := by
  unfold Compose.stepCompose
  cases hSt : s.starter with
  | none =>
    by_cases hCcc : Lookup.canonicalCombiningClass cp = 0
    · simp [hCcc]
    · simp [hCcc]
  | some st =>
    by_cases hCcc : Lookup.canonicalCombiningClass cp = 0
    · simp only [hCcc, ↓reduceIte]
      by_cases hBuf : s.buffer.isEmpty = true
      · simp only [hBuf, ↓reduceIte]
        cases hPC : Compose.primaryComposite? st cp with
        | none => simp
        | some p => rfl
      · simp only [hBuf]
        simp [Array.append_assoc]
    · simp only [hCcc, ↓reduceIte]
      by_cases hMax : Lookup.canonicalCombiningClass cp ≤ s.maxCCC
      · simp [hMax]
      · simp only [hMax, ↓reduceIte]
        cases hPC : Compose.primaryComposite? st cp with
        | none => rfl
        | some p => rfl

/-- Foldl-level emitted-prepend equivariance. -/
theorem foldl_stepCompose_emitted_prepend
    (L : List Nat) (Z : Array Nat) (s : Compose.ComposeState) :
    L.foldl Compose.stepCompose { s with emitted := Z ++ s.emitted } =
      { L.foldl Compose.stepCompose s with
        emitted := Z ++ (L.foldl Compose.stepCompose s).emitted } := by
  induction L generalizing s with
  | nil =>
    simp
  | cons cp rest ih =>
    simp only [List.foldl_cons]
    rw [stepCompose_emitted_prepend Z s cp]
    rw [ih (Compose.stepCompose s cp)]

/-- `flushCompose` distributes a prepended `emitted` prefix. -/
theorem flushCompose_emitted_prepend
    (Z : Array Nat) (s : Compose.ComposeState) :
    Compose.flushCompose { s with emitted := Z ++ s.emitted } =
      Z ++ Compose.flushCompose s := by
  unfold Compose.flushCompose
  cases hSt : s.starter with
  | none => simp [Array.append_assoc]
  | some st => simp [Array.append_assoc]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3 QC=Y STARTER FLUSHES PRIOR STATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A QC=Y starter arriving at a strongly-valid state produces the
    state `⟨flushCompose s, some cp, [], 0⟩`. The three pre-state
    branches collapse uniformly:

      * `starter = none`: by strong validity, `buffer = []` and
        `maxCCC = 0`; the post-state is `⟨em, some cp, [], 0⟩`,
        matching `flushCompose ⟨em, none, [], 0⟩ = em`.
      * `starter = some st`, `buffer = []`: Fact 4 forces
        `primaryComposite? st cp = none`; the post-state is
        `⟨em ++ #[st], some cp, [], 0⟩`, matching `flushCompose
        ⟨em, some st, [], _⟩ = em ++ #[st]`.
      * `starter = some st`, `buffer ≠ []`: post-state is
        `⟨em ++ #[st] ++ buf.reverse.toArray, some cp, [], 0⟩`,
        matching `flushCompose ⟨em, some st, buf, _⟩`. -/
theorem stepCompose_qcY_starter_flush
    (s : Compose.ComposeState) (cp : Nat)
    (hValid : ComposeStateStrongValid s)
    (hCcc : Lookup.canonicalCombiningClass cp = 0)
    (hQC : nfcQCValue cp = .Y) :
    Compose.stepCompose s cp =
      { emitted := Compose.flushCompose s
        starter := some cp
        buffer  := []
        maxCCC  := 0 } := by
  obtain ⟨⟨hStarterBuffer, hBufferCCC⟩, hStarterMax⟩ := hValid
  clear hBufferCCC
  unfold Compose.stepCompose Compose.flushCompose
  -- `cases hSt : s.starter` introduces `hSt : s.starter = ctor` but does
  -- not substitute `s.starter` syntactically (it is a projection, not a
  -- free variable). `simp only [hSt]` performs the rewrite that
  -- enables iota-reduction of the surrounding `match`. The linter
  -- false-flags it as unused.
  set_option linter.unusedSimpArgs false in
  cases hSt : s.starter with
  | none =>
    simp only [hSt]
    have hBufNil : s.buffer = [] := hStarterBuffer hSt
    have hMxZero : s.maxCCC = 0 := hStarterMax hSt
    simp [hCcc, hBufNil, hMxZero]
  | some st =>
    simp only [hSt]
    rw [if_pos hCcc]
    by_cases hBuf : s.buffer.isEmpty = true
    · rw [if_pos hBuf]
      have hBufNil : s.buffer = [] := List.isEmpty_iff.mp hBuf
      rw [primaryComposite_none_of_qcY st cp hQC]
      simp [hBufNil]
    · rw [if_neg hBuf]

/-- `stepCompose initialState cp` on a starter `cp` yields the canonical
    leading state `⟨#[], some cp, [], 0⟩`. -/
theorem stepCompose_initial_starter
    (cp : Nat) (hCcc : Lookup.canonicalCombiningClass cp = 0) :
    Compose.stepCompose Compose.initialState cp =
      { emitted := #[], starter := some cp, buffer := [], maxCCC := 0 } := by
  unfold Compose.stepCompose Compose.initialState
  simp [hCcc]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4 BLOCK ADDITIVITY (CONS-LIST FORM)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Cons-list form of compose-block additivity. The post-`head` LHS
    state matches the post-`head` RHS state up to an `emitted` prefix
    of `flushCompose s_A`; the prefix carries through the remaining
    fold and the final `flushCompose` by §2. -/
theorem compose_qcY_starter_block_additive_list
    (A : Array Nat) (head : Nat) (rest : List Nat)
    (hHeadCcc : Lookup.canonicalCombiningClass head = 0)
    (hHeadQC : nfcQCValue head = .Y) :
    Compose.flushCompose
      ((head :: rest).foldl Compose.stepCompose
        (A.foldl Compose.stepCompose Compose.initialState))
    = Compose.flushCompose
        (A.foldl Compose.stepCompose Compose.initialState)
      ++ Compose.flushCompose
        ((head :: rest).foldl Compose.stepCompose Compose.initialState) := by
  have hsA_strongValid := foldl_stepCompose_strongValid_array A
  simp only [List.foldl_cons]
  rw [stepCompose_qcY_starter_flush
        (A.foldl Compose.stepCompose Compose.initialState)
        head hsA_strongValid hHeadCcc hHeadQC]
  rw [stepCompose_initial_starter head hHeadCcc]
  -- Reshape the LHS post-`head` state to expose
  -- `flushCompose s_A ++ #[]` as the `emitted` prefix.
  have hStateRewrite :
      ({ emitted := Compose.flushCompose
                      (A.foldl Compose.stepCompose Compose.initialState)
         starter := some head
         buffer  := []
         maxCCC  := 0 } : Compose.ComposeState)
      = { (⟨#[], some head, [], 0⟩ : Compose.ComposeState) with
          emitted := Compose.flushCompose
                      (A.foldl Compose.stepCompose Compose.initialState)
                    ++ #[] } := by
    simp
  rw [hStateRewrite]
  rw [foldl_stepCompose_emitted_prepend rest
        (Compose.flushCompose
          (A.foldl Compose.stepCompose Compose.initialState))
        ⟨#[], some head, [], 0⟩]
  rw [flushCompose_emitted_prepend
        (Compose.flushCompose
          (A.foldl Compose.stepCompose Compose.initialState))
        (rest.foldl Compose.stepCompose
          (⟨#[], some head, [], 0⟩ : Compose.ComposeState))]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §5 BLOCK ADDITIVITY (ARRAY FORM)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Compose-block additivity at a QC=Y starter boundary. -/
theorem compose_qcY_starter_block_additive
    (A : Array Nat) (B : Array Nat)
    (hNonEmpty : B.size > 0)
    (hHeadCcc : Lookup.canonicalCombiningClass (B[0]'hNonEmpty) = 0)
    (hHeadQC : nfcQCValue (B[0]'hNonEmpty) = .Y) :
    Compose.compose (A ++ B) = Compose.compose A ++ Compose.compose B := by
  obtain ⟨bs⟩ := B
  match bs, hNonEmpty with
  | [], hNE =>
    exact absurd hNE (by simp)
  | head :: rest, _hNE =>
    have hHeadCcc' : Lookup.canonicalCombiningClass head = 0 := hHeadCcc
    have hHeadQC' : nfcQCValue head = .Y := hHeadQC
    show Compose.flushCompose
            ((A ++ ⟨head :: rest⟩).foldl Compose.stepCompose Compose.initialState)
        = Compose.flushCompose
            (A.foldl Compose.stepCompose Compose.initialState)
          ++ Compose.flushCompose
            ((⟨head :: rest⟩ : Array Nat).foldl
                Compose.stepCompose Compose.initialState)
    rw [Array.foldl_append]
    have hEqLeft :
        (⟨head :: rest⟩ : Array Nat).foldl Compose.stepCompose
            (A.foldl Compose.stepCompose Compose.initialState)
        = (head :: rest).foldl Compose.stepCompose
            (A.foldl Compose.stepCompose Compose.initialState) := by
      rw [← Array.foldl_toList]
    have hEqRight :
        (⟨head :: rest⟩ : Array Nat).foldl Compose.stepCompose
            Compose.initialState
        = (head :: rest).foldl Compose.stepCompose Compose.initialState := by
      rw [← Array.foldl_toList]
    rw [hEqLeft, hEqRight]
    exact compose_qcY_starter_block_additive_list A head rest hHeadCcc' hHeadQC'

-- ═══════════════════════════════════════════════════════════════════════════════
-- §8 COMPOSE-SNOC LINEARITY FOR QC=Y EXTENSION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Step-level snoc linearity for QC=Y.** Adding a QC=Y codepoint
    `cp` at the end of any strongly-valid state's processing flushes
    the prior state's pending output and appends `cp`:

        flushCompose (stepCompose s cp) = flushCompose s ++ #[cp].

    Five cases by cp's shape and the prior state's `starter`:

      * Starter cp at strongly-valid state: by §3 (`stepCompose_qcY_
        starter_flush`), the post-step state is `⟨flushCompose s,
        some cp, [], 0⟩`; its `flushCompose` is `flushCompose s ++
        #[cp]`.
      * Non-starter cp from `starter = none`: by strong validity,
        `buffer = []` and `maxCCC = 0`; the leading-non-starter
        branch appends cp to `emitted`; flush gives `emitted ++
        #[cp]`.
      * Non-starter cp from `starter = some st`: post-step has
        `buffer := cp :: s.buffer`; flushing reverses the buffer,
        appending `cp` last. -/
theorem step_qcY_linear
    (s : Compose.ComposeState) (cp : Nat)
    (hValid : ComposeStateStrongValid s)
    (hQC : nfcQCValue cp = .Y) :
    Compose.flushCompose (Compose.stepCompose s cp) =
      Compose.flushCompose s ++ #[cp] := by
  by_cases hCcc : Lookup.canonicalCombiningClass cp = 0
  · -- Starter cp: post-step state is `⟨flushCompose s, some cp, [], 0⟩`.
    rw [stepCompose_qcY_starter_flush s cp hValid hCcc hQC]
    show Compose.flushCompose s ++ #[cp] = Compose.flushCompose s ++ #[cp]
    rfl
  · -- Non-starter cp. Case on starter.
    obtain ⟨⟨hStarterBuffer, hBufferCCC⟩, hStarterMax⟩ := hValid
    clear hBufferCCC
    cases hSt : s.starter with
    | none =>
      have hBuf : s.buffer = [] := hStarterBuffer hSt
      have hMx : s.maxCCC = 0 := hStarterMax hSt
      clear hMx
      have hPostStep :
          Compose.stepCompose s cp = { s with emitted := s.emitted ++ #[cp] } := by
        set_option linter.unusedSimpArgs false in
        unfold Compose.stepCompose
        simp only [hSt]
        rw [if_neg hCcc]
      unfold Compose.flushCompose
      rw [hPostStep]
      simp only [hSt, hBuf]
      -- LHS: emitted ++ #[cp] ++ [].reverse.toArray = emitted ++ #[cp].
      -- RHS: emitted ++ [].reverse.toArray ++ #[cp] = emitted ++ #[cp].
      simp
    | some st =>
      have hCccPos : 0 < Lookup.canonicalCombiningClass cp :=
        Nat.pos_of_ne_zero hCcc
      rw [stepCompose_qcY_nonstarter_buffer_form s cp st hSt hQC hCccPos]
      unfold Compose.flushCompose
      simp only [hSt]
      -- LHS: emitted ++ #[st] ++ (cp :: buffer).reverse.toArray.
      -- RHS: emitted ++ #[st] ++ buffer.reverse.toArray ++ #[cp].
      show s.emitted ++ #[st] ++ (cp :: s.buffer).reverse.toArray
          = s.emitted ++ #[st] ++ s.buffer.reverse.toArray ++ #[cp]
      rw [List.reverse_cons]
      rw [show ((s.buffer.reverse ++ [cp]) : List Nat).toArray
            = s.buffer.reverse.toArray ++ #[cp] from by
          apply Array.toList_inj.mp
          rw [Array.toList_append, List.toList_toArray, List.toList_toArray]]
      simp

/-- **Compose-snoc linearity for QC=Y extension.** For any QC=Y cp
    and any array X, `compose (X ++ #[cp]) = compose X ++ #[cp]`.
    Lifts `step_qcY_linear` through the foldl over the snoc-extended
    array; strong validity of the post-X state comes from
    `foldl_stepCompose_strongValid_array`. -/
theorem compose_qcY_linear
    (X : Array Nat) (cp : Nat) (hQC : nfcQCValue cp = .Y) :
    Compose.compose (X ++ #[cp]) = Compose.compose X ++ #[cp] := by
  unfold Compose.compose
  rw [Array.foldl_append]
  have hStep :
      (#[cp] : Array Nat).foldl Compose.stepCompose
          (X.foldl Compose.stepCompose Compose.initialState)
        = Compose.stepCompose
            (X.foldl Compose.stepCompose Compose.initialState) cp := by
    show ([cp] : List Nat).foldl Compose.stepCompose
            (X.foldl Compose.stepCompose Compose.initialState)
        = Compose.stepCompose
            (X.foldl Compose.stepCompose Compose.initialState) cp
    simp only [List.foldl_cons, List.foldl_nil]
  rw [hStep]
  exact step_qcY_linear
          (X.foldl Compose.stepCompose Compose.initialState) cp
          (foldl_stepCompose_strongValid_array X) hQC

end Unicode.Normalization.ComposeBlockAdditive
