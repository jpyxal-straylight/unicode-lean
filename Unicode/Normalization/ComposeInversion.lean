/-
  Unicode.Normalization.ComposeInversion

  NFC idempotence pillar 2: `decompose_compose_inversion` — the claim
  that `toNFD (Compose x) = x` for NFD-form input. Combined with
  `reorder_idempotent` (pillar 1), this gives

      toNFC (toNFC cps) = Compose (toNFD (Compose (toNFD cps)))
                        = Compose (toNFD cps)          [inversion on NFD]
                        = toNFC cps

  Strategy: Compose's state machine maintains an invariant — the
  `decomposeSequence` of the state's output representation equals the
  pre of input processed so far. At termination, decomposing the
  full output recovers the full input; reorder on NFD-form input is
  identity; combined, `toNFD (Compose x) = x`.

  Uses `primaryComposite_canonicalDecomposition_nonHangul` (from
  `Invertibility`) as the structural fact that each composed codepoint
  decomposes back to the pair Compose consumed.
-/

import Unicode.Normalization.Compose
import Unicode.Normalization.Invertibility
import Unicode.Normalization.NFD
import Unicode.Normalization.ToNFDAppend
import Unicode.Invariants

namespace Unicode.Normalization.ComposeInversion

open Unicode.Normalization
open Unicode.Invariants
open Unicode.Generated

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATE-EXPANSION HELPER
--
-- The "expansion" of a ComposeState: a flat codepoint array
-- representing what the state would emit if flushed (modulo the
-- final `sortNonStarterRun` on the buffer). The inversion proof
-- tracks the RAW expansion (before buffer sorting), so that
-- decomposeSequence on the final output recovers the original
-- input multiset in order.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Raw flattening of a Compose state: emitted ++ optional starter ++
    buffer-in-scan-order (i.e., reversed because buffer accumulates in
    reverse). Used in the state invariant. -/
def expand (s : Compose.ComposeState) : Array Nat :=
  match s.starter with
  | some st => s.emitted ++ #[st] ++ s.buffer.reverse.toArray
  | none    => s.emitted ++ s.buffer.reverse.toArray

-- ═══════════════════════════════════════════════════════════════════════════════
-- ABBREVIATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Shorthand alias for the full-canonical-decompose flatten of a sequence. -/
abbrev dSeq (xs : Array Nat) : Array Nat :=
  Decompose.decomposeSequence xs

-- ═══════════════════════════════════════════════════════════════════════════════
-- NFD-EQUIVALENCE
--
-- Two arrays are NFD-equivalent if they decompose to the same NFD form.
-- This is the natural equivalence relation for reasoning about Compose:
-- `Compose x` is NFD-equivalent to `x`, and for NFD-form `x`, the
-- equivalence degenerates to equality.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Two codepoint arrays are NFD-equivalent iff they canonicalize to the
    same NFD form. -/
def NFDEquivalent (a b : Array Nat) : Prop := NFC.toNFD a = NFC.toNFD b

/-- NFD-equivalence is reflexive. -/
theorem NFDEquivalent_rfl (a : Array Nat) : NFDEquivalent a a := Eq.refl (NFC.toNFD a)

/-- NFD-equivalence is symmetric. -/
theorem NFDEquivalent_symm {a b : Array Nat}
    (h : NFDEquivalent a b) : NFDEquivalent b a := Eq.symm h

/-- NFD-equivalence is transitive. -/
theorem NFDEquivalent_trans {a b c : Array Nat}
    (hab : NFDEquivalent a b) (hbc : NFDEquivalent b c) :
    NFDEquivalent a c := Eq.trans hab hbc

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPOSE AND EXPAND
--
-- Key observation: `Compose x = flushCompose (fold stepCompose initialState x)`,
-- and `flushCompose s = expand s` when `s.buffer.reverse` is already
-- CCC-sorted (which holds for NFD-form input threading through stepCompose).
--
-- For NFD-form input, the buffer accumulates non-starters in scan order,
-- which is already CCC-sorted because reorder has already run.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- For any ComposeState `s`, `flushCompose s = expand s`. Definitional —
    both functions produce `emitted ++ starterPart ++ buffer.reverse.toArray`. -/
theorem flushCompose_eq_expand (s : Compose.ComposeState) :
    Compose.flushCompose s = expand s := by
  unfold Compose.flushCompose expand
  rfl

/-- `compose x = expand (fold stepCompose initialState x)`. Immediate from
    the definition of `compose` composed with `flushCompose_eq_expand`. -/
theorem compose_eq_expand (x : Array Nat) :
    Compose.compose x = expand (x.foldl Compose.stepCompose Compose.initialState) := by
  unfold Compose.compose
  rw [flushCompose_eq_expand]

-- ═══════════════════════════════════════════════════════════════════════════════
-- REACHABLE-STATE INVARIANT
--
-- Not every `ComposeState` can arise from folding `stepCompose` over a
-- codepoint sequence starting from `initialState`. The structural
-- property that reachable states all satisfy — and that is load-bearing
-- for the step-preservation argument — is:
--
--     s.starter = none → s.buffer = []
--
-- Intuition: a non-starter only enters the buffer after an active starter
-- has been seen. Without an active starter, a leading non-starter is
-- appended directly to `emitted`. Consequently the buffer stays empty
-- until a starter materialises.
--
-- The invariant rules out states like
--   `{ starter := none, buffer := [non-starter], … }`
-- whose `expand` places the non-starter BEFORE any subsequent starter,
-- producing a concatenation that does not match `pre ++ #[starter]` at
-- the NFD level. Such states have no preimage under `stepCompose ∘ … ∘
-- stepCompose`, so excluding them costs nothing.
--
-- The hypothesis `StepPreservesNFDEquivalence` is stated over valid
-- states only. `initialState` is valid and `stepCompose` preserves
-- validity, so `foldl_stepCompose_NFDEquivalence_given` threads the
-- invariant through the induction unchanged.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Reachable-state invariant for the compose fold. Conjoins two facts:

    * `starter = none → buffer = []`: no pending non-starters without an
      active starter. Excludes states where `expand` would trail the
      buffer behind no starter, which is unreachable from `initialState`
      under `stepCompose`.

    * `∀ y ∈ buffer, 0 < ccc y ∧ ccc y ≤ maxCCC`: every buffered
      non-starter has positive CCC (it IS a non-starter) AND is
      ≤-bounded by the running `maxCCC`. Captures the structural
      truth that `stepCompose` only prepends to `buffer` on branches
      where the incoming `cp` has `ccc cp ≠ 0` and updates `maxCCC`
      to `max s.maxCCC ccc`, so every buffer element respects the
      running bound. Needed to discharge Case 7's `hBuf` hypothesis
      at the dispatcher call site. -/
def ComposeStateValid (s : Compose.ComposeState) : Prop :=
  (s.starter = none → s.buffer = [])
  ∧ (∀ y ∈ s.buffer,
       0 < Lookup.canonicalCombiningClass y
       ∧ Lookup.canonicalCombiningClass y ≤ s.maxCCC)

/-- The initial state is valid: both `starter` and `buffer` are their
    respective empty witnesses. Both conjuncts hold vacuously. -/
theorem initialState_valid : ComposeStateValid Compose.initialState := by
  constructor
  · intro hStarterNone
    clear hStarterNone
    rfl
  · intro y hMem
    simp [Compose.initialState] at hMem

/-- When `s.starter = none`, `stepCompose` only flips `starter` or
    appends `cp` to `emitted`; it never modifies `buffer`. The two
    branches are selected by `ccc(cp) = 0`. -/
theorem stepCompose_starter_none_output
    (s : Compose.ComposeState) (cp : Nat) (hS : s.starter = none) :
    Compose.stepCompose s cp
      = if Lookup.canonicalCombiningClass cp = 0 then
          { s with starter := some cp }
        else
          { s with emitted := s.emitted ++ #[cp] } := by
  obtain ⟨em, opSt, buf, mx⟩ := s
  simp only at hS
  subst hS
  unfold Compose.stepCompose
  simp only []

/-- When `s.starter = some st`, every `stepCompose` branch produces a
    state whose `starter` is `some _`. This drives the "contradict
    `hNone`" side of the validity-preservation proof. -/
theorem stepCompose_starter_some_isSome
    (s : Compose.ComposeState) (cp : Nat) (st : Nat) (hS : s.starter = some st) :
    (Compose.stepCompose s cp).starter.isSome = true := by
  obtain ⟨em, opSt, buf, mx⟩ := s
  simp only at hS
  subst hS
  unfold Compose.stepCompose
  simp only []
  by_cases hCCC : Lookup.canonicalCombiningClass cp = 0
  · rw [if_pos hCCC]
    by_cases hBE : buf.isEmpty = true
    · rw [if_pos hBE]
      cases Compose.primaryComposite? st cp <;> rfl
    · rw [if_neg hBE]
      rfl
  · rw [if_neg hCCC]
    by_cases hBlock : Lookup.canonicalCombiningClass cp ≤ mx
    · rw [if_pos hBlock]
      rfl
    · rw [if_neg hBlock]
      cases Compose.primaryComposite? st cp <;> rfl

set_option maxRecDepth 8192 in
/-- `stepCompose` preserves the reachable-state invariant. Both
    conjuncts are discharged branch-by-branch:

    * First conjunct (starter/buffer implication): `stepCompose`'s
      non-starter branches either keep `starter = some _` (so the
      implication is vacuous) or only run when the input started with
      `none` + valid, in which case `s.buffer = []` carries through.

    * Second conjunct (buffer CCC bound): each branch is one of:
      - buffer unchanged + maxCCC unchanged (Cases 1, 2, 3, 7): old
        invariant carries directly.
      - buffer cleared to `[]` (Cases 4, 5): vacuous membership.
      - `cp :: buffer` prepended, `maxCCC := max maxCCC (ccc cp)`
        (Cases 6, 8): `cp` has `ccc cp > 0` by the branch guard and
        `ccc cp ≤ max _ (ccc cp)` by `Nat.le_max_right`; old buffer
        elements have `ccc y ≤ s.maxCCC ≤ max s.maxCCC (ccc cp)` by
        `Nat.le_max_left`.

    Uses a per-theorem `maxRecDepth` bump (per the canon's
    `Continuity.Codec.Varint` precedent) because the case-split
    through `stepCompose`'s 8 branches elaborates deep terms involving
    unfolded `match` + `if` structures. -/
theorem stepCompose_preserves_valid
    (s : Compose.ComposeState) (cp : Nat) (hv : ComposeStateValid s) :
    ComposeStateValid (Compose.stepCompose s cp) := by
  obtain ⟨hvStarter, hvBuffer⟩ := hv
  constructor
  · -- First conjunct: starter = none → buffer = []
    intro hNone
    cases hS : s.starter with
    | some st =>
      exfalso
      have hSome := stepCompose_starter_some_isSome s cp st hS
      rw [hNone] at hSome
      simp at hSome
    | none =>
      have hBuf : s.buffer = [] := hvStarter hS
      rw [stepCompose_starter_none_output s cp hS]
      by_cases hCCC : Lookup.canonicalCombiningClass cp = 0
      · simp [hCCC, hBuf]
      · simp [hCCC, hBuf]
  · -- Second conjunct: ∀ y ∈ (stepCompose s cp).buffer, 0 < ccc y ∧ ccc y ≤ ...
    unfold Compose.stepCompose
    cases hS : s.starter with
    | none =>
      have hBuf : s.buffer = [] := hvStarter hS
      by_cases hCCC : Lookup.canonicalCombiningClass cp = 0
      · simp only [hCCC, if_true]
        intro y hMem
        rw [hBuf] at hMem
        cases hMem
      · simp only [hCCC, if_false]
        intro y hMem
        rw [hBuf] at hMem
        cases hMem
    | some st =>
      by_cases hCCC : Lookup.canonicalCombiningClass cp = 0
      · simp only [hCCC, if_true]
        by_cases hBufEm : s.buffer.isEmpty = true
        · simp only [hBufEm, if_true]
          have hBufNil : s.buffer = [] := List.isEmpty_iff.mp hBufEm
          cases hPrim : Compose.primaryComposite? st cp with
          | some p =>
            intro y hMem
            rw [hBufNil] at hMem
            cases hMem
          | none =>
            intro y hMem
            cases hMem
        · simp only [hBufEm]
          intro y hMem
          cases hMem
      · simp only [hCCC, if_false]
        by_cases hBlock : Lookup.canonicalCombiningClass cp ≤ s.maxCCC
        · -- Case 6: buffer := cp :: s.buffer, maxCCC := Nat.max s.maxCCC (ccc cp)
          simp only [hBlock, if_true]
          intro y hMem
          rcases List.mem_cons.mp hMem with hHead | hTail
          · rw [hHead]
            exact ⟨Nat.pos_of_ne_zero hCCC,
                   Nat.le_max_right s.maxCCC (Lookup.canonicalCombiningClass cp)⟩
          · obtain ⟨hYpos, hYbound⟩ := hvBuffer y hTail
            exact ⟨hYpos, Nat.le_trans hYbound
                           (Nat.le_max_left s.maxCCC (Lookup.canonicalCombiningClass cp))⟩
        · simp only [hBlock, if_false]
          cases hPrim : Compose.primaryComposite? st cp with
          | some p =>
            -- Case 7: buffer unchanged, maxCCC unchanged
            intro y hMem
            exact hvBuffer y hMem
          | none =>
            -- Case 8: buffer := cp :: s.buffer, maxCCC := Nat.max s.maxCCC (ccc cp)
            intro y hMem
            rcases List.mem_cons.mp hMem with hHead | hTail
            · rw [hHead]
              exact ⟨Nat.pos_of_ne_zero hCCC,
                     Nat.le_max_right s.maxCCC (Lookup.canonicalCombiningClass cp)⟩
            · obtain ⟨hYpos, hYbound⟩ := hvBuffer y hTail
              exact ⟨hYpos, Nat.le_trans hYbound
                             (Nat.le_max_left s.maxCCC (Lookup.canonicalCombiningClass cp))⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONDITIONAL INVERSION (the proof architecture)
--
-- Decompose-compose inversion decomposes into two hypotheses:
--
--   1. `StepPreserves`: stepCompose preserves NFD-equivalence against
--      the input pre-plus-one codepoint, on VALID states. This is the key
--      multiset/reorder-commutativity lemma; captures the fact that
--      absorb-and-decompose round-trips the pair at NFD equivalence.
--
--   2. `FoldOverList`: a tactical detail — that folding append-singleton
--      over a list starting from `#[]` reconstructs the array. Structurally
--      straightforward but requires a generalized induction.
--
-- Given both hypotheses, `decompose_compose_inversion` and `toNFC_idempotent`
-- follow as corollaries. This pattern matches
-- `Precis.Preparation.precis_idempotent_given_roundtrip` — reducing NFC
-- idempotence to a single named hypothesis that can be proved separately.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Hypothesis 1.** `stepCompose` preserves NFD-equivalence on valid
    states: if `expand s` is NFD-equivalent to the input pre processed
    so far AND `s` is a reachable state (`ComposeStateValid s`), then
    `expand (stepCompose s cp)` is NFD-equivalent to that pre extended
    by `cp`.

    The validity precondition is load-bearing: without it the
    hypothesis is false (consider
    `s := { starter := none, buffer := [non-starter], … }` which
    satisfies `NFDEquivalent (expand s) #[non-starter]` but whose
    single-step expansion under a starter input places the new starter
    before the non-starter — giving a different NFD form than
    `#[non-starter, starter]`). Because `initialState` is valid and
    `stepCompose_preserves_valid` threads validity through the fold,
    restricting the hypothesis to valid states costs nothing at the
    call site.

    Closure strategy (not yet executed):
      * Case on `stepCompose` branches.
      * Pass-through branches reduce to `toNFD (A ++ #[cp]) = toNFD (A ++ #[cp])`.
      * Primary-composite absorption branches use
        `Invertibility.primaryComposite_canonicalDecomposition_nonHangul`
        to show the composite decomposes back to the absorbed pair; the
        out-of-scan-order placement of the absorbed `cp` is resolved by
        `reorder` inside `toNFD`.
      * Hangul branches use `Hangul.composePair?`/`decomposeSyllable?`
        algorithmic duality. -/
def StepPreservesNFDEquivalence : Prop :=
  ∀ (s : Compose.ComposeState) (cp : Nat) (pre : Array Nat),
    ComposeStateValid s →
    NFDEquivalent (expand s) pre →
    NFDEquivalent (expand (Compose.stepCompose s cp)) (pre ++ #[cp])

-- ═══════════════════════════════════════════════════════════════════════════════
-- BATCH A: EXPAND-APPEND CASES (1, 2, 6, 8)
--
-- These four `stepCompose` branches all have the structural property
-- `expand (stepCompose s cp) = expand s ++ #[cp]` and therefore preserve
-- NFD-equivalence via the `ToNFDAppend.toNFD_congr_append` lemma.
--
--   Case 1 — `starter = none`, `ccc = 0` (leading starter, no active
--            starter yet). Requires `ComposeStateValid` to force
--            `s.buffer = []`; the output state has `starter := some cp`
--            and still-empty buffer, so expand emits `s.emitted ++ #[cp]`.
--
--   Case 2 — `starter = none`, `ccc ≠ 0` (leading non-starter, no
--            active starter yet). Requires `ComposeStateValid` to
--            force `s.buffer = []`; otherwise `expand s` would have
--            the buffer trailing the output, and appending `cp` to
--            `emitted` would leave the buffer between `cp` and the
--            trailing end.
--
--   Case 6 — `starter = some st`, `ccc ≠ 0`, `ccc ≤ maxCCC` (blocked
--            non-starter joins the pending buffer). Buffer accumulates
--            in reverse scan order, so prepending `cp` corresponds to
--            appending it at the end of the flushed output.
--
--   Case 8 — `starter = some st`, `ccc ≠ 0`, `ccc > maxCCC`,
--            `primaryComposite? st cp = none` (strict-max non-starter,
--            no composition partner). Same buffer-prepend pattern as
--            Case 6.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `reverse` distribution over cons, lifted into `Array` form. Used to
    rewrite `(cp :: buf).reverse.toArray` as `buf.reverse.toArray ++
    #[cp]`. -/
theorem reverse_cons_toArray (cp : Nat) (buf : List Nat) :
    (cp :: buf).reverse.toArray = buf.reverse.toArray ++ #[cp] := by
  rw [List.reverse_cons]
  apply Array.toList_inj.mp
  simp

/-- **Case 1** expand equality: leading starter with no active starter
    (ccc = 0) and (by validity) empty buffer gives `expand (step s cp) =
    expand s ++ #[cp]`. The output state carries `starter := some cp`
    and still-empty buffer, so expand produces `s.emitted ++ #[cp]` —
    which equals `expand s ++ #[cp]` by the same validity-forced empty
    buffer on the input side. -/
theorem stepCompose_case_leading_starter_expand
    (s : Compose.ComposeState) (cp : Nat)
    (hSNone : s.starter = none)
    (hCCC : Lookup.canonicalCombiningClass cp = 0)
    (hv : ComposeStateValid s) :
    expand (Compose.stepCompose s cp) = expand s ++ #[cp] := by
  have hBuf : s.buffer = [] := hv.1 hSNone
  rw [stepCompose_starter_none_output s cp hSNone]
  rw [if_pos hCCC]
  unfold expand
  rw [hSNone, hBuf]
  simp

/-- **Case 2** expand equality: leading non-starter with no active
    starter and (by validity) empty buffer gives `expand (step s cp) =
    expand s ++ #[cp]`. -/
theorem stepCompose_case_leading_nonstarter_expand
    (s : Compose.ComposeState) (cp : Nat)
    (hSNone : s.starter = none)
    (hCCC : Lookup.canonicalCombiningClass cp ≠ 0)
    (hv : ComposeStateValid s) :
    expand (Compose.stepCompose s cp) = expand s ++ #[cp] := by
  have hBuf : s.buffer = [] := hv.1 hSNone
  rw [stepCompose_starter_none_output s cp hSNone]
  rw [if_neg hCCC]
  unfold expand
  rw [hSNone, hBuf]
  simp

/-- **Case 6** expand equality: blocked non-starter joins the buffer
    (reverse-prepend). `expand (step s cp) = expand s ++ #[cp]`. -/
theorem stepCompose_case_buffer_append_expand
    (s : Compose.ComposeState) (cp : Nat) (st : Nat)
    (hSome : s.starter = some st)
    (hCCC : Lookup.canonicalCombiningClass cp ≠ 0)
    (hBlock : Lookup.canonicalCombiningClass cp ≤ s.maxCCC) :
    expand (Compose.stepCompose s cp) = expand s ++ #[cp] := by
  have hStep : Compose.stepCompose s cp
             = { s with buffer := cp :: s.buffer
                      , maxCCC := Nat.max s.maxCCC
                                    (Lookup.canonicalCombiningClass cp) } := by
    unfold Compose.stepCompose
    rw [hSome]
    simp [hCCC, hBlock]
  rw [hStep]
  unfold expand
  rw [hSome]
  show s.emitted ++ #[st] ++ (cp :: s.buffer).reverse.toArray
     = s.emitted ++ #[st] ++ s.buffer.reverse.toArray ++ #[cp]
  rw [reverse_cons_toArray]
  rw [← Array.append_assoc]

/-- **Case 8** expand equality: strict-max non-starter without a
    composition partner joins the buffer. Same pattern as Case 6. -/
theorem stepCompose_case_strict_max_no_composite_expand
    (s : Compose.ComposeState) (cp : Nat) (st : Nat)
    (hSome : s.starter = some st)
    (hCCC : Lookup.canonicalCombiningClass cp ≠ 0)
    (hStrictMax : ¬(Lookup.canonicalCombiningClass cp ≤ s.maxCCC))
    (hPrim : Compose.primaryComposite? st cp = none) :
    expand (Compose.stepCompose s cp) = expand s ++ #[cp] := by
  have hStep : Compose.stepCompose s cp
             = { s with buffer := cp :: s.buffer
                      , maxCCC := Nat.max s.maxCCC
                                    (Lookup.canonicalCombiningClass cp) } := by
    unfold Compose.stepCompose
    rw [hSome]
    simp [hCCC, hStrictMax, hPrim]
  rw [hStep]
  unfold expand
  rw [hSome]
  show s.emitted ++ #[st] ++ (cp :: s.buffer).reverse.toArray
     = s.emitted ++ #[st] ++ s.buffer.reverse.toArray ++ #[cp]
  rw [reverse_cons_toArray]
  rw [← Array.append_assoc]

/-- **NFD-equivalence preservation via expand-equality.** Generic helper
    for any `stepCompose` branch where the output `expand` equals the
    input `expand` appended with the new codepoint. -/
theorem nfdEquivalent_of_expand_append
    (s : Compose.ComposeState) (cp : Nat) (pre : Array Nat)
    (hExpand : expand (Compose.stepCompose s cp) = expand s ++ #[cp])
    (hEquiv : NFDEquivalent (expand s) pre) :
    NFDEquivalent (expand (Compose.stepCompose s cp)) (pre ++ #[cp]) := by
  unfold NFDEquivalent
  rw [hExpand]
  exact ToNFDAppend.toNFD_congr_append #[cp] hEquiv

/-- **Case 1** closure: leading starter preserves NFD-equivalence. -/
theorem stepPreserves_case_leading_starter
    (s : Compose.ComposeState) (cp : Nat) (pre : Array Nat)
    (hv : ComposeStateValid s)
    (hSNone : s.starter = none)
    (hCCC : Lookup.canonicalCombiningClass cp = 0)
    (hEquiv : NFDEquivalent (expand s) pre) :
    NFDEquivalent (expand (Compose.stepCompose s cp)) (pre ++ #[cp]) :=
  nfdEquivalent_of_expand_append s cp pre
    (stepCompose_case_leading_starter_expand s cp hSNone hCCC hv) hEquiv

/-- **Case 2** closure: leading non-starter preserves NFD-equivalence. -/
theorem stepPreserves_case_leading_nonstarter
    (s : Compose.ComposeState) (cp : Nat) (pre : Array Nat)
    (hv : ComposeStateValid s)
    (hSNone : s.starter = none)
    (hCCC : Lookup.canonicalCombiningClass cp ≠ 0)
    (hEquiv : NFDEquivalent (expand s) pre) :
    NFDEquivalent (expand (Compose.stepCompose s cp)) (pre ++ #[cp]) :=
  nfdEquivalent_of_expand_append s cp pre
    (stepCompose_case_leading_nonstarter_expand s cp hSNone hCCC hv) hEquiv

/-- **Case 6** closure: blocked non-starter preserves NFD-equivalence. -/
theorem stepPreserves_case_buffer_append
    (s : Compose.ComposeState) (cp : Nat) (pre : Array Nat)
    (st : Nat)
    (hSome : s.starter = some st)
    (hCCC : Lookup.canonicalCombiningClass cp ≠ 0)
    (hBlock : Lookup.canonicalCombiningClass cp ≤ s.maxCCC)
    (hEquiv : NFDEquivalent (expand s) pre) :
    NFDEquivalent (expand (Compose.stepCompose s cp)) (pre ++ #[cp]) :=
  nfdEquivalent_of_expand_append s cp pre
    (stepCompose_case_buffer_append_expand s cp st hSome hCCC hBlock) hEquiv

/-- **Case 8** closure: strict-max non-starter without composition
    partner preserves NFD-equivalence. -/
theorem stepPreserves_case_strict_max_no_composite
    (s : Compose.ComposeState) (cp : Nat) (pre : Array Nat)
    (st : Nat)
    (hSome : s.starter = some st)
    (hCCC : Lookup.canonicalCombiningClass cp ≠ 0)
    (hStrictMax : ¬(Lookup.canonicalCombiningClass cp ≤ s.maxCCC))
    (hPrim : Compose.primaryComposite? st cp = none)
    (hEquiv : NFDEquivalent (expand s) pre) :
    NFDEquivalent (expand (Compose.stepCompose s cp)) (pre ++ #[cp]) :=
  nfdEquivalent_of_expand_append s cp pre
    (stepCompose_case_strict_max_no_composite_expand s cp st hSome hCCC
      hStrictMax hPrim) hEquiv

-- ═══════════════════════════════════════════════════════════════════════════════
-- BATCH B: STARTER-VARIANT NO-COMPOSITION CASES (4, 5)
--
-- Both branches are starter inputs (ccc = 0) that advance the active
-- starter without composing. They flush the current starter (+ any
-- buffered non-starters) into `emitted`, set `starter := some cp`, and
-- reset the buffer. The output `expand` still has the form
-- `expand s ++ #[cp]`, so NFD-equivalence preservation follows via the
-- same `nfdEquivalent_of_expand_append` helper used in Batch A —
-- `toNFD_congr_append` is agnostic about whether the appended element
-- is a starter.
--
--   Case 4 — `starter = some st`, `ccc = 0`, `buffer = []`,
--            `primaryComposite? st cp = none` (cp is a starter that
--            cannot primary-compose with st). Flushes st into
--            emitted, makes cp the new active starter.
--
--   Case 5 — `starter = some st`, `ccc = 0`, `buffer ≠ []` (cp is a
--            starter but there are buffered non-starters between it
--            and st — so composition is blocked). Flushes st + buffer
--            into emitted, makes cp the new active starter.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Case 4** expand equality: starter-to-starter with no composition.
    Buffer is empty by the branch guard, so the output `expand` has
    `emitted ++ #[st] ++ #[cp] ++ #[]` which reduces to `expand s ++
    #[cp]`. -/
theorem stepCompose_case_starter_no_composite_expand
    (s : Compose.ComposeState) (cp : Nat) (st : Nat)
    (hSome : s.starter = some st)
    (hCCC : Lookup.canonicalCombiningClass cp = 0)
    (hBufEmpty : s.buffer.isEmpty = true)
    (hPrim : Compose.primaryComposite? st cp = none) :
    expand (Compose.stepCompose s cp) = expand s ++ #[cp] := by
  have hBuf : s.buffer = [] := List.isEmpty_iff.mp hBufEmpty
  have hStep : Compose.stepCompose s cp
             = { emitted := s.emitted ++ #[st]
               , starter := some cp
               , buffer := []
               , maxCCC := 0 } := by
    unfold Compose.stepCompose
    rw [hSome]
    simp [hCCC, hBufEmpty, hPrim]
  rw [hStep]
  unfold expand
  rw [hSome, hBuf]
  simp

/-- **Case 5** expand equality: starter input with non-empty buffer.
    Flushing st and buffer into emitted, then making cp the new active
    starter, gives the output `expand` as `s.emitted ++ #[st] ++
    s.buffer.reverse.toArray ++ #[cp] ++ #[]`. Reduces to `expand s ++
    #[cp]`. -/
theorem stepCompose_case_starter_flush_expand
    (s : Compose.ComposeState) (cp : Nat) (st : Nat)
    (hSome : s.starter = some st)
    (hCCC : Lookup.canonicalCombiningClass cp = 0)
    (hBufNonEmpty : s.buffer.isEmpty = false) :
    expand (Compose.stepCompose s cp) = expand s ++ #[cp] := by
  have hStep : Compose.stepCompose s cp
             = { emitted := s.emitted ++ #[st] ++ s.buffer.reverse.toArray
               , starter := some cp
               , buffer := []
               , maxCCC := 0 } := by
    unfold Compose.stepCompose
    rw [hSome]
    simp [hCCC, hBufNonEmpty]
  rw [hStep]
  unfold expand
  rw [hSome]
  simp

/-- **Case 4** closure: starter-to-starter without composition
    preserves NFD-equivalence. -/
theorem stepPreserves_case_starter_no_composite
    (s : Compose.ComposeState) (cp : Nat) (pre : Array Nat)
    (st : Nat)
    (hSome : s.starter = some st)
    (hCCC : Lookup.canonicalCombiningClass cp = 0)
    (hBufEmpty : s.buffer.isEmpty = true)
    (hPrim : Compose.primaryComposite? st cp = none)
    (hEquiv : NFDEquivalent (expand s) pre) :
    NFDEquivalent (expand (Compose.stepCompose s cp)) (pre ++ #[cp]) :=
  nfdEquivalent_of_expand_append s cp pre
    (stepCompose_case_starter_no_composite_expand s cp st hSome hCCC
      hBufEmpty hPrim) hEquiv

/-- **Case 5** closure: starter input with non-empty buffer preserves
    NFD-equivalence. -/
theorem stepPreserves_case_starter_flush
    (s : Compose.ComposeState) (cp : Nat) (pre : Array Nat)
    (st : Nat)
    (hSome : s.starter = some st)
    (hCCC : Lookup.canonicalCombiningClass cp = 0)
    (hBufNonEmpty : s.buffer.isEmpty = false)
    (hEquiv : NFDEquivalent (expand s) pre) :
    NFDEquivalent (expand (Compose.stepCompose s cp)) (pre ++ #[cp]) :=
  nfdEquivalent_of_expand_append s cp pre
    (stepCompose_case_starter_flush_expand s cp st hSome hCCC hBufNonEmpty)
    hEquiv

-- ═══════════════════════════════════════════════════════════════════════════════
-- BATCH C: PRIMARY-COMPOSITE ABSORB (Cases 3, 7)
--
-- These branches consume a pair (st, cp) into a primary composite p
-- (`primaryComposite? st cp = some p`). The structural content is the
-- decomposition-factorization fact `fullCanonicalDecompose p =
-- fullCanonicalDecompose st ++ fullCanonicalDecompose cp`.
--
-- **Non-Hangul half: CLOSED UNCONDITIONALLY.** `primaryComposite?`'s
-- non-Hangul path resolves through `UnicodeData.rows.findSome?`. The
-- `ucd_twoEltDecomp_factoring` `native_decide` table directly verifies
-- the factorization for every UCD row with a 2-element canonical
-- decomposition. Combined with
-- `Invertibility.primaryComposite_canonicalDecomposition_nonHangul`,
-- this gives the non-Hangul primary-composite factorization
-- unconditionally.
--
-- **Hangul half: OPEN.** Remains as `FullCanonicalDecomposeFactoringHangul`.
-- Closure path: algebraic inversion of `Hangul.composePair?` and
-- `Hangul.decomposeSyllable?` with an edge-case carve-out for the
-- off-by-one in `Hangul.isTJamo` (accepts `TBase + TCount = 0x11C3`
-- which is not a valid T jamo in UCD 17.0).
--
-- **Case 7 additionally requires `ReorderCommutesStrictMax`** — parallel
-- infrastructure work to `reorder_absorbing_left`.
-- ═══════════════════════════════════════════════════════════════════════════════

-- ── UCD factoring table ───────────────────────────────────────────────────────

/-- **UCD factorization table.** For every UCD row with a 2-element
    canonical decomposition, the full canonical decomposition of the
    row's codepoint equals the concatenation of the decompositions of
    the two elements. Closed by `native_decide` over the pinned 3045-row
    table. Uses `Array.getD` to avoid pattern-matching on array literals
    (which Lean 4 cannot synthesize equation theorems for). -/
theorem ucd_twoEltDecomp_factoring :
    UnicodeData.rows.all (fun row =>
      if row.canonicalDecomposition.size = 2 then
        decide (Decompose.fullCanonicalDecompose row.codepoint
                = Decompose.fullCanonicalDecompose
                    (row.canonicalDecomposition.getD 0 0)
                  ++ Decompose.fullCanonicalDecompose
                    (row.canonicalDecomposition.getD 1 0))
      else
        true) = true := by
  native_decide

-- ── pointwise extraction (non-Hangul) ─────────────────────────────────────────

/-- Pointwise lift of `ucd_twoEltDecomp_factoring`: for any codepoint
    `p` whose `Lookup.canonicalDecomposition` returns a 2-element
    array, the full decomposition factors across the two elements.

    Uses `Lookup.lookupRow` to identify the UCD row backing `p`, then
    applies the native_decide table. -/
theorem fullCanonicalDecompose_of_twoElt_decomp
    (p d c : Nat) (h : Lookup.canonicalDecomposition p = #[d, c]) :
    Decompose.fullCanonicalDecompose p
      = Decompose.fullCanonicalDecompose d
        ++ Decompose.fullCanonicalDecompose c := by
  have hLookup : ∃ row, Lookup.lookupRow p = some row
                       ∧ row.canonicalDecomposition = #[d, c] := by
    unfold Lookup.canonicalDecomposition at h
    cases hL : Lookup.lookupRow p with
    | none =>
      rw [hL] at h
      simp at h
    | some row =>
      rw [hL] at h
      exact ⟨row, rfl, h⟩
  obtain ⟨row, hRowEq, hRowDecomp⟩ := hLookup
  have hRowMem : row ∈ UnicodeData.rows :=
    Array.mem_of_find?_eq_some hRowEq
  rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
  have hCodepointEq : row.codepoint = p := by
    have hFindProp := Array.find?_eq_some_iff_getElem.mp hRowEq
    obtain ⟨hCodeDecide, hExists⟩ := hFindProp
    have hExistsUnused := hExists
    clear hExistsUnused
    exact of_decide_eq_true hCodeDecide
  have hSize : row.canonicalDecomposition.size = 2 := by
    rw [hRowDecomp]; rfl
  have hGet0 : row.canonicalDecomposition.getD 0 0 = d := by
    rw [hRowDecomp]; rfl
  have hGet1 : row.canonicalDecomposition.getD 1 0 = c := by
    rw [hRowDecomp]; rfl
  have hTable := ucd_twoEltDecomp_factoring
  rw [Array.all_eq_true] at hTable
  have hTCell := hTable i hi
  rw [hElem] at hTCell
  rw [if_pos hSize] at hTCell
  rw [hGet0, hGet1] at hTCell
  rw [hCodepointEq] at hTCell
  exact of_decide_eq_true hTCell

/-- **Unconditional non-Hangul primary-composite factorization.**
    When `Hangul.composePair? d c = none` and `primaryComposite? d c
    = some p`, the factorization holds. Composed from
    `Invertibility.primaryComposite_canonicalDecomposition_nonHangul`
    (which gives `canonicalDecomposition p = #[d, c]`) and
    `fullCanonicalDecompose_of_twoElt_decomp` (the UCD-table-backed lift). -/
theorem fullCanonicalDecompose_of_nonHangul_primaryComposite
    (d c p : Nat) (hHangul : Hangul.composePair? d c = none)
    (h : Compose.primaryComposite? d c = some p) :
    Decompose.fullCanonicalDecompose p
      = Decompose.fullCanonicalDecompose d
        ++ Decompose.fullCanonicalDecompose c := by
  have hCanon : Lookup.canonicalDecomposition p = #[d, c] :=
    Invertibility.primaryComposite_canonicalDecomposition_nonHangul d c p hHangul h
  exact fullCanonicalDecompose_of_twoElt_decomp p d c hCanon

-- ── Hangul factorization tables ────────────────────────────────────────────────

/-- **Hangul L+V factorization table.** For every valid `(L, V)` jamo
    pair, the full canonical decomposition of the composed LV syllable
    equals the concatenation of the decompositions of L and V. Closed
    by `native_decide` over the 19×21=399 valid pairs. -/
theorem hangul_LV_factoring :
    (List.range 19).all (fun lIdx =>
      (List.range 21).all (fun vIdx =>
        let L := 0x1100 + lIdx
        let V := 0x1161 + vIdx
        match Hangul.composePair? L V with
        | some p =>
          decide (Decompose.fullCanonicalDecompose p
                  = Decompose.fullCanonicalDecompose L
                    ++ Decompose.fullCanonicalDecompose V)
        | none => true)) = true := by
  native_decide

/-- **Hangul LV+T factorization table.** For every `(LV, T)` pair where
    LV is an LV-only Hangul syllable and T is a valid T jamo (T in
    `[TBase+1, TBase+TCount-1]` = `[0x11A8, 0x11C2]`, excluding the
    `isTJamo` off-by-one at `0x11C3`), the factorization holds. Closed
    by `native_decide` over 399×27=10773 valid pairs. -/
theorem hangul_LVT_factoring :
    (List.range (19 * 21)).all (fun lvIdx =>
      (List.range 27).all (fun tIdx =>
        let LV := 0xAC00 + lvIdx * 28
        let T := 0x11A8 + tIdx
        match Hangul.composePair? LV T with
        | some p =>
          decide (Decompose.fullCanonicalDecompose p
                  = Decompose.fullCanonicalDecompose LV
                    ++ Decompose.fullCanonicalDecompose T)
        | none => true)) = true := by
  native_decide

-- ── remaining Hangul hypothesis (narrowed) ────────────────────────────────────

/-- **Hangul decomposition-factorization hypothesis** (remaining after
    the non-Hangul half closes). Narrowed to exclude the off-by-one
    edge in `Hangul.isTJamo` (which accepts `c = 0x11C3 = TBase +
    TCount`, a codepoint outside the UCD-17.0 valid T jamo range
    [0x11A8, 0x11C2]; the factorization provably fails there).

    For every `(d, c)` with `Hangul.composePair? d c = some p` AND
    `c < TBase + TCount` (i.e., c is NOT the off-by-one edge), the
    factorization holds. Closure path: extract via case analysis on the
    `composePair?` branch (L+V or LV+T) into the respective
    `native_decide` table. -/
def FullCanonicalDecomposeFactoringHangul : Prop :=
  ∀ (d c p : Nat),
    Hangul.composePair? d c = some p →
    c < Hangul.TBase + Hangul.TCount →
    Decompose.fullCanonicalDecompose p
      = Decompose.fullCanonicalDecompose d
        ++ Decompose.fullCanonicalDecompose c

/-- **Unconditional closure of the Hangul factorization hypothesis**
    via the `native_decide` tables. Dispatches on `composePair?`'s
    L+V and LV+T branches. -/
theorem fullCanonicalDecomposeFactoringHangul_holds :
    FullCanonicalDecomposeFactoringHangul := by
  intro d c p h hCRange
  -- Keep original h for applying to table; use working copy for dispatch.
  have hOrig : Hangul.composePair? d c = some p := h
  have hWork : Hangul.composePair? d c = some p := h
  unfold Hangul.composePair? at hWork
  split at hWork
  · -- L+V case
    next hLV =>
      obtain ⟨hL, hV⟩ := hLV
      unfold Hangul.isLJamo at hL
      unfold Hangul.isVJamo at hV
      obtain ⟨hLLo, hLHi⟩ := of_decide_eq_true hL
      obtain ⟨hVLo, hVHi⟩ := of_decide_eq_true hV
      simp only [Hangul.LBase, Hangul.LCount] at hLLo hLHi
      simp only [Hangul.VBase, Hangul.VCount] at hVLo hVHi
      have hLIdxRange : d - 0x1100 < 19 := by omega
      have hVIdxRange : c - 0x1161 < 21 := by omega
      have hDEq : 0x1100 + (d - 0x1100) = d := by omega
      have hCEq : 0x1161 + (c - 0x1161) = c := by omega
      have hTable := hangul_LV_factoring
      rw [List.all_eq_true] at hTable
      have hTRow := hTable (d - 0x1100) (List.mem_range.mpr hLIdxRange)
      rw [List.all_eq_true] at hTRow
      have hTCell := hTRow (c - 0x1161) (List.mem_range.mpr hVIdxRange)
      simp only at hTCell
      rw [hDEq, hCEq] at hTCell
      rw [hOrig] at hTCell
      simp only at hTCell
      exact of_decide_eq_true hTCell
  · split at hWork
    · -- LV+T case
      next hLVT =>
        obtain ⟨hLV, hT⟩ := hLVT
        unfold Hangul.isHangulSyllable at hLV
        unfold Hangul.isTJamo at hT
        obtain ⟨hLVLo, hLVHi⟩ := of_decide_eq_true hLV
        obtain ⟨hTLo, hTHi⟩ := of_decide_eq_true hT
        simp only [Hangul.SBase, Hangul.SCount, Hangul.LCount,
                   Hangul.NCount, Hangul.VCount, Hangul.TCount] at hLVLo hLVHi
        simp only [Hangul.TBase, Hangul.TCount] at hTLo hTHi
        simp only [Hangul.TBase, Hangul.TCount] at hCRange
        -- Resolve the inner `have sIndex` + `if` via by_cases.
        by_cases hMod : (d - Hangul.SBase) % Hangul.TCount = 0
        · simp only [hMod] at hWork
          have hLVIdxRange : (d - 0xAC00) / 28 < 19 * 21 := by
            simp only [Hangul.SBase] at hMod
            omega
          have hTIdxRange : c - 0x11A8 < 27 := by omega
          have hDEq : 0xAC00 + ((d - 0xAC00) / 28) * 28 = d := by
            simp only [Hangul.SBase, Hangul.TCount] at hMod
            omega
          have hCEq : 0x11A8 + (c - 0x11A8) = c := by omega
          have hTable := hangul_LVT_factoring
          rw [List.all_eq_true] at hTable
          have hTRow := hTable ((d - 0xAC00) / 28)
                         (List.mem_range.mpr hLVIdxRange)
          rw [List.all_eq_true] at hTRow
          have hTCell := hTRow (c - 0x11A8)
                           (List.mem_range.mpr hTIdxRange)
          simp only at hTCell
          rw [hDEq, hCEq] at hTCell
          rw [hOrig] at hTCell
          simp only at hTCell
          exact of_decide_eq_true hTCell
        · simp only [hMod] at hWork
          exact absurd hWork (by simp)
    · simp at hWork

/-- **Combined factorization, now unconditional (modulo the Hangul
    edge-case carve-out).** Dispatches on `Hangul.composePair?`:
    non-Hangul path via `fullCanonicalDecompose_of_nonHangul_primaryComposite`;
    Hangul path via `fullCanonicalDecomposeFactoringHangul_holds`.

    Requires `c < TBase + TCount` only on the Hangul path. -/
theorem fullCanonicalDecompose_of_primaryComposite
    (d c p : Nat) (h : Compose.primaryComposite? d c = some p)
    (hCRange : c < Hangul.TBase + Hangul.TCount) :
    Decompose.fullCanonicalDecompose p
      = Decompose.fullCanonicalDecompose d
        ++ Decompose.fullCanonicalDecompose c := by
  cases hHPath : Hangul.composePair? d c with
  | none =>
    exact fullCanonicalDecompose_of_nonHangul_primaryComposite d c p hHPath h
  | some pH =>
    have hPrim : Compose.primaryComposite? d c = some pH := by
      unfold Compose.primaryComposite?
      rw [hHPath]
    rw [hPrim] at h
    have hPEq : pH = p := Option.some.inj h
    rw [← hPEq]
    exact fullCanonicalDecomposeFactoringHangul_holds d c pH hHPath hCRange

/-- **Reorder strict-max commutativity hypothesis.** When the emitted
    prefix, active starter, and buffered non-starters are fixed, and a
    strict-max non-starter `cp` (CCC strictly greater than every
    buffered non-starter's CCC) is absorbed into a primary composite
    `p` with the active starter, the NFD form of the resulting
    sequence equals the NFD form of the input sequence with `cp`
    appended.

    Captures the sort-stability across surrounding context that
    Case 7 requires. Parallel work to `reorder_absorbing_left`; the
    list-level foundation is in
    `ReorderAppend.sortNonStarterRun_{cons,append}_max`. -/
def ReorderCommutesStrictMax : Prop :=
  ∀ (emitted : Array Nat) (st cp p : Nat)
    (buffer : List Nat) (maxCCC : Nat),
    Compose.primaryComposite? st cp = some p →
    Lookup.canonicalCombiningClass cp ≠ 0 →
    ¬(Lookup.canonicalCombiningClass cp ≤ maxCCC) →
    (∀ y ∈ buffer, 0 < Lookup.canonicalCombiningClass y
                   ∧ Lookup.canonicalCombiningClass y ≤ maxCCC) →
    NFC.toNFD (emitted ++ #[p] ++ buffer.reverse.toArray)
      = NFC.toNFD (emitted ++ #[st] ++ buffer.reverse.toArray ++ #[cp])

-- ── Context-lifted factorization at the NFD level ─────────────────────────────

/-- Corollary of the primary-composite factorization: for any surrounding
    context `X`, `toNFD (X ++ #[p]) = toNFD (X ++ #[d] ++ #[c])` when
    `primaryComposite? d c = some p` and `c` is not the `0x11C3`
    edge-case jamo. -/
theorem toNFD_primaryComposite_expand
    (X : Array Nat) (d c p : Nat)
    (h : Compose.primaryComposite? d c = some p)
    (hCRange : c < Hangul.TBase + Hangul.TCount) :
    NFC.toNFD (X ++ #[p]) = NFC.toNFD (X ++ #[d] ++ #[c]) := by
  unfold NFC.toNFD
  rw [Distribute.decomposeSequence_append X #[p]]
  rw [Distribute.decomposeSequence_singleton p]
  rw [fullCanonicalDecompose_of_primaryComposite d c p h hCRange]
  rw [Distribute.decomposeSequence_append (X ++ #[d]) #[c]]
  rw [Distribute.decomposeSequence_append X #[d]]
  rw [Distribute.decomposeSequence_singleton d]
  rw [Distribute.decomposeSequence_singleton c]
  rw [Array.append_assoc]

/-- **Non-Hangul variant of `toNFD_primaryComposite_expand`.** When
    `Hangul.composePair? d c = none`, the expansion chain goes through
    `fullCanonicalDecompose_of_nonHangul_primaryComposite` (already
    unconditional), so the `c < TBase + TCount` bound from the Hangul
    path is not needed. Shape otherwise identical to
    `toNFD_primaryComposite_expand`. Used by the dispatcher's non-Hangul
    branch of Case 3 (which covers the 35 Brahmic + musical-symbol
    starter-starter primary composites catalogued in the UCD audit,
    all of which route through the non-Hangul `UnicodeData.rows` scan). -/
theorem toNFD_primaryComposite_expand_nonHangul
    (X : Array Nat) (d c p : Nat)
    (hHangul : Hangul.composePair? d c = none)
    (h : Compose.primaryComposite? d c = some p) :
    NFC.toNFD (X ++ #[p]) = NFC.toNFD (X ++ #[d] ++ #[c]) := by
  unfold NFC.toNFD
  rw [Distribute.decomposeSequence_append X #[p]]
  rw [Distribute.decomposeSequence_singleton p]
  rw [fullCanonicalDecompose_of_nonHangul_primaryComposite d c p hHangul h]
  rw [Distribute.decomposeSequence_append (X ++ #[d]) #[c]]
  rw [Distribute.decomposeSequence_append X #[d]]
  rw [Distribute.decomposeSequence_singleton d]
  rw [Distribute.decomposeSequence_singleton c]
  rw [Array.append_assoc]

/-- **Hangul composePair? second-argument bound**. When
    `Hangul.composePair? first second = some _`, the second argument
    is strictly less than `TBase + TCount = 0x11C3`. Derived from the
    V-jamo range on the `L+V` path (second ∈ [0x1161, 0x1175]) and
    the strict T-jamo range on the `LV+T` path (second ∈ [0x11A8,
    0x11C2] post-isTJamo-fix). Lets the dispatcher's Case 3 Hangul
    branch satisfy the existing Case 3 closure's `hCpRange`
    parameter without requiring a caller-supplied bound. -/
theorem composePair?_second_lt_TBase_plus_TCount
    (first second p : Nat) (h : Hangul.composePair? first second = some p) :
    second < Hangul.TBase + Hangul.TCount := by
  unfold Hangul.composePair? at h
  split at h
  · -- L+V case
    next hLV =>
      have hV : Hangul.isVJamo second = true := hLV.2
      unfold Hangul.isVJamo at hV
      have hVBound := of_decide_eq_true hV
      simp only [Hangul.VBase, Hangul.VCount, Hangul.TBase, Hangul.TCount]
        at hVBound ⊢
      omega
  · split at h
    · -- LV+T case
      next hLVT =>
        have hT : Hangul.isTJamo second = true := hLVT.2
        unfold Hangul.isTJamo at hT
        have hTBound := of_decide_eq_true hT
        simp only [Hangul.TBase, Hangul.TCount] at hTBound ⊢
        exact hTBound.2
    · simp at h

/-- **V jamos are starters.** Every codepoint in the V jamo range
    `[0x1161, 0x1176)` has `ccc = 0`. Closed by `native_decide` over
    the 21 V jamos. -/
theorem vJamo_ccc_zero :
    (List.range 21).all (fun i =>
      decide (Lookup.canonicalCombiningClass (0x1161 + i) = 0)) = true := by
  native_decide

/-- **T jamos are starters.** Every codepoint in the T jamo range
    `[0x11A8, 0x11C3)` (post-isTJamo-fix) has `ccc = 0`. Closed by
    `native_decide` over the 27 valid T jamos. -/
theorem tJamo_ccc_zero :
    (List.range 27).all (fun i =>
      decide (Lookup.canonicalCombiningClass (0x11A8 + i) = 0)) = true := by
  native_decide

/-- **Hangul.composePair? second-argument is a starter.** When
    `Hangul.composePair? first second = some _`, the second argument
    has `ccc = 0`. Derived from the V-jamo and T-jamo ccc-is-zero
    tables above. Contrapositive: `ccc second ≠ 0 → Hangul.composePair?
    first second = none`. -/
theorem composePair?_second_ccc_zero
    (first second p : Nat) (h : Hangul.composePair? first second = some p) :
    Lookup.canonicalCombiningClass second = 0 := by
  unfold Hangul.composePair? at h
  split at h
  · -- L+V case: second is a V jamo
    next hLV =>
      have hV : Hangul.isVJamo second = true := hLV.2
      unfold Hangul.isVJamo at hV
      have hVBound := of_decide_eq_true hV
      simp only [Hangul.VBase, Hangul.VCount] at hVBound
      have hTable := vJamo_ccc_zero
      rw [List.all_eq_true] at hTable
      have hIRange : second - 0x1161 < 21 := by omega
      have hIMem : second - 0x1161 ∈ List.range 21 := List.mem_range.mpr hIRange
      have hAt := of_decide_eq_true (hTable (second - 0x1161) hIMem)
      have hEq : 0x1161 + (second - 0x1161) = second := by omega
      rw [hEq] at hAt
      exact hAt
  · split at h
    · -- LV+T case: second is a T jamo
      next hLVT =>
        have hT : Hangul.isTJamo second = true := hLVT.2
        unfold Hangul.isTJamo at hT
        have hTBound := of_decide_eq_true hT
        simp only [Hangul.TBase, Hangul.TCount] at hTBound
        have hTable := tJamo_ccc_zero
        rw [List.all_eq_true] at hTable
        have hIRange : second - 0x11A8 < 27 := by omega
        have hIMem : second - 0x11A8 ∈ List.range 27 := List.mem_range.mpr hIRange
        have hAt := of_decide_eq_true (hTable (second - 0x11A8) hIMem)
        have hEq : 0x11A8 + (second - 0x11A8) = second := by omega
        rw [hEq] at hAt
        exact hAt
    · simp at h

/-- **Contrapositive: non-starter second argument → composePair? returns none.**
    Used by the `ReorderCommutesStrictMax` discharge to rule out the
    Hangul branch when the stepCompose input has `ccc cp ≠ 0`. -/
theorem composePair?_none_of_nonStarter_second
    (first second : Nat) (h : Lookup.canonicalCombiningClass second ≠ 0) :
    Hangul.composePair? first second = none := by
  cases hH : Hangul.composePair? first second with
  | none => rfl
  | some p =>
    exfalso
    exact h (composePair?_second_ccc_zero first second p hH)

-- ── Case 3 close (conditional on Hangul factoring hypothesis only) ────────────

/-- **Case 3** closure, conditional on `cp` not being the `0x11C3`
    off-by-one edge: primary-composite absorb at starter boundary
    (empty buffer). The non-Hangul sub-case is handled unconditionally;
    the Hangul sub-case uses the `native_decide`-backed
    `fullCanonicalDecomposeFactoringHangul_holds`. -/
theorem stepPreserves_case_primary_absorb_starter
    (s : Compose.ComposeState) (cp : Nat) (pre : Array Nat)
    (st : Nat) (p : Nat)
    (hSome : s.starter = some st)
    (hCCC : Lookup.canonicalCombiningClass cp = 0)
    (hBufEmpty : s.buffer.isEmpty = true)
    (hPrim : Compose.primaryComposite? st cp = some p)
    (hCpRange : cp < Hangul.TBase + Hangul.TCount)
    (hEquiv : NFDEquivalent (expand s) pre) :
    NFDEquivalent (expand (Compose.stepCompose s cp)) (pre ++ #[cp]) := by
  have hBuf : s.buffer = [] := List.isEmpty_iff.mp hBufEmpty
  have hStep : Compose.stepCompose s cp = { s with starter := some p } := by
    unfold Compose.stepCompose
    rw [hSome]
    simp [hCCC, hBufEmpty, hPrim]
  have hExpandInput : expand s = s.emitted ++ #[st] := by
    unfold expand; rw [hSome, hBuf]; simp
  have hExpandOutput : expand (Compose.stepCompose s cp) = s.emitted ++ #[p] := by
    rw [hStep]; unfold expand; rw [hBuf]; simp
  rw [hExpandOutput]
  unfold NFDEquivalent
  rw [toNFD_primaryComposite_expand s.emitted st cp p hPrim hCpRange]
  have hEquiv' : NFC.toNFD (s.emitted ++ #[st]) = NFC.toNFD pre := by
    unfold NFDEquivalent at hEquiv
    rw [← hExpandInput]; exact hEquiv
  exact ToNFDAppend.toNFD_congr_append #[cp] hEquiv'

/-- **Case 3 non-Hangul closure**: primary-composite absorb at starter
    boundary when the composition goes through the UnicodeData path
    (`Hangul.composePair? st cp = none`). Parallels
    `stepPreserves_case_primary_absorb_starter` but uses
    `toNFD_primaryComposite_expand_nonHangul`, which does not require
    the `cp < TBase + TCount` bound. Handles the 35 non-Hangul
    starter-starter primary composites catalogued in the UCD audit,
    including the 18 with `cp ≥ 0x11C3` (Brahmic vowel signs +
    musical-symbol combining stems). -/
theorem stepPreserves_case_primary_absorb_starter_nonHangul
    (s : Compose.ComposeState) (cp : Nat) (pre : Array Nat)
    (st : Nat) (p : Nat)
    (hSome : s.starter = some st)
    (hCCC : Lookup.canonicalCombiningClass cp = 0)
    (hBufEmpty : s.buffer.isEmpty = true)
    (hPrim : Compose.primaryComposite? st cp = some p)
    (hHangul : Hangul.composePair? st cp = none)
    (hEquiv : NFDEquivalent (expand s) pre) :
    NFDEquivalent (expand (Compose.stepCompose s cp)) (pre ++ #[cp]) := by
  have hBuf : s.buffer = [] := List.isEmpty_iff.mp hBufEmpty
  have hStep : Compose.stepCompose s cp = { s with starter := some p } := by
    unfold Compose.stepCompose
    rw [hSome]
    simp [hCCC, hBufEmpty, hPrim]
  have hExpandInput : expand s = s.emitted ++ #[st] := by
    unfold expand; rw [hSome, hBuf]; simp
  have hExpandOutput : expand (Compose.stepCompose s cp) = s.emitted ++ #[p] := by
    rw [hStep]; unfold expand; rw [hBuf]; simp
  rw [hExpandOutput]
  unfold NFDEquivalent
  rw [toNFD_primaryComposite_expand_nonHangul s.emitted st cp p hHangul hPrim]
  have hEquiv' : NFC.toNFD (s.emitted ++ #[st]) = NFC.toNFD pre := by
    unfold NFDEquivalent at hEquiv
    rw [← hExpandInput]; exact hEquiv
  exact ToNFDAppend.toNFD_congr_append #[cp] hEquiv'

-- ── Case 7 close (conditional on both hypotheses) ─────────────────────────────

/-- **Case 7** closure, conditional on `ReorderCommutesStrictMax`:
    strict-max non-starter primary-composite absorb. The absorb
    preserves `emitted` and `buffer`, replacing the active starter
    `st` with the composite `p`. -/
theorem stepPreserves_case_primary_absorb_strict_max
    (hRCSM : ReorderCommutesStrictMax)
    (s : Compose.ComposeState) (cp : Nat) (pre : Array Nat)
    (st : Nat) (p : Nat)
    (hSome : s.starter = some st)
    (hCCC : Lookup.canonicalCombiningClass cp ≠ 0)
    (hStrictMax : ¬(Lookup.canonicalCombiningClass cp ≤ s.maxCCC))
    (hPrim : Compose.primaryComposite? st cp = some p)
    (hBuf : ∀ y ∈ s.buffer, 0 < Lookup.canonicalCombiningClass y
                            ∧ Lookup.canonicalCombiningClass y ≤ s.maxCCC)
    (hEquiv : NFDEquivalent (expand s) pre) :
    NFDEquivalent (expand (Compose.stepCompose s cp)) (pre ++ #[cp]) := by
  have hStep : Compose.stepCompose s cp = { s with starter := some p } := by
    unfold Compose.stepCompose
    rw [hSome]
    simp [hCCC, hStrictMax, hPrim]
  have hExpandInput : expand s = s.emitted ++ #[st] ++ s.buffer.reverse.toArray := by
    unfold expand; rw [hSome]
  have hExpandOutput :
      expand (Compose.stepCompose s cp)
        = s.emitted ++ #[p] ++ s.buffer.reverse.toArray := by
    rw [hStep]; unfold expand; simp
  rw [hExpandOutput]
  unfold NFDEquivalent
  rw [hRCSM s.emitted st cp p s.buffer s.maxCCC hPrim hCCC hStrictMax hBuf]
  have hEquiv' :
      NFC.toNFD (s.emitted ++ #[st] ++ s.buffer.reverse.toArray)
        = NFC.toNFD pre := by
    unfold NFDEquivalent at hEquiv
    rw [← hExpandInput]; exact hEquiv
  exact ToNFDAppend.toNFD_congr_append #[cp] hEquiv'

-- ═══════════════════════════════════════════════════════════════════════════════
-- DISPATCHER: StepPreservesNFDEquivalence given ReorderCommutesStrictMax
--
-- Composes the 8 case closures into the top-level
-- `StepPreservesNFDEquivalence` Prop, conditional only on
-- `ReorderCommutesStrictMax`. Each stepCompose branch is dispatched to
-- its corresponding closure; Case 3 is split internally on
-- `Hangul.composePair?` to route Hangul inputs through the
-- `hCpRange`-bearing closure (with the bound derived from
-- `composePair?_second_lt_TBase_plus_TCount`) and non-Hangul inputs
-- through the parallel non-Hangul closure.
--
-- Case 7's `hBuf` hypothesis is discharged from `ComposeStateValid`'s
-- second conjunct, which is why the strengthened invariant is required.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **StepPreservesNFDEquivalence given ReorderCommutesStrictMax.** The
    sole remaining open hypothesis is `ReorderCommutesStrictMax` (the
    NFD-level strict-max reorder commutativity required by Case 7).
    All other hypotheses are discharged internally via the 8 case
    closures + the strengthened `ComposeStateValid`. -/
theorem stepPreservesNFDEquivalence_given_rcsm
    (hRCSM : ReorderCommutesStrictMax) :
    StepPreservesNFDEquivalence := by
  intro s cp pre hv hEquiv
  obtain ⟨hvStarter, hvBuffer⟩ := hv
  cases hS : s.starter with
  | none =>
    by_cases hCCC : Lookup.canonicalCombiningClass cp = 0
    · -- Case 1
      exact stepPreserves_case_leading_starter s cp pre
              ⟨hvStarter, hvBuffer⟩ hS hCCC hEquiv
    · -- Case 2
      exact stepPreserves_case_leading_nonstarter s cp pre
              ⟨hvStarter, hvBuffer⟩ hS hCCC hEquiv
  | some st =>
    by_cases hCCC : Lookup.canonicalCombiningClass cp = 0
    · -- Cases 3, 4, 5 (starter=some, ccc=0)
      by_cases hBufEm : s.buffer.isEmpty = true
      · -- Cases 3, 4
        cases hPrim : Compose.primaryComposite? st cp with
        | some p =>
          -- Case 3: dispatch on Hangul.composePair?
          cases hH : Hangul.composePair? st cp with
          | some pH =>
            -- Hangul path: derive cp < TBase + TCount from composePair? output
            have hCpRange : cp < Hangul.TBase + Hangul.TCount :=
              composePair?_second_lt_TBase_plus_TCount st cp pH hH
            exact stepPreserves_case_primary_absorb_starter s cp pre st p
                    hS hCCC hBufEm hPrim hCpRange hEquiv
          | none =>
            -- Non-Hangul path: use the parallel closure (no hCpRange needed)
            exact stepPreserves_case_primary_absorb_starter_nonHangul s cp pre st p
                    hS hCCC hBufEm hPrim hH hEquiv
        | none =>
          -- Case 4
          exact stepPreserves_case_starter_no_composite s cp pre st
                  hS hCCC hBufEm hPrim hEquiv
      · -- Case 5: buffer non-empty
        have hBufNonEm : s.buffer.isEmpty = false := by
          cases hBE : s.buffer.isEmpty with
          | true => exact absurd hBE hBufEm
          | false => rfl
        exact stepPreserves_case_starter_flush s cp pre st
                hS hCCC hBufNonEm hEquiv
    · -- Cases 6, 7, 8 (starter=some, ccc≠0)
      by_cases hBlock : Lookup.canonicalCombiningClass cp ≤ s.maxCCC
      · -- Case 6: blocked (ccc ≤ maxCCC)
        exact stepPreserves_case_buffer_append s cp pre st
                hS hCCC hBlock hEquiv
      · -- Strict-max (ccc > maxCCC): Cases 7, 8
        cases hPrim : Compose.primaryComposite? st cp with
        | some p =>
          -- Case 7: hBuf derived from strengthened ComposeStateValid
          exact stepPreserves_case_primary_absorb_strict_max hRCSM s cp pre st p
                  hS hCCC hBlock hPrim hvBuffer hEquiv
        | none =>
          -- Case 8
          exact stepPreserves_case_strict_max_no_composite s cp pre st
                  hS hCCC hBlock hPrim hEquiv

/-- **Tactical lemma (closed).** Folding append-singleton over a list
    reconstructs the array. Closed via `Array.push_eq_append` (definitional
    push/append equivalence) and `List.foldl_push_eq_append'` (standard
    library lemma for foldl-push reconstruction). -/
theorem foldOverList (xs : Array Nat) :
    xs.toList.foldl (fun acc (x : Nat) => acc ++ #[x]) #[] = xs := by
  have hPushEq : (fun (acc : Array Nat) (x : Nat) => acc ++ #[x]) =
                 (fun acc x => acc.push x) := by
    funext acc x
    rfl
  rw [hPushEq, List.foldl_push_eq_append']
  simp

/-- Folding `stepCompose` preserves the NFD-equivalence invariant — conditional
    on the step-preservation hypothesis. The fold-over-list tactical detail
    is discharged unconditionally via `foldOverList`. The `ComposeStateValid`
    invariant is threaded through the induction unconditionally via
    `initialState_valid` and `stepCompose_preserves_valid`. -/
theorem foldl_stepCompose_NFDEquivalence_given
    (hStep : StepPreservesNFDEquivalence) (xs : Array Nat) :
    NFDEquivalent (expand (xs.foldl Compose.stepCompose Compose.initialState)) xs := by
  rw [← Array.foldl_toList]
  have key : ∀ (l : List Nat) (s : Compose.ComposeState) (pre : Array Nat),
      ComposeStateValid s →
      NFDEquivalent (expand s) pre →
      NFDEquivalent (expand (l.foldl Compose.stepCompose s))
                    (l.foldl (fun acc x => acc ++ #[x]) pre) := by
    intro l
    induction l with
    | nil =>
      intro s pre hv h
      clear hv
      exact h
    | cons hd tl ih =>
      intro s pre hv h
      simp only [List.foldl_cons]
      apply ih (Compose.stepCompose s hd)
        (pre ++ #[hd])
        (stepCompose_preserves_valid s hd hv)
      exact hStep s hd pre hv h
  have hInit : NFDEquivalent (expand Compose.initialState) #[] := by
    unfold expand Compose.initialState
    simp
    rfl
  have hRes := key xs.toList Compose.initialState #[] initialState_valid hInit
  rw [foldOverList xs] at hRes
  exact hRes

-- ═══════════════════════════════════════════════════════════════════════════════
-- DECOMPOSE-COMPOSE INVERSION (conditional)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Decompose-compose inversion (NFC idempotence pillar 2) — conditional
    on the step-preservation hypothesis.** For any NFD-form input `x`,
    `toNFD (compose x) = x`. -/
theorem decompose_compose_inversion_given
    (hStep : StepPreservesNFDEquivalence)
    (x : Array Nat) (hx : NFC.toNFD x = x) :
    NFC.toNFD (Compose.compose x) = x := by
  rw [compose_eq_expand]
  have hEquiv := foldl_stepCompose_NFDEquivalence_given hStep x
  unfold NFDEquivalent at hEquiv
  rw [hEquiv]
  exact hx

-- ═══════════════════════════════════════════════════════════════════════════════
-- NFC IDEMPOTENCE (conditional)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **NFC idempotence — conditional on the step-preservation hypothesis.**
    `toNFC (toNFC x) = toNFC x` for all inputs. Once
    `StepPreservesNFDEquivalence` is closed, this becomes unconditional. -/
theorem toNFC_idempotent_given
    (hStep : StepPreservesNFDEquivalence)
    (x : Array Nat) :
    NFC.toNFC (NFC.toNFC x) = NFC.toNFC x := by
  unfold NFC.toNFC
  have hNFD : NFC.toNFD (NFC.toNFD x) = NFC.toNFD x :=
    NFD.toNFD_idempotent x
  rw [decompose_compose_inversion_given hStep (NFC.toNFD x) hNFD]

-- ═══════════════════════════════════════════════════════════════════════════════
-- NFD-NFC CANCELLATION (conditional)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **NFD-NFC cancellation — conditional on the step-preservation hypothesis.**
    `toNFD ∘ toNFC = toNFD`. Derived directly from
    `decompose_compose_inversion_given` applied to `toNFD x` (which is
    trivially in NFD form by `toNFD_idempotent`). -/
theorem toNFD_toNFC_eq_toNFD_given
    (hStep : StepPreservesNFDEquivalence)
    (x : Array Nat) :
    NFC.toNFD (NFC.toNFC x) = NFC.toNFD x := by
  -- toNFC x = compose (toNFD x) by definition
  unfold NFC.toNFC
  -- toNFD x is NFD form (toNFD idempotent)
  have hNFD : NFC.toNFD (NFC.toNFD x) = NFC.toNFD x :=
    NFD.toNFD_idempotent x
  -- decompose_compose_inversion: toNFD (compose y) = y for NFD-form y.
  exact decompose_compose_inversion_given hStep (NFC.toNFD x) hNFD

-- ═══════════════════════════════════════════════════════════════════════════════
-- CCC PRESERVATION UNDER CANONICAL DECOMPOSITION
--
-- Closes the NFD-level `ReorderCommutesStrictMax` by establishing the
-- UCD invariant that `fullCanonicalDecompose` preserves the CCC on
-- every non-starter input. With this, the strict-max separation
-- between `cp`'s decomposition and the buffer's decomposition follows
-- from the input strict-max, and the multi-element
-- `reorder_commutes_strict_max_multi` (in ReorderAppend)
-- swaps the two decomposed runs.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **UCD invariant: non-starter rows preserve CCC under full canonical
    decomposition.** For every row with `ccc > 0`, every codepoint in
    its `fullCanonicalDecompose` output has the same CCC. Closed by
    `native_decide` over the 3045-row pinned UnicodeData table. -/
theorem nonStarter_fullCanonicalDecompose_preserves_ccc :
    UnicodeData.rows.all (fun row =>
      decide (row.canonicalCombiningClass = 0)
      || (Decompose.fullCanonicalDecompose row.codepoint).all
          (fun cp' => decide (Lookup.canonicalCombiningClass cp'
                                = row.canonicalCombiningClass))) = true := by
  native_decide

/-- **Pointwise CCC preservation.** For any non-starter codepoint `cp`,
    every element of `fullCanonicalDecompose cp` has CCC equal to
    `ccc cp`. Derived from the UCD table above by locating `cp`'s row
    via `lookupRow` (non-starter implies in the table). -/
theorem fullCanonicalDecompose_preserves_ccc_of_nonStarter
    (cp : Nat) (h : Lookup.canonicalCombiningClass cp ≠ 0)
    (cp' : Nat) (hMem : cp' ∈ Decompose.fullCanonicalDecompose cp) :
    Lookup.canonicalCombiningClass cp' = Lookup.canonicalCombiningClass cp := by
  cases hL : Lookup.lookupRow cp with
  | none =>
    exfalso
    apply h
    unfold Lookup.canonicalCombiningClass
    rw [hL]
  | some row =>
    have hCpEq : row.codepoint = cp := by
      unfold Lookup.lookupRow at hL
      have hFind := Array.find?_eq_some_iff_getElem.mp hL
      obtain ⟨hDec, hRest⟩ := hFind
      clear hRest
      exact of_decide_eq_true hDec
    have hRowCCC : row.canonicalCombiningClass = Lookup.canonicalCombiningClass cp := by
      unfold Lookup.canonicalCombiningClass
      rw [hL]
    have hRowMem : row ∈ UnicodeData.rows := Array.mem_of_find?_eq_some hL
    have hTable := nonStarter_fullCanonicalDecompose_preserves_ccc
    rw [Array.all_eq_true] at hTable
    rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
    have hAt := hTable i hi
    rw [hElem] at hAt
    have hRowCCCne : row.canonicalCombiningClass ≠ 0 := by
      rw [hRowCCC]; exact h
    -- hAt : (decide (row.ccc = 0) || preserve-bool) = true.
    -- row.ccc ≠ 0, so the first disjunct is false, forcing preserve-bool = true.
    have hNotZero : decide (row.canonicalCombiningClass = 0) = false :=
      decide_eq_false hRowCCCne
    rw [hNotZero, Bool.false_or] at hAt
    rw [Array.all_eq_true] at hAt
    rw [← hCpEq] at hMem
    rcases Array.getElem_of_mem hMem with ⟨j, hj, hJElem⟩
    have hCpcEq := of_decide_eq_true (hAt j hj)
    rw [hJElem] at hCpcEq
    rw [hCpcEq, hRowCCC]

/-- **Generic foldl-append membership lemma.** Local copy of the
    helper from `Decompose.lean`; the private version there is
    inaccessible from this module. -/
theorem mem_foldl_fullCanonicalDecompose
    (Y : Array Nat) (z : Nat)
    (hZ : z ∈ (Decompose.decomposeSequence Y).toList) :
    ∃ y ∈ Y.toList, z ∈ Decompose.fullCanonicalDecompose y := by
  unfold Decompose.decomposeSequence at hZ
  rw [← Array.foldl_toList] at hZ
  have key : ∀ (l : List Nat) (init : Array Nat),
      z ∈ (l.foldl (fun acc y => acc ++ Decompose.fullCanonicalDecompose y)
                    init).toList →
      z ∈ init.toList ∨ ∃ y ∈ l, z ∈ Decompose.fullCanonicalDecompose y := by
    intro l
    induction l with
    | nil => intro init hM; left; simpa using hM
    | cons hd tl ih =>
      intro init hM
      simp only [List.foldl_cons] at hM
      rcases ih (init ++ Decompose.fullCanonicalDecompose hd) hM with hInit | ⟨y, hyM, hyF⟩
      · rcases Array.mem_append.mp (by simpa using hInit) with h1 | h2
        · left; simpa using h1
        · right; exact ⟨hd, by simp, h2⟩
      · right; exact ⟨y, by simp [hyM], hyF⟩
  rcases key Y.toList #[] hZ with hEmpty | ⟨y, hyM, hyF⟩
  · exact absurd hEmpty (by simp)
  · exact ⟨y, hyM, hyF⟩

/-- **Sequence CCC preservation for non-starter arrays.** For every
    array `Y` whose elements are all non-starters with CCC ≤ some
    bound `M`, every element of `decomposeSequence Y` is also a
    non-starter with CCC ≤ `M`. -/
theorem decomposeSequence_nonStarter_preserves_ccc
    (Y : Array Nat) (M : Nat)
    (hYnonStarter : ∀ y ∈ Y.toList, 0 < Lookup.canonicalCombiningClass y)
    (hYbound : ∀ y ∈ Y.toList, Lookup.canonicalCombiningClass y ≤ M) :
    ∀ z ∈ (Decompose.decomposeSequence Y).toList,
      0 < Lookup.canonicalCombiningClass z
      ∧ Lookup.canonicalCombiningClass z ≤ M := by
  intro z hZ
  obtain ⟨y, hyM, hyF⟩ := mem_foldl_fullCanonicalDecompose Y z hZ
  have hYnStar : 0 < Lookup.canonicalCombiningClass y := hYnonStarter y hyM
  have hYccc : Lookup.canonicalCombiningClass y ≤ M := hYbound y hyM
  have hYne : Lookup.canonicalCombiningClass y ≠ 0 := Nat.pos_iff_ne_zero.mp hYnStar
  have hEq : Lookup.canonicalCombiningClass z = Lookup.canonicalCombiningClass y :=
    fullCanonicalDecompose_preserves_ccc_of_nonStarter y hYne z hyF
  refine ⟨?nonStarter, ?bounded⟩
  · rw [hEq]; exact hYnStar
  · rw [hEq]; exact hYccc

/-- **Sequence CCC preservation for a non-starter singleton.** For a
    single non-starter codepoint `cp`, every element of
    `decomposeSequence #[cp] = fullCanonicalDecompose cp` is a
    non-starter with the same CCC as `cp`. -/
theorem fullCanonicalDecompose_nonStarter_preserves_ccc
    (cp : Nat) (h : Lookup.canonicalCombiningClass cp ≠ 0) :
    ∀ c ∈ (Decompose.fullCanonicalDecompose cp).toList,
      0 < Lookup.canonicalCombiningClass c
      ∧ Lookup.canonicalCombiningClass c
          = Lookup.canonicalCombiningClass cp := by
  intro c hMem
  have hMemArr : c ∈ Decompose.fullCanonicalDecompose cp := by simpa using hMem
  have hEq := fullCanonicalDecompose_preserves_ccc_of_nonStarter cp h c hMemArr
  constructor
  · rw [hEq]; exact Nat.pos_of_ne_zero h
  · exact hEq

-- ═══════════════════════════════════════════════════════════════════════════════
-- DISCHARGE OF ReorderCommutesStrictMax
--
-- Combines the Hangul-absurdity lemma, non-Hangul toNFD expansion,
-- decomposeSequence distribution, CCC preservation, and the
-- array-level `reorder_commutes_strict_max_multi` into a proof of
-- the NFD-level `ReorderCommutesStrictMax`. With this, every
-- `_given hStep` corollary in this module becomes unconditionally
-- derivable (Case 7's closure, the dispatcher, and every subsequent
-- NFC idempotence / NFD-NFC cancellation theorem).
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Discharge of `ReorderCommutesStrictMax`.** The NFD-level
    strict-max reorder commutativity holds unconditionally.

    Proof outline:
      1. `ccc cp ≠ 0` forces `Hangul.composePair? st cp = none` (V
         and T jamos are starters).
      2. The non-Hangul primary-composite expansion + `toNFD_congr_append`
         give `toNFD (E ++ [p] ++ buf.rev) = toNFD (E ++ [st] ++ [cp] ++ buf.rev)`.
      3. Unfold `toNFD`, distribute `decomposeSequence` across `++`.
      4. Apply `reorder_commutes_strict_max_multi` with
         `C = fullCanonicalDecompose cp` and
         `Y = decomposeSequence buf.rev.toArray`.
      5. Discharge the `multi` hypotheses from CCC preservation
         (non-starter decomposition preserves CCC) + the `hStrict`
         input hypothesis. -/
theorem reorderCommutesStrictMax_holds : ReorderCommutesStrictMax := by
  intro emitted st cp p buffer maxCCC hPrim hCCCNe hStrict hBuf
  -- Step 1: Derive Hangul.composePair? st cp = none from ccc cp ≠ 0
  have hHangul : Hangul.composePair? st cp = none :=
    composePair?_none_of_nonStarter_second st cp hCCCNe
  -- Step 2: Expand p = [st, cp] in NFD via the non-Hangul helper
  have hExpandP : NFC.toNFD (emitted ++ #[p]) = NFC.toNFD (emitted ++ #[st] ++ #[cp]) :=
    toNFD_primaryComposite_expand_nonHangul emitted st cp p hHangul hPrim
  have hExpandFull : NFC.toNFD (emitted ++ #[p] ++ buffer.reverse.toArray)
                   = NFC.toNFD (emitted ++ #[st] ++ #[cp] ++ buffer.reverse.toArray) := by
    calc NFC.toNFD (emitted ++ #[p] ++ buffer.reverse.toArray)
        _ = NFC.toNFD ((emitted ++ #[p]) ++ buffer.reverse.toArray) := by
            rw [Array.append_assoc]
        _ = NFC.toNFD ((emitted ++ #[st] ++ #[cp]) ++ buffer.reverse.toArray) :=
            ToNFDAppend.toNFD_congr_append buffer.reverse.toArray hExpandP
        _ = NFC.toNFD (emitted ++ #[st] ++ #[cp] ++ buffer.reverse.toArray) := by
            rw [Array.append_assoc]
  rw [hExpandFull]
  -- Step 3: Prove toNFD (emitted ++ [st] ++ [cp] ++ buf.rev) = toNFD (emitted ++ [st] ++ buf.rev ++ [cp])
  -- Unfold toNFD, distribute decomposeSequence, apply reorder_commutes_strict_max_multi.
  unfold NFC.toNFD
  -- Reassociate both sides to (emitted ++ #[st]) ++ ...
  have hLhsAssoc : emitted ++ #[st] ++ #[cp] ++ buffer.reverse.toArray
                 = (emitted ++ #[st]) ++ (#[cp] ++ buffer.reverse.toArray) := by
    rw [Array.append_assoc, Array.append_assoc]
  have hRhsAssoc : emitted ++ #[st] ++ buffer.reverse.toArray ++ #[cp]
                 = (emitted ++ #[st]) ++ (buffer.reverse.toArray ++ #[cp]) := by
    rw [Array.append_assoc, Array.append_assoc]
  rw [hLhsAssoc, hRhsAssoc]
  rw [Distribute.decomposeSequence_append (emitted ++ #[st]) (#[cp] ++ buffer.reverse.toArray)]
  rw [Distribute.decomposeSequence_append (emitted ++ #[st]) (buffer.reverse.toArray ++ #[cp])]
  rw [Distribute.decomposeSequence_append #[cp] buffer.reverse.toArray]
  rw [Distribute.decomposeSequence_append buffer.reverse.toArray #[cp]]
  rw [Distribute.decomposeSequence_singleton cp]
  -- Reassociate to ((A ++ C) ++ Y) vs ((A ++ Y) ++ C) shape
  simp only [← Array.append_assoc]
  -- Now goal in the shape of reorder_commutes_strict_max_multi:
  -- reorder (A ++ C ++ Y) = reorder (A ++ Y ++ C)   -- note: direction
  -- where A = ds(emitted ++ #[st]), C = fullCanonicalDecompose cp, Y = ds buf.rev
  -- reorder_commutes_strict_max_multi: reorder (A ++ Y ++ C) = reorder (A ++ C ++ Y)
  -- The .symm direction matches the goal.
  -- Establish the three multi-element hypotheses.
  have hBufRevNonStarter : ∀ y ∈ buffer.reverse.toArray.toList,
                              0 < Lookup.canonicalCombiningClass y := by
    intro y hy
    have hyBuf : y ∈ buffer := by
      have hyRev : y ∈ buffer.reverse := by simpa using hy
      exact List.mem_reverse.mp hyRev
    exact (hBuf y hyBuf).1
  have hBufRevBound : ∀ y ∈ buffer.reverse.toArray.toList,
                         Lookup.canonicalCombiningClass y ≤ maxCCC := by
    intro y hy
    have hyBuf : y ∈ buffer := by
      have hyRev : y ∈ buffer.reverse := by simpa using hy
      exact List.mem_reverse.mp hyRev
    exact (hBuf y hyBuf).2
  have hYdecomp :
      ∀ z ∈ (Decompose.decomposeSequence buffer.reverse.toArray).toList,
        0 < Lookup.canonicalCombiningClass z
        ∧ Lookup.canonicalCombiningClass z ≤ maxCCC :=
    decomposeSequence_nonStarter_preserves_ccc buffer.reverse.toArray maxCCC
      hBufRevNonStarter hBufRevBound
  have hCdecomp :
      ∀ c ∈ (Decompose.fullCanonicalDecompose cp).toList,
        0 < Lookup.canonicalCombiningClass c
        ∧ Lookup.canonicalCombiningClass c
            = Lookup.canonicalCombiningClass cp :=
    fullCanonicalDecompose_nonStarter_preserves_ccc cp hCCCNe
  have hCposMulti : ∀ c ∈ (Decompose.fullCanonicalDecompose cp).toList,
                      0 < Lookup.canonicalCombiningClass c :=
    fun c hc => (hCdecomp c hc).1
  have hYposMulti : ∀ y ∈ (Decompose.decomposeSequence buffer.reverse.toArray).toList,
                      0 < Lookup.canonicalCombiningClass y :=
    fun y hy => (hYdecomp y hy).1
  have hStrictMulti :
      ∀ c ∈ (Decompose.fullCanonicalDecompose cp).toList,
      ∀ y ∈ (Decompose.decomposeSequence buffer.reverse.toArray).toList,
        Lookup.canonicalCombiningClass y
          < Lookup.canonicalCombiningClass c := by
    intro c hc y hy
    have hCeq : Lookup.canonicalCombiningClass c
                  = Lookup.canonicalCombiningClass cp := (hCdecomp c hc).2
    have hYbound : Lookup.canonicalCombiningClass y ≤ maxCCC := (hYdecomp y hy).2
    have hCpAboveMax : maxCCC < Lookup.canonicalCombiningClass cp :=
      Nat.lt_of_not_le hStrict
    rw [hCeq]
    exact Nat.lt_of_le_of_lt hYbound hCpAboveMax
  -- Apply reorder_commutes_strict_max_multi with direction .symm.
  exact (ReorderAppend.reorder_commutes_strict_max_multi
           (Decompose.decomposeSequence (emitted ++ #[st]))
           (Decompose.decomposeSequence buffer.reverse.toArray)
           (Decompose.fullCanonicalDecompose cp)
           hCposMulti hYposMulti hStrictMulti).symm

-- ═══════════════════════════════════════════════════════════════════════════════
-- UNCONDITIONAL SPECIALIZATIONS
--
-- `reorderCommutesStrictMax_holds` discharges the single remaining
-- hypothesis in the `_given hRCSM` chain. Specializing the existing
-- conditional theorems with this discharge yields the unconditional
-- versions of StepPreservesNFDEquivalence, decompose_compose_inversion
-- (NFC idempotence pillar 2), toNFC_idempotent, and the NFD-NFC
-- cancellation identity.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **`StepPreservesNFDEquivalence` unconditional.** Every valid
    compose state preserves NFD-equivalence across `stepCompose`. -/
theorem stepPreservesNFDEquivalence_holds : StepPreservesNFDEquivalence :=
  stepPreservesNFDEquivalence_given_rcsm reorderCommutesStrictMax_holds

/-- **Decompose-compose inversion (NFC idempotence pillar 2),
    unconditional.** For any NFD-form input, applying `compose` and
    then `toNFD` returns the input unchanged. -/
theorem decompose_compose_inversion
    (x : Array Nat) (hx : NFC.toNFD x = x) :
    NFC.toNFD (Compose.compose x) = x :=
  decompose_compose_inversion_given stepPreservesNFDEquivalence_holds x hx

/-- **NFC idempotence, unconditional.** `toNFC (toNFC x) = toNFC x`
    for every codepoint sequence. -/
theorem toNFC_idempotent (x : Array Nat) :
    NFC.toNFC (NFC.toNFC x) = NFC.toNFC x :=
  toNFC_idempotent_given stepPreservesNFDEquivalence_holds x

/-- **NFD-NFC cancellation, unconditional.** `toNFD ∘ toNFC = toNFD`. -/
theorem toNFD_toNFC_eq_toNFD (x : Array Nat) :
    NFC.toNFD (NFC.toNFC x) = NFC.toNFD x :=
  toNFD_toNFC_eq_toNFD_given stepPreservesNFDEquivalence_holds x

end Unicode.Normalization.ComposeInversion
