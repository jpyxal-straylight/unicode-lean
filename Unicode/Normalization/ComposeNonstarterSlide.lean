/-
  Unicode.Normalization.ComposeNonstarterSlide

  Two structural primitives for the QC=Y non-starter slide of
  `Compose.compose`:

    * **Fact A** (`primary_chain_starter_only`) — folding a primary-
      firing chain over a state updates only the `starter` field;
      `emitted`, `buffer`, and `maxCCC` are preserved.
    * **Fact B** (`stepCompose_qcY_nonstarter_strictMax`) — a QC=Y
      non-starter with `ccc > maxCCC` arriving at any state with a
      `some` starter only appends to `buffer` and bumps `maxCCC`;
      `emitted` and `starter` are preserved (Fact 4 forces the
      strict-max branch's `none` case for QC=Y).

  These two facts compose at the snoc boundary to yield the slide
  `compose (X ++ #[cp] ++ B.toArray) = compose (X ++ B.toArray ++ #[cp])`,
  which is the substantive content for the non-starter snoc case of
  the master soundness theorem.
-/

import Unicode.Normalization.Compose
import Unicode.Normalization.QuickCheckSoundnessFact4

namespace Unicode.Normalization.ComposeNonstarterSlide

open Unicode.Normalization
open Unicode.Normalization.NFC (nfcQCValue)
open Unicode.Normalization.QuickCheckSoundnessFact4 (primaryComposite_none_of_qcY)

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1 PRIMARY-FIRING CHAIN PREDICATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A list `B` of non-starters primary-fires from state `s` when each
    successive element primary-composes with the running starter. The
    predicate is satisfied vacuously by the empty list and recursively
    by `head` firing followed by `rest` firing from the post-`head`
    state. -/
def PrimaryFiresChain : Compose.ComposeState → List Nat → Prop
  | _, []         => True
  | s, head :: rest =>
      ∃ st p, s.starter = some st ∧
              0 < Lookup.canonicalCombiningClass head ∧
              ¬ Lookup.canonicalCombiningClass head ≤ s.maxCCC ∧
              Compose.primaryComposite? st head = some p ∧
              PrimaryFiresChain { s with starter := some p } rest

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2 FACT A — CHAIN-FIRING UPDATES ONLY starter
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The strict-max + primary-fire branch of `stepCompose`: when the
    state has `starter = some st`, `cp` has `ccc > 0`, `ccc cp >
    maxCCC`, and `primaryComposite? st cp = some p`, the post-state
    is `{ s with starter := some p }`. -/
theorem stepCompose_primary_fire_form
    (s : Compose.ComposeState) (cp st p : Nat)
    (hSt : s.starter = some st)
    (hCccPos : 0 < Lookup.canonicalCombiningClass cp)
    (hMax : ¬ Lookup.canonicalCombiningClass cp ≤ s.maxCCC)
    (hPC : Compose.primaryComposite? st cp = some p) :
    Compose.stepCompose s cp = { s with starter := some p } := by
  have hCccNe : Lookup.canonicalCombiningClass cp ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hCccPos
  set_option linter.unusedSimpArgs false in
  unfold Compose.stepCompose
  simp only [hSt]
  rw [if_neg hCccNe, if_neg hMax, hPC]

/-- **Chain-firing preserves `emitted`, `buffer`, and `maxCCC`.** When
    `B` primary-fires from `s`, folding `stepCompose` over `B` updates
    only the `starter` field. -/
theorem primary_chain_starter_only
    (B : List Nat) (s : Compose.ComposeState)
    (hChain : PrimaryFiresChain s B) :
    (B.foldl Compose.stepCompose s).emitted = s.emitted ∧
    (B.foldl Compose.stepCompose s).buffer = s.buffer ∧
    (B.foldl Compose.stepCompose s).maxCCC = s.maxCCC := by
  induction B generalizing s with
  | nil =>
    refine ⟨rfl, rfl, rfl⟩
  | cons head rest ih =>
    obtain ⟨st, p, hSt, hCccPos, hMax, hPC, hRest⟩ := hChain
    simp only [List.foldl_cons]
    rw [stepCompose_primary_fire_form s head st p hSt hCccPos hMax hPC]
    exact ih { s with starter := some p } hRest

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3 FACT B — QC=Y NON-STARTER UPDATES ONLY buffer + maxCCC (STRICT-MAX BRANCH)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **QC=Y non-starter preserves `emitted` and `starter`.** When `cp`
    is a QC=Y non-starter arriving at a state with `starter = some _`,
    `stepCompose` produces a state with `buffer = cp :: s.buffer` and
    `maxCCC = max s.maxCCC (ccc cp)`, regardless of whether the input
    is in the blocked or strict-max branch. The two branches share
    output form: blocked directly produces it; strict-max with QC=Y
    routes through Fact 4's `primaryComposite? = none` exclusion. -/
theorem stepCompose_qcY_nonstarter_buffer_form
    (s : Compose.ComposeState) (cp st : Nat)
    (hSt : s.starter = some st)
    (hQC : nfcQCValue cp = .Y)
    (hCccPos : 0 < Lookup.canonicalCombiningClass cp) :
    Compose.stepCompose s cp =
      { s with
        buffer := cp :: s.buffer
        maxCCC := Nat.max s.maxCCC (Lookup.canonicalCombiningClass cp) } := by
  have hCccNe : Lookup.canonicalCombiningClass cp ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hCccPos
  set_option linter.unusedSimpArgs false in
  unfold Compose.stepCompose
  simp only [hSt]
  rw [if_neg hCccNe]
  by_cases hMax : Lookup.canonicalCombiningClass cp ≤ s.maxCCC
  · rw [if_pos hMax]
  · rw [if_neg hMax]
    rw [primaryComposite_none_of_qcY st cp hQC]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4 CHAIN-FINAL STARTER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The chain's final starter as a function of the initial starter
    and the list. Defined to match `stepCompose`'s primary-fire
    branch step-by-step. -/
def chainFinalStarter : Option Nat → List Nat → Option Nat
  | st, []         => st
  | none, _ :: _   => none
  | some st, head :: rest =>
      match Compose.primaryComposite? st head with
      | none   => none
      | some p => chainFinalStarter (some p) rest

/-- Under chain firing, the post-fold state's starter equals
    `chainFinalStarter` applied to the initial starter. -/
theorem chain_final_starter_eq
    (B : List Nat) (s : Compose.ComposeState)
    (hChain : PrimaryFiresChain s B) :
    (B.foldl Compose.stepCompose s).starter = chainFinalStarter s.starter B := by
  induction B generalizing s with
  | nil =>
    rfl
  | cons head rest ih =>
    obtain ⟨st, p, hSt, hCccPos, hMax, hPC, hRest⟩ := hChain
    simp only [List.foldl_cons]
    rw [stepCompose_primary_fire_form s head st p hSt hCccPos hMax hPC]
    have hRecur := ih { s with starter := some p } hRest
    rw [hRecur]
    show chainFinalStarter (some p) rest = chainFinalStarter s.starter (head :: rest)
    rw [hSt]
    show chainFinalStarter (some p) rest =
      match Compose.primaryComposite? st head with
      | none => none
      | some p' => chainFinalStarter (some p') rest
    rw [hPC]

/-- Under chain firing from a `some` starter, the chain's final
    starter is also `some`. The chain validity guarantees each step's
    `primaryComposite?` returns `some`, propagating through. -/
theorem chainFinalStarter_isSome_of_chain
    (B : List Nat) (st : Nat) (s : Compose.ComposeState)
    (hSt : s.starter = some st)
    (hChain : PrimaryFiresChain s B) :
    ∃ stFinal, chainFinalStarter (some st) B = some stFinal := by
  induction B generalizing st s with
  | nil =>
    exact ⟨st, rfl⟩
  | cons head rest ih =>
    obtain ⟨st1, p, hSt1, hCccPos, hMax, hPC, hRest⟩ := hChain
    have hSt1Eq : st = st1 := by
      rw [hSt] at hSt1
      exact ((Option.some.injEq st st1).mp hSt1)
    subst hSt1Eq
    show ∃ stFinal,
        (match Compose.primaryComposite? st head with
         | none => none
         | some p' => chainFinalStarter (some p') rest) = some stFinal
    rw [hPC]
    exact ih p ({ s with starter := some p } : Compose.ComposeState) rfl hRest

-- ═══════════════════════════════════════════════════════════════════════════════
-- §5 CHAIN TRANSFER FROM s TO cp-POST STATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The chain that fires from `s` also fires from the cp-post state
    `{ s with buffer := cp :: s.buffer, maxCCC := max s.maxCCC (ccc cp) }`,
    provided every chain element has `ccc > ccc cp`. The starter is
    unchanged across the cp step (Fact B), so the chain's primary
    firings produce the same final starter; the strict-max condition
    is preserved because chain elements have `ccc > ccc cp ≤ post-
    state's maxCCC`. -/
theorem chain_transfer_through_cp
    (B : List Nat) (s : Compose.ComposeState) (cp : Nat)
    (hHighGt : ∀ b ∈ B, Lookup.canonicalCombiningClass cp
                          < Lookup.canonicalCombiningClass b)
    (hChain : PrimaryFiresChain s B) :
    PrimaryFiresChain
      { s with
        buffer := cp :: s.buffer
        maxCCC := Nat.max s.maxCCC (Lookup.canonicalCombiningClass cp) } B := by
  induction B generalizing s with
  | nil =>
    trivial
  | cons head rest ih =>
    obtain ⟨st, p, hSt, hCccPos, hMax, hPC, hRest⟩ := hChain
    refine ⟨st, p, hSt, hCccPos, ?cpPostMax, hPC, ?cpPostRest⟩
    · -- Strict-max for `head` from cp-post state.
      show ¬ Lookup.canonicalCombiningClass head
            ≤ Nat.max s.maxCCC (Lookup.canonicalCombiningClass cp)
      have hHeadGtCp : Lookup.canonicalCombiningClass cp
                          < Lookup.canonicalCombiningClass head :=
        hHighGt head List.mem_cons_self
      have hHeadGtM : s.maxCCC < Lookup.canonicalCombiningClass head := by
        omega
      have hMaxLtHead :
          Nat.max s.maxCCC (Lookup.canonicalCombiningClass cp)
            < Lookup.canonicalCombiningClass head :=
        Nat.max_lt.mpr ⟨hHeadGtM, hHeadGtCp⟩
      intro hLe
      omega
    · -- Recursive call: chain from `{ ... with starter := some p }`,
      -- equivalent to chain from cp-post-of-`{ s with starter := some p }`.
      have hRestHigh : ∀ b ∈ rest, Lookup.canonicalCombiningClass cp
                          < Lookup.canonicalCombiningClass b :=
        fun b hb => hHighGt b (List.mem_cons.mpr (Or.inr hb))
      have hRecur := ih { s with starter := some p } hRestHigh hRest
      -- The post-cp state of `{ s with starter := some p }` is
      -- `{ s with starter := some p, buffer := cp :: s.buffer, maxCCC := ... }`,
      -- which matches the post-head state of cp-post: `{ cp-post with starter := some p }`.
      exact hRecur

-- ═══════════════════════════════════════════════════════════════════════════════
-- §6 STATE-LEVEL SLIDE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **State-level slide.** For QC=Y non-starter `cp` arriving at a
    state with `starter = some st`, followed by a primary-firing
    chain `B` whose elements all have `ccc > ccc cp`, the two
    processing orders (cp before B vs. cp after B) produce the same
    final state. -/
theorem slide_state_eq
    (s : Compose.ComposeState) (cp : Nat) (B : List Nat) (st : Nat)
    (hSt : s.starter = some st)
    (hQC : nfcQCValue cp = .Y)
    (hCccPos : 0 < Lookup.canonicalCombiningClass cp)
    (hHighGt : ∀ b ∈ B, Lookup.canonicalCombiningClass cp
                          < Lookup.canonicalCombiningClass b)
    (hChain : PrimaryFiresChain s B) :
    B.foldl Compose.stepCompose (Compose.stepCompose s cp) =
      Compose.stepCompose (B.foldl Compose.stepCompose s) cp := by
  -- LHS: process cp first → cp-post state. Then chain on cp-post.
  have hCpStep := stepCompose_qcY_nonstarter_buffer_form s cp st hSt hQC hCccPos
  have hChainCpPost : PrimaryFiresChain
      { s with
        buffer := cp :: s.buffer
        maxCCC := Nat.max s.maxCCC (Lookup.canonicalCombiningClass cp) } B :=
    chain_transfer_through_cp B s cp hHighGt hChain
  have hLhsChainState := primary_chain_starter_only B
        ({ s with
            buffer := cp :: s.buffer
            maxCCC := Nat.max s.maxCCC (Lookup.canonicalCombiningClass cp) })
        hChainCpPost
  have hLhsChainStarter := chain_final_starter_eq B
        ({ s with
            buffer := cp :: s.buffer
            maxCCC := Nat.max s.maxCCC (Lookup.canonicalCombiningClass cp) })
        hChainCpPost
  -- RHS: process chain on s, then cp on the chain-result.
  have hRhsChainState := primary_chain_starter_only B s hChain
  have hRhsChainStarter := chain_final_starter_eq B s hChain
  -- The post-chain state on RHS has `starter = chainFinalStarter
  -- s.starter B`, and the chain's final starter is the same on both
  -- sides because both chains start from `s.starter`.
  -- Show the post-chain RHS state's `starter` is `some _` so Fact B
  -- applies to the cp step.
  have hRhsStEqLhsSt :
      ({ s with
          buffer := cp :: s.buffer
          maxCCC := Nat.max s.maxCCC (Lookup.canonicalCombiningClass cp) }
        : Compose.ComposeState).starter = s.starter := rfl
  have hChainSameStarter :
      (B.foldl Compose.stepCompose
          ({ s with
              buffer := cp :: s.buffer
              maxCCC := Nat.max s.maxCCC
                          (Lookup.canonicalCombiningClass cp) }
            : Compose.ComposeState)).starter
        = (B.foldl Compose.stepCompose s).starter := by
    rw [hLhsChainStarter, hRhsChainStarter, hRhsStEqLhsSt]
  -- Extract the chain-final starter as `some stFinal`.
  -- From `hRhsChainStarter` and `hSt`: the final starter is
  -- `chainFinalStarter (some st) B`, which is `some _` by induction
  -- on B's chain validity.
  have hFinalStSome :
      ∃ stFinal, (B.foldl Compose.stepCompose s).starter = some stFinal := by
    rw [hRhsChainStarter, hSt]
    exact chainFinalStarter_isSome_of_chain B st s hSt hChain
  obtain ⟨stFinal, hFinalSt⟩ := hFinalStSome
  -- RHS: stepCompose at the post-chain state with starter = some stFinal.
  have hRhsMxAtChain : (B.foldl Compose.stepCompose s).maxCCC = s.maxCCC :=
    hRhsChainState.2.2
  have hRhsStepCp := stepCompose_qcY_nonstarter_buffer_form
        (B.foldl Compose.stepCompose s) cp stFinal hFinalSt hQC hCccPos
  -- Both final states are structurally identical record updates of `s`.
  -- Rewrite the goal so both sides expose the same four fields.
  rw [hCpStep, hRhsStepCp]
  -- LHS = B.foldl stepCompose cp-post-state
  -- RHS = { B.foldl stepCompose s with buffer := ..., maxCCC := ... }
  -- Destructure each fold result; then use the chain characterizations
  -- to substitute the field equalities and close with `rfl`.
  have hLhsCharStar :
      (B.foldl Compose.stepCompose
          ({ s with
              buffer := cp :: s.buffer
              maxCCC := Nat.max s.maxCCC (Lookup.canonicalCombiningClass cp) }
            : Compose.ComposeState)).starter = (B.foldl Compose.stepCompose s).starter := by
    rw [hLhsChainStarter, hRhsChainStarter]
  obtain ⟨hLhsEm, hLhsBuf, hLhsMx⟩ := hLhsChainState
  obtain ⟨hRhsEm, hRhsBuf, hRhsMx⟩ := hRhsChainState
  cases hLhsFold :
      B.foldl Compose.stepCompose
          ({ s with
              buffer := cp :: s.buffer
              maxCCC := Nat.max s.maxCCC (Lookup.canonicalCombiningClass cp) }
            : Compose.ComposeState) with
  | mk emL opStL bufL mxL =>
    cases hRhsFold : B.foldl Compose.stepCompose s with
    | mk emR opStR bufR mxR =>
      rw [hLhsFold] at hLhsEm hLhsBuf hLhsMx hLhsCharStar
      rw [hRhsFold] at hLhsCharStar hRhsEm hRhsBuf hRhsMx
      simp only at hLhsEm hLhsBuf hLhsMx hLhsCharStar hRhsEm hRhsBuf hRhsMx
      subst hLhsEm hLhsBuf hLhsMx hLhsCharStar hRhsEm hRhsBuf hRhsMx
      rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- §7 COMPOSE-LEVEL SLIDE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Compose-level slide.** A QC=Y non-starter `cp` may be moved
    past a primary-firing chain `B` without changing `compose`'s
    output:

        compose (X ++ #[cp] ++ B.toArray) = compose (X ++ B.toArray ++ #[cp]).

    Lifts `slide_state_eq` through `flushCompose`. The state-level
    equality of folds carries to the flushed outputs because
    `flushCompose` is a function of the post-fold state. -/
theorem compose_slide_qcY
    (X : Array Nat) (cp : Nat) (B : List Nat) (st : Nat)
    (hSt : (X.foldl Compose.stepCompose Compose.initialState).starter = some st)
    (hQC : nfcQCValue cp = .Y)
    (hCccPos : 0 < Lookup.canonicalCombiningClass cp)
    (hHighGt : ∀ b ∈ B, Lookup.canonicalCombiningClass cp
                          < Lookup.canonicalCombiningClass b)
    (hChain : PrimaryFiresChain
                (X.foldl Compose.stepCompose Compose.initialState) B) :
    Compose.compose (X ++ #[cp] ++ B.toArray) =
      Compose.compose (X ++ B.toArray ++ #[cp]) := by
  unfold Compose.compose
  -- Reduce both sides to `flushCompose ∘ (cp-or-chain dispatch over s_X)`.
  rw [Array.foldl_append, Array.foldl_append]
  rw [Array.foldl_append, Array.foldl_append]
  -- LHS: flushCompose (B.toArray.foldl stepCompose
  --        (#[cp].foldl stepCompose s_X))
  -- RHS: flushCompose (#[cp].foldl stepCompose
  --        (B.toArray.foldl stepCompose s_X))
  -- Convert array-foldl to list-foldl on B and singleton on #[cp].
  have hCpStep :
      ∀ s, (#[cp] : Array Nat).foldl Compose.stepCompose s
            = Compose.stepCompose s cp := by
    intro s
    show ([cp] : List Nat).foldl Compose.stepCompose s
       = Compose.stepCompose s cp
    simp only [List.foldl_cons, List.foldl_nil]
  rw [hCpStep, hCpStep]
  have hConvert1 :
      B.toArray.foldl Compose.stepCompose
          (Compose.stepCompose
            (X.foldl Compose.stepCompose Compose.initialState) cp)
        = B.foldl Compose.stepCompose
            (Compose.stepCompose
              (X.foldl Compose.stepCompose Compose.initialState) cp) := by
    rw [← Array.foldl_toList, List.toList_toArray]
  have hConvert2 :
      B.toArray.foldl Compose.stepCompose
          (X.foldl Compose.stepCompose Compose.initialState)
        = B.foldl Compose.stepCompose
            (X.foldl Compose.stepCompose Compose.initialState) := by
    rw [← Array.foldl_toList, List.toList_toArray]
  rw [hConvert1, hConvert2]
  rw [slide_state_eq (X.foldl Compose.stepCompose Compose.initialState)
        cp B st hSt hQC hCccPos hHighGt hChain]

end Unicode.Normalization.ComposeNonstarterSlide
