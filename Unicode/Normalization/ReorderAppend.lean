/-
  Unicode.Normalization.ReorderAppend

  Starter-boundary partition lemmas for `reorder`. Two central results:

  * `reorder_append_starter` — tail version:
        reorder (X ++ #[cp]) = reorder X ++ #[cp]    when ccc(cp) = 0

  * `reorder_append_starter_middle` — interior version:
        reorder (X ++ #[cp] ++ Y) = reorder X ++ #[cp] ++ reorder Y
                                    when ccc(cp) = 0

  The interior version partitions the input at an interior starter:
  no non-starter run spans the starter boundary, so `reorder` operates
  independently on the two halves.

  Proof machinery: a state-prefix additivity lemma
  (`foldl_list_stepReorder_emitted_add`) shows that folding `stepReorder`
  over any sequence from a state with arbitrary `emitted` prefix `Z` and
  empty `currentRun` yields the output `Z ++ reorder Y` — the `Z` prefix
  passes through untouched. Combined with the shape of `stepReorder` on
  a starter (which flushes `currentRun` and resets it to `[]`), this
  gives both absorbing lemmas.

  These lemmas lift to `toNFD`: for any starter `cp`, the
  `fullCanonicalDecompose cp` starts with a starter, so
  `toNFD (X ++ #[cp]) = toNFD X ++ toNFD #[cp]`. This closes the Case 1
  branch (leading-starter absorb) of `StepPreservesNFDEquivalence` in
  `ComposeInversion`.
-/

import Unicode.Normalization.Reorder

namespace Unicode.Normalization.ReorderAppend

open Unicode.Normalization.Reorder

/-- Unfold `sortNonStarterRun` on the empty list. -/
theorem sortNonStarterRun_nil : sortNonStarterRun [] = [] := by
  unfold sortNonStarterRun
  simp

/-- `flushRun` on a state with empty `currentRun` is the empty array. -/
theorem flushRun_empty_run
    (s : ReorderState) (h : s.currentRun = []) :
    flushRun s = #[] := by
  unfold flushRun
  rw [h]
  simp [sortNonStarterRun_nil]

/-- Specialization of `flushRun_empty_run` for an explicitly-constructed
    state with `currentRun := []`. Saves the need to thread the witness
    through `stepReorder` rewrites at a starter. -/
theorem flushRun_emptyRun_ctor (e : Array Nat) :
    flushRun { emitted := e, currentRun := [] } = #[] :=
  flushRun_empty_run { emitted := e, currentRun := [] } rfl

/-- Shape of `stepReorder` on a starter. -/
theorem stepReorder_starter_output
    (s : ReorderState) (cp : Nat)
    (h : Lookup.canonicalCombiningClass cp = 0) :
    stepReorder s cp
      = { emitted := s.emitted ++ flushRun s ++ #[cp], currentRun := [] } := by
  unfold stepReorder
  rw [if_pos h]

/-- Explicit `reorder` equation without the internal `let` binding. Lets
    downstream rewrites reach inside `reorder` calls. -/
theorem reorder_eq (Y : Array Nat) :
    reorder Y = (Y.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
                ++ flushRun (Y.foldl stepReorder { emitted := #[], currentRun := [] }) := rfl

/-- **Starter-append absorbing lemma.** Appending a starter codepoint to
    the input of `reorder` is the same as appending it to the reordered
    output. -/
theorem reorder_append_starter
    (X : Array Nat) (cp : Nat)
    (h : Lookup.canonicalCombiningClass cp = 0) :
    reorder (X ++ #[cp]) = reorder X ++ #[cp] := by
  rw [reorder_eq (X ++ #[cp]), reorder_eq X]
  rw [Array.foldl_append]
  have hStep :
      (#[cp] : Array Nat).foldl stepReorder
        (X.foldl stepReorder { emitted := #[], currentRun := [] })
      = stepReorder (X.foldl stepReorder { emitted := #[], currentRun := [] }) cp := by
    simp
  rw [hStep]
  rw [stepReorder_starter_output (X.foldl stepReorder { emitted := #[], currentRun := [] }) cp h]
  rw [flushRun_emptyRun_ctor]
  simp

-- ═══════════════════════════════════════════════════════════════════════════════
-- STARTER-MIDDLE PARTITION
--
-- `reorder` partitions at any interior starter. Specifically, for a starter
-- codepoint `cp` (ccc = 0) and any arrays `X`, `Y`:
--
--     reorder (X ++ #[cp] ++ Y) = reorder X ++ #[cp] ++ reorder Y
--
-- Intuitively: the starter `cp` forces a flush of the pending run when
-- encountered, and the subsequent processing of `Y` starts from an
-- empty `currentRun`. The final output concatenates `reorder X`, the
-- starter, and `reorder Y` — no non-starter run spans the starter
-- boundary.
--
-- Proof uses a state-prefix additivity lemma: processing an array `Y`
-- from a state with arbitrary `emitted` prefix `Z` and empty
-- `currentRun` yields the same output shape as processing `Y` from
-- the initial state, plus the `Z` prefix.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `flushRun` depends only on `currentRun`, not on `emitted`. -/
theorem flushRun_ignores_emitted (e1 e2 : Array Nat) (R : List Nat) :
    flushRun { emitted := e1, currentRun := R }
      = flushRun { emitted := e2, currentRun := R } := by
  unfold flushRun
  rfl

/-- `stepReorder` on a non-starter has an explicit output shape —
    `emitted` unchanged, `currentRun` gains the codepoint as its new
    head. -/
theorem stepReorder_nonstarter_output
    (s : ReorderState) (cp : Nat)
    (h : Lookup.canonicalCombiningClass cp ≠ 0) :
    stepReorder s cp = { emitted := s.emitted, currentRun := cp :: s.currentRun } := by
  unfold stepReorder
  rw [if_neg h]

/-- `stepReorder` on either starter or non-starter branch produces a state
    whose `emitted` delta is independent of the incoming `emitted`. The
    incoming `emitted` acts purely as a prefix that passes through. -/
theorem foldl_list_stepReorder_emitted_add
    (Y : List Nat) (Z : Array Nat) (R : List Nat) :
    (Y.foldl stepReorder { emitted := Z, currentRun := R }).emitted
      = Z ++ ((Y.foldl stepReorder { emitted := #[], currentRun := R }).emitted) := by
  induction Y generalizing Z R with
  | nil => simp
  | cons cp Y' ih =>
    simp only [List.foldl_cons]
    by_cases h : Lookup.canonicalCombiningClass cp = 0
    · rw [stepReorder_starter_output { emitted := Z, currentRun := R } cp h]
      rw [stepReorder_starter_output { emitted := #[], currentRun := R } cp h]
      rw [ih (Z ++ flushRun { emitted := Z, currentRun := R } ++ #[cp]) []]
      rw [ih (#[] ++ flushRun { emitted := #[], currentRun := R } ++ #[cp]) []]
      rw [flushRun_ignores_emitted Z #[] R]
      simp [Array.append_assoc]
    · rw [stepReorder_nonstarter_output { emitted := Z, currentRun := R } cp h]
      rw [stepReorder_nonstarter_output { emitted := #[], currentRun := R } cp h]
      exact ih Z (cp :: R)

/-- Dual of emitted-additivity: the final `currentRun` is independent of
    the starting `emitted`. -/
theorem foldl_list_stepReorder_currentRun_eq
    (Y : List Nat) (Z : Array Nat) (R : List Nat) :
    (Y.foldl stepReorder { emitted := Z, currentRun := R }).currentRun
      = (Y.foldl stepReorder { emitted := #[], currentRun := R }).currentRun := by
  induction Y generalizing Z R with
  | nil => rfl
  | cons cp Y' ih =>
    simp only [List.foldl_cons]
    by_cases h : Lookup.canonicalCombiningClass cp = 0
    · rw [stepReorder_starter_output { emitted := Z, currentRun := R } cp h]
      rw [stepReorder_starter_output { emitted := #[], currentRun := R } cp h]
      rw [ih (Z ++ flushRun { emitted := Z, currentRun := R } ++ #[cp]) []]
      rw [ih (#[] ++ flushRun { emitted := #[], currentRun := R } ++ #[cp]) []]
    · rw [stepReorder_nonstarter_output { emitted := Z, currentRun := R } cp h]
      rw [stepReorder_nonstarter_output { emitted := #[], currentRun := R } cp h]
      exact ih Z (cp :: R)

/-- Processing `Y` from state `(emitted := Z, currentRun := [])` yields
    the output `Z ++ reorder Y`. Key consequence of emitted-additivity
    and currentRun-independence: the starting `Z` prefix passes through
    untouched to the final output. -/
theorem reorder_with_prefixed_state (Y : Array Nat) (Z : Array Nat) :
    (Y.foldl stepReorder { emitted := Z, currentRun := ([] : List Nat) }).emitted
      ++ flushRun (Y.foldl stepReorder { emitted := Z, currentRun := ([] : List Nat) })
      = Z ++ reorder Y := by
  rw [← Array.foldl_toList]
  rw [foldl_list_stepReorder_emitted_add Y.toList Z []]
  have hFlush :
      flushRun (Y.toList.foldl stepReorder { emitted := Z, currentRun := [] })
        = flushRun (Y.toList.foldl stepReorder { emitted := #[], currentRun := [] }) := by
    unfold flushRun
    rw [foldl_list_stepReorder_currentRun_eq Y.toList Z []]
  rw [hFlush]
  rw [reorder_eq Y]
  rw [← Array.foldl_toList]
  simp [Array.append_assoc]

/-- **Starter-middle partition.** `reorder` commutes with any starter
    codepoint sitting between two arbitrary arrays: the reordered
    output is the concatenation of `reorder X`, the starter, and
    `reorder Y`. -/
theorem reorder_append_starter_middle
    (X : Array Nat) (cp : Nat) (Y : Array Nat)
    (h : Lookup.canonicalCombiningClass cp = 0) :
    reorder (X ++ #[cp] ++ Y) = reorder X ++ #[cp] ++ reorder Y := by
  rw [reorder_eq (X ++ #[cp] ++ Y)]
  rw [Array.foldl_append]
  rw [Array.foldl_append]
  have hStepCp :
      (#[cp] : Array Nat).foldl stepReorder
        (X.foldl stepReorder { emitted := #[], currentRun := [] })
      = stepReorder (X.foldl stepReorder { emitted := #[], currentRun := [] }) cp := by
    simp
  rw [hStepCp]
  rw [stepReorder_starter_output
        (X.foldl stepReorder { emitted := #[], currentRun := [] }) cp h]
  rw [reorder_with_prefixed_state Y
        ((X.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
          ++ flushRun (X.foldl stepReorder { emitted := #[], currentRun := [] })
          ++ #[cp])]
  rw [← reorder_eq X]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SORTNONSTARTERRUN IDEMPOTENCE + APPEND-ABSORBING
--
-- Stable-sort primitives on a single non-starter run. Foundation for
-- lifting `reorder_append_starter_middle` to the non-starter-append
-- version of absorbing — specifically, the key identity
--
--     sortNonStarterRun (L ++ [x]) = sortNonStarterRun (sortNonStarterRun L ++ [x])
--
-- which says: pre-sorting the run before inserting the next element
-- produces the same stably-sorted output as inserting into the
-- unsorted run. Equivalent to stable-sort being a canonical form: the
-- sort output depends only on the multiset + relative order of equal-
-- key items, both of which `sortNonStarterRun` preserves.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `sortNonStarterRun` is the identity on a CCC-sorted input. Direct
    instance of `insertByCCC_foldl_append` with an empty prefix: folding
    `insertByCCC` over a sorted list returns the list unchanged. -/
theorem sortNonStarterRun_id_on_sorted
    (L : List Nat) (h : IsCCCSorted L) :
    sortNonStarterRun L = L := by
  unfold sortNonStarterRun
  have hEmpty : IsCCCSorted ([] : List Nat) := by trivial
  have hBridge : IsCCCSorted ([] ++ L) := by simpa using h
  have := insertByCCC_foldl_append [] L hEmpty hBridge
  simpa using this

/-- `sortNonStarterRun` is idempotent. Combines `sortNonStarterRun_sorted`
    (output is sorted) with `sortNonStarterRun_id_on_sorted` (identity on
    sorted inputs). -/
theorem sortNonStarterRun_idempotent (L : List Nat) :
    sortNonStarterRun (sortNonStarterRun L) = sortNonStarterRun L :=
  sortNonStarterRun_id_on_sorted
    (sortNonStarterRun L)
    (sortNonStarterRun_sorted L)

/-- **Append-absorbing.** Inserting `x` into an unsorted run's sort gives
    the same stably-sorted result as inserting `x` into the pre-sorted
    run. Foundation for the non-starter-append version of
    `reorder_absorbing_left`. -/
theorem sortNonStarterRun_append_absorbing (L : List Nat) (x : Nat) :
    sortNonStarterRun (L ++ [x])
      = sortNonStarterRun (sortNonStarterRun L ++ [x]) := by
  show (L ++ [x]).foldl (fun acc cp => insertByCCC cp acc) []
     = (sortNonStarterRun L ++ [x]).foldl (fun acc cp => insertByCCC cp acc) []
  rw [List.foldl_append, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hLFold : L.foldl (fun acc cp => insertByCCC cp acc) []
              = sortNonStarterRun L := rfl
  have hSLFold : (sortNonStarterRun L).foldl (fun acc cp => insertByCCC cp acc) []
               = sortNonStarterRun (sortNonStarterRun L) := rfl
  rw [hLFold, hSLFold, sortNonStarterRun_idempotent]

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRICT-MAX ELEMENT SORTING
--
-- Foundational stability lemmas for Case 7 of `StepPreservesNFDEquivalence`
-- (primary-composite absorb of a non-starter with `ccc > maxCCC buffer`):
-- a stable sort places a strict-max-CCC element at the end of the sorted
-- run regardless of its input position. Concretely:
--
--     sortNonStarterRun (cp :: Y) = sortNonStarterRun Y ++ [cp]
--     sortNonStarterRun (Y ++ [cp]) = sortNonStarterRun Y ++ [cp]
--
-- when every `y ∈ Y` has `ccc y < ccc cp`. Both derive from the
-- inductive stepping lemma `insertByCCC_append_max` — inserting a
-- lower-CCC element into a list already containing a strict-max cp
-- preserves cp's trailing position.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Inserting a lower-CCC element `y` into a list ending with a
    strict-max-CCC element `cp` preserves `cp`'s tail position: the
    insertion lands somewhere in the prefix. -/
theorem insertByCCC_append_max
    (y : Nat) (L : List Nat) (cp : Nat)
    (h : Lookup.canonicalCombiningClass y
           < Lookup.canonicalCombiningClass cp) :
    insertByCCC y (L ++ [cp]) = insertByCCC y L ++ [cp] := by
  induction L with
  | nil =>
    show insertByCCC y [cp] = [y] ++ [cp]
    unfold insertByCCC
    rw [if_pos h]
    rfl
  | cons z L' ih =>
    -- Normalize (z :: L') ++ [cp] = z :: (L' ++ [cp]) on both sides.
    have hStep : ∀ (xs : List Nat),
        insertByCCC y (z :: xs)
          = if Lookup.canonicalCombiningClass y
                 < Lookup.canonicalCombiningClass z
              then y :: z :: xs
              else z :: insertByCCC y xs := by
      intro xs
      rfl
    have hConsAppend : (z :: L') ++ [cp] = z :: (L' ++ [cp]) := rfl
    rw [hConsAppend]
    rw [hStep (L' ++ [cp]), hStep L']
    by_cases hYZ : Lookup.canonicalCombiningClass y
                     < Lookup.canonicalCombiningClass z
    · rw [if_pos hYZ, if_pos hYZ]
      rfl
    · rw [if_neg hYZ, if_neg hYZ, ih]
      rfl

/-- Folding `insertByCCC` over a list whose elements all have CCC
    strictly less than `cp`'s CCC preserves `cp`'s position at the end
    of the accumulator. Used to lift `insertByCCC_append_max` through a
    sequence of insertions. -/
theorem foldl_insertByCCC_append_max
    (Y : List Nat) (cp : Nat) (acc : List Nat)
    (h : ∀ y ∈ Y,
           Lookup.canonicalCombiningClass y
             < Lookup.canonicalCombiningClass cp) :
    Y.foldl (fun a x => insertByCCC x a) (acc ++ [cp])
      = Y.foldl (fun a x => insertByCCC x a) acc ++ [cp] := by
  induction Y generalizing acc with
  | nil => rfl
  | cons y Y' ih =>
    simp only [List.foldl_cons]
    have hY : Lookup.canonicalCombiningClass y
                < Lookup.canonicalCombiningClass cp := h y (by simp)
    rw [insertByCCC_append_max y acc cp hY]
    have hTl : ∀ z ∈ Y',
                 Lookup.canonicalCombiningClass z
                   < Lookup.canonicalCombiningClass cp :=
      fun z hz => h z (by simp [hz])
    exact ih (insertByCCC y acc) hTl

/-- **Strict-max append.** Stable-sorting a run with a strict-max-CCC
    element at the end places it at the tail of the sorted output. -/
theorem sortNonStarterRun_append_max
    (Y : List Nat) (cp : Nat)
    (h : ∀ y ∈ Y,
           Lookup.canonicalCombiningClass y
             < Lookup.canonicalCombiningClass cp) :
    sortNonStarterRun (Y ++ [cp]) = sortNonStarterRun Y ++ [cp] := by
  show (Y ++ [cp]).foldl (fun a x => insertByCCC x a) []
     = sortNonStarterRun Y ++ [cp]
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hYFold : Y.foldl (fun a x => insertByCCC x a) [] = sortNonStarterRun Y := rfl
  rw [hYFold]
  apply insertByCCC_append_of_all_le
  intro z hz
  have hPreserve :
      ∀ w ∈ Y,
        (fun n => decide (Lookup.canonicalCombiningClass n
                            ≤ Lookup.canonicalCombiningClass cp)) w = true := by
    intro w hw
    exact decide_eq_true (Nat.le_of_lt (h w hw))
  have hBool := sortNonStarterRun_preserves_all
    (fun n => decide (Lookup.canonicalCombiningClass n
                        ≤ Lookup.canonicalCombiningClass cp))
    Y hPreserve z hz
  exact of_decide_eq_true hBool

/-- **Strict-max prepend.** Stable-sorting a run with a strict-max-CCC
    element at the front also places it at the tail of the sorted
    output. Combined with `sortNonStarterRun_append_max`, this gives
    the commutativity needed for Case 7 of
    `StepPreservesNFDEquivalence`. -/
theorem sortNonStarterRun_cons_max
    (Y : List Nat) (cp : Nat)
    (h : ∀ y ∈ Y,
           Lookup.canonicalCombiningClass y
             < Lookup.canonicalCombiningClass cp) :
    sortNonStarterRun (cp :: Y) = sortNonStarterRun Y ++ [cp] := by
  show (cp :: Y).foldl (fun a x => insertByCCC x a) []
     = sortNonStarterRun Y ++ [cp]
  simp only [List.foldl_cons]
  have hCp : insertByCCC cp [] = [cp] := rfl
  rw [hCp]
  have hEmptyAppend : [cp] = ([] : List Nat) ++ [cp] := by simp
  rw [hEmptyAppend]
  rw [foldl_insertByCCC_append_max Y cp [] h]
  rfl

/-- **Strict-max prepend equals strict-max append.** Direct consequence
    of `sortNonStarterRun_cons_max` + `sortNonStarterRun_append_max`. -/
theorem sortNonStarterRun_cons_eq_append_max
    (Y : List Nat) (cp : Nat)
    (h : ∀ y ∈ Y,
           Lookup.canonicalCombiningClass y
             < Lookup.canonicalCombiningClass cp) :
    sortNonStarterRun (cp :: Y) = sortNonStarterRun (Y ++ [cp]) := by
  rw [sortNonStarterRun_cons_max Y cp h]
  rw [sortNonStarterRun_append_max Y cp h]

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRICT-LESS INSERTBYCCC COMMUTATIVITY + CONTEXT-AWARE SORT SWAP
--
-- Foundation for `ReorderCommutesStrictMax`: when two codepoints `x`,
-- `cp` have strictly different CCCs (say `ccc x < ccc cp`), the two
-- `insertByCCC` operations commute at every point in the list. Lifts
-- through a fold over a sequence `Y` with every element strict-less
-- than `cp`, giving that `insertByCCC cp` commutes with that fold.
--
-- Context-aware swap: for any prefix `R` and non-starter run `Y` with
-- every element of `Y` strict-less than `cp`,
--     sortNonStarterRun (R ++ Y ++ [cp]) = sortNonStarterRun (R ++ cp :: Y)
-- — cp can slide across Y without changing the stably-sorted output.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Helper: insertByCCC on a list of length 2 where the head has
    strictly-less CCC puts the new element after the head. -/
theorem insertByCCC_cons_ge (x y : Nat) (ys : List Nat)
    (h : ¬ Lookup.canonicalCombiningClass x
            < Lookup.canonicalCombiningClass y) :
    insertByCCC x (y :: ys) = y :: insertByCCC x ys := by
  rw [insertByCCC_cons, if_neg h]

/-- Helper: insertByCCC on a cons where the new element has
    strictly-less CCC than the head places it at the front. -/
theorem insertByCCC_cons_lt (x y : Nat) (ys : List Nat)
    (h : Lookup.canonicalCombiningClass x
           < Lookup.canonicalCombiningClass y) :
    insertByCCC x (y :: ys) = x :: y :: ys := by
  rw [insertByCCC_cons, if_pos h]

/-- `insertByCCC` on the empty list is a singleton. -/
theorem insertByCCC_nil (x : Nat) :
    insertByCCC x [] = [x] := rfl

/-- Single-step strict-less commutativity: `insertByCCC x` and
    `insertByCCC cp` commute at any position when `ccc x < ccc cp`. -/
theorem insertByCCC_comm_strict_lt
    (L : List Nat) (x cp : Nat)
    (h : Lookup.canonicalCombiningClass x
           < Lookup.canonicalCombiningClass cp) :
    insertByCCC cp (insertByCCC x L) = insertByCCC x (insertByCCC cp L) := by
  have hXcp : ¬ (Lookup.canonicalCombiningClass cp
                  < Lookup.canonicalCombiningClass x) := by omega
  induction L with
  | nil =>
    -- LHS: insertByCCC cp [x] = x :: insertByCCC cp [] = [x, cp]
    -- RHS: insertByCCC x [cp] = [x, cp]
    rw [insertByCCC_nil, insertByCCC_cons_ge cp x [] hXcp,
        insertByCCC_nil, insertByCCC_cons_lt x cp [] h]
  | cons z L' ih =>
    by_cases hXZ : Lookup.canonicalCombiningClass x
                     < Lookup.canonicalCombiningClass z
    · by_cases hCpZ : Lookup.canonicalCombiningClass cp
                       < Lookup.canonicalCombiningClass z
      · -- ccc x < ccc z, ccc cp < ccc z. Both go before z.
        -- LHS: cp (x (z L')) = cp (x::z::L') = x::cp (z::L') = x::cp::z::L'
        -- RHS: x (cp (z::L')) = x (cp::z::L') = x::cp::z::L'
        rw [insertByCCC_cons_lt x z L' hXZ,
            insertByCCC_cons_ge cp x (z :: L') hXcp,
            insertByCCC_cons_lt cp z L' hCpZ,
            insertByCCC_cons_lt x cp (z :: L') h]
      · -- ccc x < ccc z, ccc cp ≥ ccc z.
        -- LHS: cp (x::z::L') = x :: cp (z::L') = x :: z :: cp L'
        -- RHS: x (z :: cp L') = x :: z :: cp L'
        rw [insertByCCC_cons_lt x z L' hXZ,
            insertByCCC_cons_ge cp x (z :: L') hXcp,
            insertByCCC_cons_ge cp z L' hCpZ,
            insertByCCC_cons_lt x z (insertByCCC cp L') hXZ]
    · -- ccc x ≥ ccc z. Then ccc cp > ccc x ≥ ccc z, so ccc cp ≥ ccc z too.
      have hCpZ : ¬ (Lookup.canonicalCombiningClass cp
                      < Lookup.canonicalCombiningClass z) := by
        intro hCp
        have : Lookup.canonicalCombiningClass x
                 < Lookup.canonicalCombiningClass z := by omega
        exact hXZ this
      -- LHS: cp (z :: x L') = z :: cp (x L')
      -- RHS: x (z :: cp L') = z :: x (cp L')
      -- Equal by IH.
      rw [insertByCCC_cons_ge x z L' hXZ,
          insertByCCC_cons_ge cp z (insertByCCC x L') hCpZ,
          insertByCCC_cons_ge cp z L' hCpZ,
          insertByCCC_cons_ge x z (insertByCCC cp L') hXZ,
          ih]

/-- Fold-level strict-less commutativity: `insertByCCC cp` commutes
    with any foldl of `insertByCCC` over a list `Y` whose elements are
    all strict-less than `cp` in CCC. -/
theorem foldl_insertByCCC_comm_strict_lt
    (Y : List Nat) (cp : Nat) (L : List Nat)
    (hY : ∀ y ∈ Y,
            Lookup.canonicalCombiningClass y
              < Lookup.canonicalCombiningClass cp) :
    insertByCCC cp (Y.foldl (fun acc y => insertByCCC y acc) L)
      = Y.foldl (fun acc y => insertByCCC y acc) (insertByCCC cp L) := by
  induction Y generalizing L with
  | nil => rfl
  | cons y Y' ih =>
    simp only [List.foldl_cons]
    have hY' : ∀ z ∈ Y',
                 Lookup.canonicalCombiningClass z
                   < Lookup.canonicalCombiningClass cp :=
      fun z hz => hY z (by simp [hz])
    have hYhd : Lookup.canonicalCombiningClass y
                  < Lookup.canonicalCombiningClass cp := hY y (by simp)
    rw [ih (insertByCCC y L) hY']
    rw [insertByCCC_comm_strict_lt L y cp hYhd]

/-- **Context-aware strict-max sort swap.** For any prefix `R` and
    non-starter run `Y` with every element strict-less than `cp` in
    CCC, sorting the concatenated list is invariant under moving `cp`
    from the tail to just before `Y`. -/
theorem sortNonStarterRun_append_cons_swap_max
    (R Y : List Nat) (cp : Nat)
    (hY : ∀ y ∈ Y,
            Lookup.canonicalCombiningClass y
              < Lookup.canonicalCombiningClass cp) :
    sortNonStarterRun (R ++ Y ++ [cp])
      = sortNonStarterRun (R ++ cp :: Y) := by
  -- Derive each side's normalized form explicitly.
  have hRFold : R.foldl (fun acc y => insertByCCC y acc) []
              = sortNonStarterRun R := rfl
  have hLHS : sortNonStarterRun (R ++ Y ++ [cp])
            = insertByCCC cp (Y.foldl (fun acc y => insertByCCC y acc)
                                      (sortNonStarterRun R)) := by
    show (R ++ Y ++ [cp]).foldl (fun acc y => insertByCCC y acc) []
       = insertByCCC cp (Y.foldl (fun acc y => insertByCCC y acc)
                                 (sortNonStarterRun R))
    rw [List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hRFold]
  have hRHS : sortNonStarterRun (R ++ cp :: Y)
            = Y.foldl (fun acc y => insertByCCC y acc)
                      (insertByCCC cp (sortNonStarterRun R)) := by
    show (R ++ cp :: Y).foldl (fun acc y => insertByCCC y acc) []
       = Y.foldl (fun acc y => insertByCCC y acc)
                 (insertByCCC cp (sortNonStarterRun R))
    rw [List.foldl_append]
    simp only [List.foldl_cons]
    rw [hRFold]
  rw [hLHS, hRHS]
  exact foldl_insertByCCC_comm_strict_lt Y cp (sortNonStarterRun R) hY

-- ═══════════════════════════════════════════════════════════════════════════════
-- FOLD CHARACTERIZATION ON SPECIAL-SHAPED INPUTS
--
-- Two structural lemmas about `stepReorder`-folding behavior:
--
--   1. Processing a `HasSortedRuns` sequence that ends with a starter
--      (or is empty) from `initState` yields state `(sequence, [])`.
--      The trailing starter forces `currentRun` to `[]`.
--
--   2. Processing a sequence of only non-starters from state
--      `(E, R)` yields `(E, reversed-non-starters ++ R)` — each step
--      just prepends its codepoint to `currentRun` with no side effects
--      on `emitted`.
--
-- Together they characterize `state(reorder A)` given `state(A)`,
-- which combined with `sortNonStarterRun_append_absorbing` closes the
-- non-starter single-element case of `reorder_absorbing_left`.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Processing a sequence of only non-starters from state `(E, R)`
    prepends each codepoint to `currentRun` (in reverse). -/
theorem fold_nonstarters_from_state
    (L : List Nat)
    (hNonStarter : ∀ x ∈ L, 0 < Lookup.canonicalCombiningClass x)
    (E : Array Nat) (R : List Nat) :
    L.foldl stepReorder { emitted := E, currentRun := R }
      = { emitted := E, currentRun := L.reverse ++ R } := by
  induction L generalizing R with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hHdPos : 0 < Lookup.canonicalCombiningClass hd := hNonStarter hd (by simp)
    have hHdNe : Lookup.canonicalCombiningClass hd ≠ 0 := Nat.pos_iff_ne_zero.mp hHdPos
    have hStep : stepReorder { emitted := E, currentRun := R } hd
               = { emitted := E, currentRun := hd :: R } := by
      unfold stepReorder
      rw [if_neg hHdNe]
    rw [hStep]
    have hTlNS : ∀ x ∈ tl, 0 < Lookup.canonicalCombiningClass x :=
      fun x hx => hNonStarter x (List.mem_cons_of_mem hd hx)
    rw [ih hTlNS (hd :: R)]
    show (⟨E, tl.reverse ++ hd :: R⟩ : ReorderState)
       = ⟨E, (hd :: tl).reverse ++ R⟩
    rw [List.reverse_cons, List.append_assoc]
    rfl

/-- Processing a `HasSortedRuns` sequence that ends with a starter (or
    is empty) from `initState` produces state `(sequence, [])`. The
    trailing starter forces `currentRun := []`. -/
theorem fold_HSR_endingStarter_from_init
    (L : List Nat)
    (hSR : HasSortedRuns L)
    (hEnd : L = []
          ∨ ∃ (pre : List Nat) (last : Nat),
              L = pre ++ [last]
                ∧ Lookup.canonicalCombiningClass last = 0) :
    L.foldl stepReorder initState
      = { emitted := L.toArray, currentRun := [] } := by
  rcases hEnd with hNil | ⟨pre, last, hL, hLast⟩
  · subst hNil
    rfl
  · subst hL
    rw [List.foldl_append]
    have hPreSR : HasSortedRuns pre :=
      HasSortedRuns_of_append_singleton pre last hSR
    have hReorderPre : reorder pre.toArray = pre.toArray := by
      apply reorder_id_on_HasSortedRuns
      simpa using hPreSR
    have hFoldPreEq : pre.foldl stepReorder initState
                    = pre.toArray.foldl stepReorder initState := by
      rw [← Array.foldl_toList]
    rw [hFoldPreEq]
    simp only [List.foldl_cons, List.foldl_nil]
    have hStep :
        stepReorder (pre.toArray.foldl stepReorder initState) last
          = { emitted := (pre.toArray.foldl stepReorder initState).emitted
                           ++ flushRun (pre.toArray.foldl stepReorder initState)
                           ++ #[last]
            , currentRun := [] } := by
      unfold stepReorder
      rw [if_pos hLast]
    rw [hStep]
    have hReorderExpand :
        (pre.toArray.foldl stepReorder initState).emitted
          ++ flushRun (pre.toArray.foldl stepReorder initState)
        = pre.toArray := by
      exact hReorderPre
    rw [hReorderExpand]
    have hArr : pre.toArray ++ #[last] = (pre ++ [last]).toArray := by
      apply Array.toList_inj.mp
      simp
    rw [hArr]

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATE(REORDER A) CHARACTERIZATION
--
-- Given state(A), characterize state(reorder A):
--   state(reorder A).emitted    = state(A).emitted
--   state(reorder A).currentRun = (sortNonStarterRun state(A).currentRun.reverse).reverse
--
-- Uses the two fold characterizations above plus `reorder_eq`.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `state(reorder A).emitted = state(A).emitted`. -/
theorem state_reorder_emitted_eq_state_emitted (A : Array Nat) :
    ((reorder A).foldl stepReorder initState).emitted
      = (A.foldl stepReorder initState).emitted := by
  have hInvOut : ReorderOutputInvariant (A.foldl stepReorder initState) := by
    have h := foldl_stepReorder_output_invariant A.toList
    rw [Array.foldl_toList] at h
    exact h
  obtain ⟨hEmittedHSR, hEmittedEnd, hRunNS⟩ := hInvOut
  have hReorderEq :
      reorder A = (A.foldl stepReorder initState).emitted
                    ++ flushRun (A.foldl stepReorder initState) := rfl
  have hFlushListEq :
      (flushRun (A.foldl stepReorder initState)).toList
        = sortNonStarterRun (A.foldl stepReorder initState).currentRun.reverse := by
    unfold flushRun
    rfl
  have hStateEmitted :
      (A.foldl stepReorder initState).emitted.toList.foldl stepReorder initState
        = { emitted := (A.foldl stepReorder initState).emitted, currentRun := [] } := by
    have h := fold_HSR_endingStarter_from_init
                (A.foldl stepReorder initState).emitted.toList hEmittedHSR hEmittedEnd
    rw [h]
  have hReorderAToList :
      (reorder A).toList
        = (A.foldl stepReorder initState).emitted.toList
            ++ (flushRun (A.foldl stepReorder initState)).toList := by
    rw [hReorderEq]
    simp
  have hArrFoldEq :
      (reorder A).foldl stepReorder initState
        = (reorder A).toList.foldl stepReorder initState := by
    rw [← Array.foldl_toList]
  rw [hArrFoldEq, hReorderAToList, List.foldl_append, hStateEmitted]
  have hFlushNonStarter :
      ∀ x ∈ (flushRun (A.foldl stepReorder initState)).toList,
        0 < Lookup.canonicalCombiningClass x := by
    rw [hFlushListEq]
    intro x hx
    have hPreserve :
        ∀ y ∈ (A.foldl stepReorder initState).currentRun.reverse,
          0 < Lookup.canonicalCombiningClass y := by
      intro y hy
      rw [List.mem_reverse] at hy
      exact hRunNS y hy
    have hBool := sortNonStarterRun_preserves_all
      (fun n => decide (0 < Lookup.canonicalCombiningClass n))
      (A.foldl stepReorder initState).currentRun.reverse
      (fun y hy => by simp [hPreserve y hy])
      x hx
    exact of_decide_eq_true hBool
  rw [fold_nonstarters_from_state
      (flushRun (A.foldl stepReorder initState)).toList
      hFlushNonStarter
      (A.foldl stepReorder initState).emitted
      []]

/-- `sortNonStarterRun state(reorder A).currentRun.reverse
      = sortNonStarterRun state(A).currentRun.reverse`. -/
theorem state_reorder_currentRun_sortedRun_eq (A : Array Nat) :
    sortNonStarterRun ((reorder A).foldl stepReorder initState).currentRun.reverse
      = sortNonStarterRun (A.foldl stepReorder initState).currentRun.reverse := by
  have hInvOut : ReorderOutputInvariant (A.foldl stepReorder initState) := by
    have h := foldl_stepReorder_output_invariant A.toList
    rw [Array.foldl_toList] at h
    exact h
  obtain ⟨hEmittedHSR, hEmittedEnd, hRunNS⟩ := hInvOut
  have hReorderEq :
      reorder A = (A.foldl stepReorder initState).emitted
                    ++ flushRun (A.foldl stepReorder initState) := rfl
  have hFlushListEq :
      (flushRun (A.foldl stepReorder initState)).toList
        = sortNonStarterRun (A.foldl stepReorder initState).currentRun.reverse := by
    unfold flushRun
    rfl
  have hStateEmitted :
      (A.foldl stepReorder initState).emitted.toList.foldl stepReorder initState
        = { emitted := (A.foldl stepReorder initState).emitted, currentRun := [] } := by
    have h := fold_HSR_endingStarter_from_init
                (A.foldl stepReorder initState).emitted.toList hEmittedHSR hEmittedEnd
    rw [h]
  have hReorderAToList :
      (reorder A).toList
        = (A.foldl stepReorder initState).emitted.toList
            ++ (flushRun (A.foldl stepReorder initState)).toList := by
    rw [hReorderEq]
    simp
  have hArrFoldEq :
      (reorder A).foldl stepReorder initState
        = (reorder A).toList.foldl stepReorder initState := by
    rw [← Array.foldl_toList]
  have hFlushNonStarter :
      ∀ x ∈ (flushRun (A.foldl stepReorder initState)).toList,
        0 < Lookup.canonicalCombiningClass x := by
    rw [hFlushListEq]
    intro x hx
    have hPreserve :
        ∀ y ∈ (A.foldl stepReorder initState).currentRun.reverse,
          0 < Lookup.canonicalCombiningClass y := by
      intro y hy
      rw [List.mem_reverse] at hy
      exact hRunNS y hy
    have hBool := sortNonStarterRun_preserves_all
      (fun n => decide (0 < Lookup.canonicalCombiningClass n))
      (A.foldl stepReorder initState).currentRun.reverse
      (fun y hy => by simp [hPreserve y hy])
      x hx
    exact of_decide_eq_true hBool
  rw [hArrFoldEq, hReorderAToList, List.foldl_append, hStateEmitted,
      fold_nonstarters_from_state
        (flushRun (A.foldl stepReorder initState)).toList
        hFlushNonStarter
        (A.foldl stepReorder initState).emitted
        []]
  show sortNonStarterRun
        ((flushRun (A.foldl stepReorder initState)).toList.reverse ++ []).reverse
     = sortNonStarterRun (A.foldl stepReorder initState).currentRun.reverse
  rw [List.append_nil, List.reverse_reverse]
  rw [hFlushListEq]
  exact sortNonStarterRun_idempotent (A.foldl stepReorder initState).currentRun.reverse

-- ═══════════════════════════════════════════════════════════════════════════════
-- REORDER_ABSORBING_LEFT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Single-element absorbing-left for non-starter append.** Uses the
    state characterization + `sortNonStarterRun_append_absorbing`. -/
theorem reorder_append_absorbing_nonstarter
    (A : Array Nat) (cp : Nat)
    (h : 0 < Lookup.canonicalCombiningClass cp) :
    reorder (A ++ #[cp]) = reorder (reorder A ++ #[cp]) := by
  have hCpNe : Lookup.canonicalCombiningClass cp ≠ 0 := Nat.pos_iff_ne_zero.mp h
  rw [reorder_eq (A ++ #[cp]), reorder_eq (reorder A ++ #[cp])]
  rw [Array.foldl_append, Array.foldl_append]
  have hStepLhs :
      (#[cp] : Array Nat).foldl stepReorder
        (A.foldl stepReorder { emitted := #[], currentRun := [] })
        = stepReorder
            (A.foldl stepReorder { emitted := #[], currentRun := [] }) cp := by
    simp
  have hStepRhs :
      (#[cp] : Array Nat).foldl stepReorder
        ((reorder A).foldl stepReorder { emitted := #[], currentRun := [] })
        = stepReorder
            ((reorder A).foldl stepReorder { emitted := #[], currentRun := [] }) cp := by
    simp
  rw [hStepLhs, hStepRhs]
  let sA := A.foldl stepReorder { emitted := #[], currentRun := [] }
  let sRA := (reorder A).foldl stepReorder { emitted := #[], currentRun := [] }
  have hStepNsLhs :
      stepReorder sA cp = { sA with currentRun := cp :: sA.currentRun } := by
    unfold stepReorder
    rw [if_neg hCpNe]
  have hStepNsRhs :
      stepReorder sRA cp = { sRA with currentRun := cp :: sRA.currentRun } := by
    unfold stepReorder
    rw [if_neg hCpNe]
  rw [hStepNsLhs, hStepNsRhs]
  -- LHS = sA.emitted ++ flushRun { sA with currentRun := cp :: sA.currentRun }
  --     = sA.emitted ++ (sortNonStarterRun (cp :: sA.currentRun).reverse).toArray
  --     = sA.emitted ++ (sortNonStarterRun (sA.currentRun.reverse ++ [cp])).toArray
  -- RHS = sRA.emitted ++ (sortNonStarterRun (sRA.currentRun.reverse ++ [cp])).toArray
  -- By state characterization: sA.emitted = sRA.emitted,
  --                            sortNonStarterRun sA.currentRun.reverse = sortNonStarterRun sRA.currentRun.reverse
  -- By absorbing: sortNonStarterRun (sA.currentRun.reverse ++ [cp]) = sortNonStarterRun (sRA.currentRun.reverse ++ [cp])
  have hEmittedEq : sA.emitted = sRA.emitted :=
    (state_reorder_emitted_eq_state_emitted A).symm
  have hSortedEq : sortNonStarterRun sA.currentRun.reverse
                 = sortNonStarterRun sRA.currentRun.reverse :=
    (state_reorder_currentRun_sortedRun_eq A).symm
  show sA.emitted ++ flushRun { sA with currentRun := cp :: sA.currentRun }
     = sRA.emitted ++ flushRun { sRA with currentRun := cp :: sRA.currentRun }
  have hFlushLhs :
      flushRun { sA with currentRun := cp :: sA.currentRun }
        = (sortNonStarterRun (sA.currentRun.reverse ++ [cp])).toArray := by
    unfold flushRun
    show (sortNonStarterRun (cp :: sA.currentRun).reverse).toArray
       = (sortNonStarterRun (sA.currentRun.reverse ++ [cp])).toArray
    rw [List.reverse_cons]
  have hFlushRhs :
      flushRun { sRA with currentRun := cp :: sRA.currentRun }
        = (sortNonStarterRun (sRA.currentRun.reverse ++ [cp])).toArray := by
    unfold flushRun
    show (sortNonStarterRun (cp :: sRA.currentRun).reverse).toArray
       = (sortNonStarterRun (sRA.currentRun.reverse ++ [cp])).toArray
    rw [List.reverse_cons]
  rw [hFlushLhs, hFlushRhs]
  have hAbsorbLhs : sortNonStarterRun (sA.currentRun.reverse ++ [cp])
                  = sortNonStarterRun (sortNonStarterRun sA.currentRun.reverse ++ [cp]) :=
    sortNonStarterRun_append_absorbing sA.currentRun.reverse cp
  have hAbsorbRhs : sortNonStarterRun (sRA.currentRun.reverse ++ [cp])
                  = sortNonStarterRun (sortNonStarterRun sRA.currentRun.reverse ++ [cp]) :=
    sortNonStarterRun_append_absorbing sRA.currentRun.reverse cp
  rw [hAbsorbLhs, hAbsorbRhs, hSortedEq, hEmittedEq]

/-- **Single-element absorbing-left.** Combines the starter case (via
    `reorder_append_starter`) and the non-starter case. -/
theorem reorder_append_absorbing (A : Array Nat) (cp : Nat) :
    reorder (A ++ #[cp]) = reorder (reorder A ++ #[cp]) := by
  by_cases h : Lookup.canonicalCombiningClass cp = 0
  · rw [reorder_append_starter A cp h]
    rw [reorder_append_starter (reorder A) cp h]
    rw [reorder_idempotent]
  · have hPos : 0 < Lookup.canonicalCombiningClass cp := Nat.pos_of_ne_zero h
    exact reorder_append_absorbing_nonstarter A cp hPos

/-- Local snoc-induction principle for `List Nat`. Derived by inducting
    on the reversed list: every `List` is `(reverse of reverse)`, so
    inducting on the reverse reduces the `l ++ [e]` case to the
    `cons hd tl` case of `tl.reverse ++ [hd]`. -/
theorem list_snoc_ind
    {motive : List Nat → Prop} (L : List Nat)
    (nil : motive [])
    (snoc : ∀ (l : List Nat) (e : Nat), motive l → motive (l ++ [e])) :
    motive L := by
  suffices h : ∀ (R : List Nat), motive R.reverse by
    have hR := h L.reverse
    have hRR : L.reverse.reverse = L := by simp
    rw [hRR] at hR
    exact hR
  intro R
  induction R with
  | nil => simpa using nil
  | cons hd tl ih =>
    rw [List.reverse_cons]
    exact snoc tl.reverse hd ih

/-- **General absorbing-left.** For any arrays `A`, `B`:
    `reorder (A ++ B) = reorder (reorder A ++ B)`. Induction performed
    on `B.toList` via `list_snoc_ind` (snoc-induction), which reduces
    each step to a single-element append handled by
    `reorder_append_absorbing`. -/
theorem reorder_absorbing_left (A B : Array Nat) :
    reorder (A ++ B) = reorder (reorder A ++ B) := by
  suffices h : ∀ (L : List Nat),
      reorder (A ++ L.toArray) = reorder (reorder A ++ L.toArray) by
    have hB := h B.toList
    have hTA : B.toList.toArray = B := Array.toArray_toList
    rw [hTA] at hB
    exact hB
  intro L
  induction L using list_snoc_ind with
  | nil =>
    have hNilToArr : ([] : List Nat).toArray = (#[] : Array Nat) := rfl
    rw [hNilToArr]
    have hEmptyA : A ++ (#[] : Array Nat) = A := by
      apply Array.toList_inj.mp
      simp
    have hEmptyRA : reorder A ++ (#[] : Array Nat) = reorder A := by
      apply Array.toList_inj.mp
      simp
    rw [hEmptyA, hEmptyRA]
    exact (reorder_idempotent A).symm
  | snoc L' cp ih =>
    have hListToArr : (L' ++ [cp]).toArray = L'.toArray ++ #[cp] := by
      apply Array.toList_inj.mp
      simp
    rw [hListToArr]
    have hAssoc1 : A ++ (L'.toArray ++ #[cp]) = (A ++ L'.toArray) ++ #[cp] := by
      rw [← Array.append_assoc]
    have hAssoc2 : reorder A ++ (L'.toArray ++ #[cp]) = (reorder A ++ L'.toArray) ++ #[cp] := by
      rw [← Array.append_assoc]
    rw [hAssoc1, hAssoc2]
    rw [reorder_append_absorbing (A ++ L'.toArray) cp]
    rw [reorder_append_absorbing (reorder A ++ L'.toArray) cp]
    rw [ih]

-- ═══════════════════════════════════════════════════════════════════════════════
-- REORDER COMMUTES WITH STRICT-MAX INSERTION
--
-- Array-level commutativity: for any prefix `A` and non-starter run `Y`,
-- moving a non-starter `cp` with `ccc cp > max(ccc y | y ∈ Y)` from after
-- `Y` to before `Y` leaves `reorder` unchanged. Both placements produce
-- the same sorted output because a stable sort over a run of non-starters
-- assigns `cp` to the tail regardless of its input position.
--
-- Formal statement:
--   reorder (A ++ Y ++ #[cp]) = reorder (A ++ #[cp] ++ Y)
--   when every `y ∈ Y.toList` is a non-starter with
--   `ccc y < ccc cp` (and `cp` is itself a non-starter).
--
-- Proof via state-characterization: fold `A`, then fold the non-starters
-- (which just prepend to `currentRun`), then observe that the final
-- `flushRun` sorts the same multiset on both sides. Close with
-- `sortNonStarterRun_append_cons_swap_max`.
--
-- Feeds `ComposeInversion.ReorderCommutesStrictMax` (the NFD-level
-- analogue driving Case 7 of `StepPreservesNFDEquivalence`).
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Helper for `reorder_commutes_strict_max`: `flushRun` agrees on two
    states whose `emitted` fields coincide and whose `currentRun` fields
    differ only by moving a strictly-greater-CCC element `cp` across a
    non-starter run `Y`. Factored out of the main theorem so the local
    `congr 1` on `.toArray` operates on a shallow `sortNonStarterRun`
    equality rather than the full fold term — keeps the main theorem's
    whnf/heartbeat budget from accumulating across the whole proof. -/
theorem flushRun_swap_strict_max
    (E : Array Nat) (R Y : List Nat) (cp : Nat)
    (hY : ∀ y ∈ Y, Lookup.canonicalCombiningClass y
                      < Lookup.canonicalCombiningClass cp) :
    flushRun { emitted := E, currentRun := cp :: (Y.reverse ++ R) }
      = flushRun { emitted := E, currentRun := Y.reverse ++ cp :: R } := by
  unfold flushRun
  congr 1
  have hLhsRev : (cp :: (Y.reverse ++ R)).reverse
                  = R.reverse ++ Y ++ [cp] := by
    simp [List.reverse_cons, List.reverse_append, List.reverse_reverse,
          List.append_assoc]
  have hRhsRev : (Y.reverse ++ cp :: R).reverse
                  = R.reverse ++ cp :: Y := by
    simp [List.reverse_cons, List.reverse_append, List.reverse_reverse,
          List.append_assoc]
  rw [hLhsRev, hRhsRev]
  exact sortNonStarterRun_append_cons_swap_max R.reverse Y cp hY

/-- **Strict-max reorder commutativity (array level).** A non-starter
    `cp` with CCC strictly greater than every element of a non-starter
    run `Y` can slide across `Y` without changing `reorder`'s output. -/
theorem reorder_commutes_strict_max
    (A Y : Array Nat) (cp : Nat)
    (hCp : 0 < Lookup.canonicalCombiningClass cp)
    (hY : ∀ y ∈ Y.toList,
            0 < Lookup.canonicalCombiningClass y
            ∧ Lookup.canonicalCombiningClass y
                < Lookup.canonicalCombiningClass cp) :
    reorder (A ++ Y ++ #[cp]) = reorder (A ++ #[cp] ++ Y) := by
  have hCpNe : Lookup.canonicalCombiningClass cp ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hCp
  have hYNonStarter : ∀ y ∈ Y.toList,
        0 < Lookup.canonicalCombiningClass y :=
    fun y hy => (hY y hy).1
  have hYStrictLt : ∀ y ∈ Y.toList,
        Lookup.canonicalCombiningClass y
          < Lookup.canonicalCombiningClass cp :=
    fun y hy => (hY y hy).2
  -- Unfold `reorder` on both sides, split the folds.
  rw [reorder_eq (A ++ Y ++ #[cp]), reorder_eq (A ++ #[cp] ++ Y)]
  rw [Array.foldl_append, Array.foldl_append,
      Array.foldl_append, Array.foldl_append]
  -- Reduce the singleton folds.
  have hSingletonLhs :
      (#[cp] : Array Nat).foldl stepReorder
        (Y.foldl stepReorder (A.foldl stepReorder { emitted := #[], currentRun := [] }))
        = stepReorder
            (Y.foldl stepReorder (A.foldl stepReorder { emitted := #[], currentRun := [] })) cp := by
    simp
  have hSingletonRhs :
      (#[cp] : Array Nat).foldl stepReorder
        (A.foldl stepReorder { emitted := #[], currentRun := [] })
        = stepReorder (A.foldl stepReorder { emitted := #[], currentRun := [] }) cp := by
    simp
  rw [hSingletonLhs, hSingletonRhs]
  -- Characterize the state after folding `Y` (all non-starters).
  have hFoldY :
      Y.foldl stepReorder (A.foldl stepReorder { emitted := #[], currentRun := [] })
        = { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
          , currentRun := Y.toList.reverse
                           ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun
          } := by
    rw [← Array.foldl_toList]
    exact fold_nonstarters_from_state Y.toList hYNonStarter
      (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
      (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun
  -- Characterize the state after `A ++ #[cp]`, then folding `Y`.
  have hStepCp :
      stepReorder (A.foldl stepReorder { emitted := #[], currentRun := [] }) cp
        = { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
          , currentRun := cp :: (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun
          } :=
    stepReorder_nonstarter_output
      (A.foldl stepReorder { emitted := #[], currentRun := [] }) cp hCpNe
  have hFoldYFromCp :
      Y.foldl stepReorder
        (stepReorder (A.foldl stepReorder { emitted := #[], currentRun := [] }) cp)
        = { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
          , currentRun := Y.toList.reverse
                           ++ cp :: (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun
          } := by
    rw [hStepCp]
    rw [← Array.foldl_toList]
    exact fold_nonstarters_from_state Y.toList hYNonStarter
      (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
      (cp :: (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun)
  rw [hFoldY, hFoldYFromCp]
  -- Apply `stepReorder` at `cp` on the LHS (non-starter).
  have hStepLhs :
      stepReorder
        { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
        , currentRun := Y.toList.reverse
                         ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun
        } cp
        = { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
          , currentRun := cp :: (Y.toList.reverse
                                   ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun)
          } :=
    stepReorder_nonstarter_output
      { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
      , currentRun := Y.toList.reverse
                       ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun
      } cp hCpNe
  rw [hStepLhs]
  -- Both records share `emitted := stateA.emitted`. The `.emitted`
  -- projections reduce by iota, letting `congrArg (stateA.emitted ++ ·)`
  -- unify the common prefix — no top-level `congr 1` over the full
  -- `Array.append` term (which accumulates whnf work across the proof
  -- and exhausts the heartbeat budget). Remaining `flushRun` equality
  -- is discharged by the `flushRun_swap_strict_max` helper.
  exact congrArg
    ((A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted ++ ·)
    (flushRun_swap_strict_max
      (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
      (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun
      Y.toList cp hYStrictLt)

-- ═══════════════════════════════════════════════════════════════════════════════
-- MULTI-ELEMENT FOLDL COMMUTATIVITY (strict-max disjoint CCCs)
--
-- Lifts `foldl_insertByCCC_comm_strict_lt` from single-element to
-- multi-element: two foldl's of `insertByCCC` commute when every
-- element of the "upper" list has strictly greater CCC than every
-- element of the "lower" list. The NFD-level
-- `ReorderCommutesStrictMax` discharge uses this to swap a
-- multi-element `fullCanonicalDecompose cp` across the decomposed
-- buffer, since `cp`'s decomposition may introduce multiple non-
-- starters (e.g., U+0344 decomposes to U+0308 U+0301).
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Multi-element foldl-foldl commutativity.** For lists `A`, `B`
    where every element of `A` has strictly greater CCC than every
    element of `B`, folding `B`'s inserts then `A`'s inserts
    produces the same result as folding `A`'s then `B`'s. Proof by
    induction on `A`, each step using the single-element commutation
    `foldl_insertByCCC_comm_strict_lt`. -/
theorem foldl_insertByCCC_foldl_comm_strict_lt
    (A B : List Nat) (L : List Nat)
    (hStrict : ∀ a ∈ A, ∀ b ∈ B,
                 Lookup.canonicalCombiningClass b
                   < Lookup.canonicalCombiningClass a) :
    B.foldl (fun acc y => insertByCCC y acc) (A.foldl (fun acc y => insertByCCC y acc) L)
      = A.foldl (fun acc y => insertByCCC y acc) (B.foldl (fun acc y => insertByCCC y acc) L) := by
  induction A generalizing L with
  | nil => rfl
  | cons a A' ih =>
    have hStrict' : ∀ a' ∈ A', ∀ b ∈ B,
                       Lookup.canonicalCombiningClass b
                         < Lookup.canonicalCombiningClass a' :=
      fun a' ha' b hb => hStrict a' (List.mem_cons_of_mem a ha') b hb
    have hStrictHead : ∀ b ∈ B,
                         Lookup.canonicalCombiningClass b
                           < Lookup.canonicalCombiningClass a :=
      fun b hb => hStrict a (by simp) b hb
    simp only [List.foldl_cons]
    -- LHS: B.foldl (A'.foldl L_after_a)
    --      where L_after_a = insertByCCC a L
    -- RHS: A'.foldl (B.foldl (insertByCCC a L))
    --    = A'.foldl (insertByCCC a (B.foldl L))   [by foldl_insertByCCC_comm_strict_lt]
    --    = A'.foldl (B.foldl L)_after_a
    rw [ih (insertByCCC a L) hStrict']
    rw [← foldl_insertByCCC_comm_strict_lt B a L hStrictHead]

/-- **sortNonStarterRun block swap (strict-max disjoint CCCs).** For a
    prefix `R` and two non-starter blocks `A`, `B` where every element
    of `A` has strictly greater CCC than every element of `B`, sorting
    `R ++ A ++ B` produces the same output as sorting `R ++ B ++ A`.
    Follows from `foldl_insertByCCC_foldl_comm_strict_lt` via foldl
    rearrangement. -/
theorem sortNonStarterRun_swap_disjoint_ccc
    (R A B : List Nat)
    (hStrict : ∀ a ∈ A, ∀ b ∈ B,
                 Lookup.canonicalCombiningClass b
                   < Lookup.canonicalCombiningClass a) :
    sortNonStarterRun (R ++ A ++ B) = sortNonStarterRun (R ++ B ++ A) := by
  show (R ++ A ++ B).foldl (fun acc y => insertByCCC y acc) []
     = (R ++ B ++ A).foldl (fun acc y => insertByCCC y acc) []
  rw [List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_append]
  exact foldl_insertByCCC_foldl_comm_strict_lt A B
    (R.foldl (fun acc y => insertByCCC y acc) []) hStrict

-- ═══════════════════════════════════════════════════════════════════════════════
-- REORDER COMMUTES WITH MULTI-ELEMENT STRICT-MAX RUN
--
-- Array-level multi-element version of `reorder_commutes_strict_max`.
-- The non-Hangul primary-composite factorization can expand a single
-- non-starter `cp` into a multi-element fullCanonicalDecompose output
-- (e.g., U+0344 → [U+0308, U+0301]). The NFD-level
-- `ReorderCommutesStrictMax` proof needs to commute this entire
-- multi-element block `C` across the decomposed buffer `Y` when
-- `C`'s CCCs are strictly greater than `Y`'s.
-- ═══════════════════════════════════════════════════════════════════════════════

set_option maxRecDepth 8192 in
/-- **Multi-element strict-max reorder commutativity (array level).**
    A non-starter run `C` whose every element has CCC strictly greater
    than every element of the non-starter run `Y` can slide across `Y`
    without changing `reorder`'s output. Generalizes
    `reorder_commutes_strict_max` from single `cp` to multi-element `C`. -/
theorem reorder_commutes_strict_max_multi
    (A Y C : Array Nat)
    (hCpos : ∀ c ∈ C.toList, 0 < Lookup.canonicalCombiningClass c)
    (hYpos : ∀ y ∈ Y.toList, 0 < Lookup.canonicalCombiningClass y)
    (hStrict : ∀ c ∈ C.toList, ∀ y ∈ Y.toList,
                 Lookup.canonicalCombiningClass y
                   < Lookup.canonicalCombiningClass c) :
    reorder (A ++ Y ++ C) = reorder (A ++ C ++ Y) := by
  rw [reorder_eq (A ++ Y ++ C), reorder_eq (A ++ C ++ Y)]
  rw [Array.foldl_append, Array.foldl_append,
      Array.foldl_append, Array.foldl_append]
  -- Characterize Y.foldl from stateA.
  have hFoldY :
      Y.foldl stepReorder (A.foldl stepReorder { emitted := #[], currentRun := [] })
        = { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
          , currentRun := Y.toList.reverse
                           ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun
          } := by
    rw [← Array.foldl_toList]
    exact fold_nonstarters_from_state Y.toList hYpos
      (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
      (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun
  -- Characterize C.foldl from (Y.foldl stateA).
  have hFoldCfromY :
      C.foldl stepReorder (Y.foldl stepReorder (A.foldl stepReorder { emitted := #[], currentRun := [] }))
        = { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
          , currentRun := C.toList.reverse
                           ++ (Y.toList.reverse
                                 ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun)
          } := by
    rw [hFoldY]
    rw [← Array.foldl_toList]
    exact fold_nonstarters_from_state C.toList hCpos
      (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
      (Y.toList.reverse
        ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun)
  -- Characterize C.foldl from stateA.
  have hFoldC :
      C.foldl stepReorder (A.foldl stepReorder { emitted := #[], currentRun := [] })
        = { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
          , currentRun := C.toList.reverse
                           ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun
          } := by
    rw [← Array.foldl_toList]
    exact fold_nonstarters_from_state C.toList hCpos
      (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
      (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun
  -- Characterize Y.foldl from (C.foldl stateA).
  have hFoldYfromC :
      Y.foldl stepReorder (C.foldl stepReorder (A.foldl stepReorder { emitted := #[], currentRun := [] }))
        = { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
          , currentRun := Y.toList.reverse
                           ++ (C.toList.reverse
                                 ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun)
          } := by
    rw [hFoldC]
    rw [← Array.foldl_toList]
    exact fold_nonstarters_from_state Y.toList hYpos
      (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
      (C.toList.reverse
        ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun)
  rw [hFoldCfromY, hFoldYfromC]
  -- Both records share `emitted`; discharge via congrArg on the common prefix.
  -- The remaining `flushRun` equality reduces to `sortNonStarterRun_swap_disjoint_ccc`.
  have hFlushEq :
      flushRun { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
               , currentRun := C.toList.reverse
                                ++ (Y.toList.reverse
                                      ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun) }
        = flushRun { emitted := (A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted
                   , currentRun := Y.toList.reverse
                                    ++ (C.toList.reverse
                                          ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun) } := by
    unfold flushRun
    congr 1
    have hLhsRev :
        (C.toList.reverse
          ++ (Y.toList.reverse
                ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun)).reverse
          = (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun.reverse
              ++ Y.toList ++ C.toList := by
      simp [List.reverse_append, List.reverse_reverse, List.append_assoc]
    have hRhsRev :
        (Y.toList.reverse
          ++ (C.toList.reverse
                ++ (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun)).reverse
          = (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun.reverse
              ++ C.toList ++ Y.toList := by
      simp [List.reverse_append, List.reverse_reverse, List.append_assoc]
    rw [hLhsRev, hRhsRev]
    exact (sortNonStarterRun_swap_disjoint_ccc
            (A.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun.reverse
            C.toList Y.toList hStrict).symm
  exact congrArg
    ((A.foldl stepReorder { emitted := #[], currentRun := [] }).emitted ++ ·)
    hFlushEq

-- ═══════════════════════════════════════════════════════════════════════════════
-- SORT RIGHT-ABSORBING
--
-- Dual of `sortNonStarterRun_append_absorbing`: pre-sorting the RIGHT
-- operand of a concatenation produces the same stably-sorted result
-- as sorting the unsorted original.  Foundation for
-- `reorder_absorbing_right` and `toNFD_absorbing_right`, which in
-- turn close the sequence lift `CaseFoldNfdCommutesSeq`.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Symmetric companion to `foldl_insertByCCC_comm_strict_lt`: when
    every element of `Y` has CCC STRICTLY GREATER than `cp`, inserting
    `cp` into `L` first and then folding `Y` yields the same result as
    folding `Y` first and then inserting `cp`.  Reduces to
    `insertByCCC_comm_strict_lt` with swapped codepoint arguments. -/
theorem foldl_insertByCCC_comm_strict_gt
    (Y : List Nat) (cp : Nat) (L : List Nat)
    (hY : ∀ y ∈ Y,
            Lookup.canonicalCombiningClass cp
              < Lookup.canonicalCombiningClass y) :
    insertByCCC cp (Y.foldl (fun acc y => insertByCCC y acc) L)
      = Y.foldl (fun acc y => insertByCCC y acc) (insertByCCC cp L) := by
  induction Y generalizing L with
  | nil => rfl
  | cons y Y' ih =>
    simp only [List.foldl_cons]
    have hY' : ∀ z ∈ Y',
                 Lookup.canonicalCombiningClass cp
                   < Lookup.canonicalCombiningClass z :=
      fun z hz => hY z (by simp [hz])
    have hYhd : Lookup.canonicalCombiningClass cp
                  < Lookup.canonicalCombiningClass y := hY y (by simp)
    rw [ih (insertByCCC y L) hY']
    rw [← insertByCCC_comm_strict_lt L cp y hYhd]

/-- Split a CCC-sorted list around the sorted position of a new
    element `x`.  Every sorted `N` factors as `N₁ ++ N₂` where
    `insertByCCC x N = N₁ ++ x :: N₂` and every element of `N₂` has
    CCC strictly greater than `x`'s CCC.  Induction on `N`: if the
    head has CCC strictly greater than `x`, split at the head;
    otherwise, recurse into the tail. -/
theorem insertByCCC_split_sorted
    (N : List Nat) (hN : IsCCCSorted N) (x : Nat) :
    ∃ (N₁ N₂ : List Nat),
      N = N₁ ++ N₂ ∧
      insertByCCC x N = N₁ ++ x :: N₂ ∧
      ∀ y ∈ N₂, Lookup.canonicalCombiningClass x
                   < Lookup.canonicalCombiningClass y := by
  induction N with
  | nil =>
    have hEmptyMem : ∀ y ∈ ([] : List Nat),
        Lookup.canonicalCombiningClass x
          < Lookup.canonicalCombiningClass y := by
      intro y hy
      cases hy
    exact ⟨[], [], rfl, rfl, hEmptyMem⟩
  | cons hd tl ih =>
    by_cases h : Lookup.canonicalCombiningClass x
                   < Lookup.canonicalCombiningClass hd
    · have hInsHead : insertByCCC x (hd :: tl) = [] ++ x :: (hd :: tl) := by
        rw [insertByCCC_cons, if_pos h]
        rfl
      have hGtAll : ∀ y ∈ hd :: tl,
          Lookup.canonicalCombiningClass x
            < Lookup.canonicalCombiningClass y := by
        intro y hy
        rcases List.mem_cons.mp hy with hEq | hyTl
        · rw [hEq]; exact h
        · have hHdLe : Lookup.canonicalCombiningClass hd
                         ≤ Lookup.canonicalCombiningClass y :=
            IsCCCSorted_tail_all_ge hN y hyTl
          omega
      exact ⟨[], hd :: tl, rfl, hInsHead, hGtAll⟩
    · have hTlSorted : IsCCCSorted tl := IsCCCSorted_tail hN
      obtain ⟨N₁', N₂', hEq, hIns, hGt⟩ := ih hTlSorted
      have hConsEq : hd :: tl = (hd :: N₁') ++ N₂' := by
        rw [hEq]; rfl
      have hConsIns : insertByCCC x (hd :: tl) = (hd :: N₁') ++ x :: N₂' := by
        rw [insertByCCC_cons, if_neg h, hIns]; rfl
      exact ⟨hd :: N₁', N₂', hConsEq, hConsIns, hGt⟩

/-- For any sorted list `N` and list `A`, inserting `x` after folding
    `N` equals folding `insertByCCC x N` — the insertion can be
    "pushed" past all elements of `N`'s suffix (those with CCC
    strictly greater than `x`) because `insertByCCC` commutes with
    each such insertion.  Uses `insertByCCC_split_sorted` to identify
    the pushing region. -/
theorem insertByCCC_foldl_absorb
    (N : List Nat) (hN : IsCCCSorted N)
    (A : List Nat) (x : Nat) :
    insertByCCC x (N.foldl (fun acc y => insertByCCC y acc) A)
      = (insertByCCC x N).foldl (fun acc y => insertByCCC y acc) A := by
  obtain ⟨N₁, N₂, hEq, hIns, hN₂gt⟩ := insertByCCC_split_sorted N hN x
  rw [hIns, hEq]
  rw [List.foldl_append, List.foldl_append]
  simp only [List.foldl_cons]
  exact foldl_insertByCCC_comm_strict_gt N₂ x
          (N₁.foldl (fun acc y => insertByCCC y acc) A) hN₂gt

/-- Snoc expansion of `sortNonStarterRun`: sorting a snoc-list
    equals inserting the new element into the sorted prefix. -/
theorem sortNonStarterRun_snoc (L : List Nat) (x : Nat) :
    sortNonStarterRun (L ++ [x]) = insertByCCC x (sortNonStarterRun L) := by
  show (L ++ [x]).foldl (fun acc cp => insertByCCC cp acc) []
     = insertByCCC x (sortNonStarterRun L)
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rfl

/-- Folding `insertByCCC` over `M` or over `sortNonStarterRun M` into
    the same sorted accumulator `A` produces the same result.  The
    order of stable insertions is invariant under the stable-sort
    permutation of `M`: equal-CCC elements keep their relative
    positions, strict-CCC insertions commute, and the accumulator
    stays sorted across insertions. -/
theorem foldl_insertByCCC_sort_invariant
    (A : List Nat) (M : List Nat) :
    M.foldl (fun acc cp => insertByCCC cp acc) A
      = (sortNonStarterRun M).foldl (fun acc cp => insertByCCC cp acc) A := by
  induction M using list_snoc_ind with
  | nil => rfl
  | snoc M' x ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih]
    rw [sortNonStarterRun_snoc M' x]
    exact insertByCCC_foldl_absorb (sortNonStarterRun M')
            (sortNonStarterRun_sorted M') A x

/-- **Right-absorbing for `sortNonStarterRun`.**  Stable-sorting
    `L ++ M` equals stable-sorting `L ++ sortNonStarterRun M`:
    pre-sorting the right operand leaves the final output
    unchanged.  Dual of `sortNonStarterRun_append_absorbing`, which
    pre-sorts the left operand. -/
theorem sortNonStarterRun_right_absorbing (L M : List Nat) :
    sortNonStarterRun (L ++ M)
      = sortNonStarterRun (L ++ sortNonStarterRun M) := by
  show (L ++ M).foldl (fun acc cp => insertByCCC cp acc) []
     = (L ++ sortNonStarterRun M).foldl (fun acc cp => insertByCCC cp acc) []
  rw [List.foldl_append, List.foldl_append]
  exact foldl_insertByCCC_sort_invariant
          (L.foldl (fun acc cp => insertByCCC cp acc) []) M

-- ═══════════════════════════════════════════════════════════════════════════════
-- REORDER_ABSORBING_RIGHT
--
-- Lift `sortNonStarterRun_right_absorbing` to the array-level
-- `reorder` via the state-machine decomposition.  The right operand
-- interacts with the left operand only through the trailing
-- non-starter run of the left: every pre-reordering of the right
-- operand corresponds to a pre-sort of that boundary non-starter
-- run, which `sortNonStarterRun_right_absorbing` closes.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Generalisation of `reorder_with_prefixed_state` allowing a
    non-empty starting `currentRun`.  When the starting state is
    `{Z, Rrev}` with `Rrev` all non-starters, folding `Y` and then
    flushing produces `Z ++ reorder (Rrev.reverse.toArray ++ Y)`.
    Reduces to the empty-currentRun version by pre-folding
    `Rrev.reverse.toArray` into the initial state. -/
theorem reorder_with_prefixed_run_state
    (Y : Array Nat) (Z : Array Nat) (Rrev : List Nat)
    (hRrev : ∀ r ∈ Rrev, 0 < Lookup.canonicalCombiningClass r) :
    (Y.foldl stepReorder { emitted := Z, currentRun := Rrev }).emitted
      ++ flushRun (Y.foldl stepReorder { emitted := Z, currentRun := Rrev })
      = Z ++ reorder (Rrev.reverse.toArray ++ Y) := by
  -- Rrev.reverse is the non-starter run in forward order; folding it
  -- from initState produces exactly state {#[], Rrev}.
  have hRrevRevNS : ∀ x ∈ Rrev.reverse, 0 < Lookup.canonicalCombiningClass x := by
    intro x hx
    rw [List.mem_reverse] at hx
    exact hRrev x hx
  have hFoldRrev :
      Rrev.reverse.toArray.foldl stepReorder { emitted := #[], currentRun := [] }
        = { emitted := #[], currentRun := Rrev } := by
    rw [← Array.foldl_toList]
    have hT : Rrev.reverse.toArray.toList = Rrev.reverse := List.toList_toArray
    rw [hT]
    have hFoldNS := fold_nonstarters_from_state Rrev.reverse hRrevRevNS
                      (#[] : Array Nat) []
    rw [hFoldNS]
    have hRR : Rrev.reverse.reverse = Rrev := List.reverse_reverse Rrev
    rw [hRR, List.append_nil]
  -- Rewrite LHS via foldl_list_stepReorder_emitted_add and
  -- foldl_list_stepReorder_currentRun_eq.
  rw [← Array.foldl_toList]
  rw [foldl_list_stepReorder_emitted_add Y.toList Z Rrev]
  have hFlushEq :
      flushRun (Y.toList.foldl stepReorder { emitted := Z, currentRun := Rrev })
        = flushRun (Y.toList.foldl stepReorder { emitted := #[], currentRun := Rrev }) := by
    unfold flushRun
    rw [foldl_list_stepReorder_currentRun_eq Y.toList Z Rrev]
  rw [hFlushEq]
  -- Now the LHS equals Z ++ (fold Y from {#[], Rrev}).emitted ++ flushRun(fold Y from {#[], Rrev}).
  -- Collapse to Z ++ reorder (Rrev.reverse.toArray ++ Y).
  rw [show reorder (Rrev.reverse.toArray ++ Y)
        = ((Rrev.reverse.toArray ++ Y).foldl stepReorder
              { emitted := #[], currentRun := [] }).emitted
          ++ flushRun
              ((Rrev.reverse.toArray ++ Y).foldl stepReorder
                { emitted := #[], currentRun := [] })
       from rfl]
  rw [Array.foldl_append]
  rw [hFoldRrev]
  rw [← Array.foldl_toList]
  simp [Array.append_assoc]

/-- **Intermediate reduction to non-starter left operand.**  For any
    `Z, Rrev` (`Rrev` all non-starters) and arrays `Y, W` where
    `state(Z) = {Z.emitted, Rrev}`, the right-absorbing property for
    `X ++ Y` reduces to the right-absorbing property for
    `(Rrev.reverse.toArray) ++ Y`.  Corollary of
    `reorder_with_prefixed_run_state`. -/
theorem reorder_absorb_right_via_prefix
    (Z : Array Nat) (Rrev : List Nat)
    (hRrev : ∀ r ∈ Rrev, 0 < Lookup.canonicalCombiningClass r)
    (Y : Array Nat)
    (hIH : reorder (Rrev.reverse.toArray ++ Y)
             = reorder (Rrev.reverse.toArray ++ reorder Y)) :
    (Y.foldl stepReorder { emitted := Z, currentRun := Rrev }).emitted
      ++ flushRun (Y.foldl stepReorder { emitted := Z, currentRun := Rrev })
      = ((reorder Y).foldl stepReorder { emitted := Z, currentRun := Rrev }).emitted
          ++ flushRun ((reorder Y).foldl stepReorder { emitted := Z, currentRun := Rrev }) := by
  rw [reorder_with_prefixed_run_state Y Z Rrev hRrev]
  rw [reorder_with_prefixed_run_state (reorder Y) Z Rrev hRrev]
  rw [hIH]

/-- `reorder` applied to an all-non-starter array equals the
    stable sort of its underlying list.  Derived from
    `fold_nonstarters_from_state` applied to the whole array. -/
theorem reorder_all_nonStarter_eq_sort
    (X : Array Nat)
    (hX : ∀ x ∈ X.toList, 0 < Lookup.canonicalCombiningClass x) :
    reorder X = (sortNonStarterRun X.toList).toArray := by
  rw [reorder_eq X]
  rw [← Array.foldl_toList]
  rw [fold_nonstarters_from_state X.toList hX (#[] : Array Nat) []]
  unfold flushRun
  simp

/-- Decomposition: every array is either all non-starters, or splits
    into an all-non-starter prefix followed by a starter and a
    remaining suffix.  Case-analysis helper for
    `reorder_absorbing_right_on_nonStarterRun`. -/
theorem array_first_starter_split (W : Array Nat) :
    (∀ w ∈ W.toList, 0 < Lookup.canonicalCombiningClass w)
    ∨ ∃ (W₁ W₃ : Array Nat) (s : Nat),
        W = W₁ ++ #[s] ++ W₃
        ∧ (∀ w ∈ W₁.toList, 0 < Lookup.canonicalCombiningClass w)
        ∧ Lookup.canonicalCombiningClass s = 0 := by
  suffices h : ∀ (L : List Nat),
      (∀ w ∈ L, 0 < Lookup.canonicalCombiningClass w)
      ∨ ∃ (L₁ L₃ : List Nat) (s : Nat),
          L = L₁ ++ s :: L₃
          ∧ (∀ w ∈ L₁, 0 < Lookup.canonicalCombiningClass w)
          ∧ Lookup.canonicalCombiningClass s = 0 by
    rcases h W.toList with hNS | ⟨L₁, L₃, s, hEq, hL₁NS, hSstar⟩
    · left; exact hNS
    · right
      have hArrayEq : W = L₁.toArray ++ #[s] ++ L₃.toArray := by
        apply Array.toList_inj.mp
        rw [hEq]
        simp
      have hArrayNS : ∀ w ∈ L₁.toArray.toList,
          0 < Lookup.canonicalCombiningClass w := by
        intro w hw
        rw [List.toList_toArray] at hw
        exact hL₁NS w hw
      exact ⟨L₁.toArray, L₃.toArray, s, hArrayEq, hArrayNS, hSstar⟩
  intro L
  induction L with
  | nil => left; intro w hw; cases hw
  | cons hd tl ih =>
    by_cases hHd : Lookup.canonicalCombiningClass hd = 0
    · right
      have hSplitEq : hd :: tl = [] ++ hd :: tl := by simp
      have hEmptyNS : ∀ w ∈ ([] : List Nat),
          0 < Lookup.canonicalCombiningClass w := by
        intro w hw; cases hw
      exact ⟨[], tl, hd, hSplitEq, hEmptyNS, hHd⟩
    · have hHdNS : 0 < Lookup.canonicalCombiningClass hd :=
        Nat.pos_of_ne_zero hHd
      rcases ih with hNSTl | ⟨L₁', L₃', s, hEqTl, hL₁NS, hSstar⟩
      · left
        intro w hw
        rcases List.mem_cons.mp hw with hEq | hwTl
        · rw [hEq]; exact hHdNS
        · exact hNSTl w hwTl
      · right
        have hSplitEq : hd :: tl = (hd :: L₁') ++ s :: L₃' := by
          show hd :: tl = hd :: L₁' ++ s :: L₃'
          rw [hEqTl]; rfl
        have hPrefixNS : ∀ w ∈ hd :: L₁',
            0 < Lookup.canonicalCombiningClass w := by
          intro w hw
          rcases List.mem_cons.mp hw with hEq | hwL₁'
          · rw [hEq]; exact hHdNS
          · exact hL₁NS w hwL₁'
        exact ⟨hd :: L₁', L₃', s, hSplitEq, hPrefixNS, hSstar⟩

/-- **Reorder-right-absorbing for a non-starter left operand.** When
    `R` consists entirely of non-starters, pre-reordering the right
    operand commutes with `reorder` of the concatenation.  Case-split
    on `W`: (a) `W` all non-starters reduces to
    `sortNonStarterRun_right_absorbing`; (b) `W` has a starter, split
    at the first starter and apply `reorder_append_starter_middle` to
    reduce to case (a). -/
theorem reorder_absorbing_right_on_nonStarterRun
    (R : Array Nat)
    (hR : ∀ r ∈ R.toList, 0 < Lookup.canonicalCombiningClass r)
    (W : Array Nat) :
    reorder (R ++ W) = reorder (R ++ reorder W) := by
  rcases array_first_starter_split W with hAllNS | ⟨W₁, W₃, s, hEqW, hW₁NS, hSstar⟩
  · -- Case (a): W is all non-starters.  Both sides reduce to
    -- `sortNonStarterRun` of the concatenation.
    have hRWns : ∀ w ∈ (R ++ W).toList, 0 < Lookup.canonicalCombiningClass w := by
      intro w hw
      rw [Array.toList_append] at hw
      rcases List.mem_append.mp hw with h1 | h2
      · exact hR w h1
      · exact hAllNS w h2
    have hReorderW : reorder W = (sortNonStarterRun W.toList).toArray :=
      reorder_all_nonStarter_eq_sort W hAllNS
    have hSortedWNS : ∀ w ∈ (sortNonStarterRun W.toList), 0 < Lookup.canonicalCombiningClass w := by
      intro w hw
      have hBool := sortNonStarterRun_preserves_all
        (fun n => decide (0 < Lookup.canonicalCombiningClass n))
        W.toList
        (fun y hy => by simp [hAllNS y hy])
        w hw
      exact of_decide_eq_true hBool
    have hRreorderWns :
        ∀ w ∈ (R ++ reorder W).toList, 0 < Lookup.canonicalCombiningClass w := by
      intro w hw
      rw [Array.toList_append] at hw
      rcases List.mem_append.mp hw with h1 | h2
      · exact hR w h1
      · rw [hReorderW, List.toList_toArray] at h2
        exact hSortedWNS w h2
    rw [reorder_all_nonStarter_eq_sort (R ++ W) hRWns]
    rw [reorder_all_nonStarter_eq_sort (R ++ reorder W) hRreorderWns]
    have hLhsList : (R ++ W).toList = R.toList ++ W.toList := by
      rw [Array.toList_append]
    have hRhsList : (R ++ reorder W).toList = R.toList ++ sortNonStarterRun W.toList := by
      rw [Array.toList_append, hReorderW, List.toList_toArray]
    rw [hLhsList, hRhsList]
    rw [sortNonStarterRun_right_absorbing R.toList W.toList]
  · -- Case (b): W = W₁ ++ #[s] ++ W₃, W₁ all non-starters, s starter.
    -- Split at s via reorder_append_starter_middle, reduce to case (a)
    -- on the pre-s segment (which is all non-starters combined with R).
    rw [hEqW]
    -- LHS: reorder (R ++ (W₁ ++ #[s] ++ W₃))
    --    = reorder (R ++ W₁) ++ #[s] ++ reorder W₃
    have hLhsStep :
        reorder (R ++ (W₁ ++ #[s] ++ W₃))
          = reorder (R ++ W₁) ++ #[s] ++ reorder W₃ := by
      rw [show R ++ (W₁ ++ #[s] ++ W₃) = (R ++ W₁) ++ #[s] ++ W₃
            from by rw [← Array.append_assoc, ← Array.append_assoc]]
      exact reorder_append_starter_middle (R ++ W₁) s W₃ hSstar
    -- reorder (W₁ ++ #[s] ++ W₃) = reorder W₁ ++ #[s] ++ reorder W₃
    have hInnerReorder :
        reorder (W₁ ++ #[s] ++ W₃) = reorder W₁ ++ #[s] ++ reorder W₃ :=
      reorder_append_starter_middle W₁ s W₃ hSstar
    -- RHS: reorder (R ++ reorder (W₁ ++ #[s] ++ W₃))
    --    = reorder (R ++ reorder W₁) ++ #[s] ++ reorder W₃
    have hRhsStep :
        reorder (R ++ reorder (W₁ ++ #[s] ++ W₃))
          = reorder (R ++ reorder W₁) ++ #[s] ++ reorder W₃ := by
      rw [hInnerReorder]
      rw [show R ++ (reorder W₁ ++ #[s] ++ reorder W₃)
            = (R ++ reorder W₁) ++ #[s] ++ reorder W₃
          from by rw [← Array.append_assoc, ← Array.append_assoc]]
      rw [reorder_append_starter_middle (R ++ reorder W₁) s (reorder W₃) hSstar]
      rw [reorder_idempotent W₃]
    rw [hLhsStep, hRhsStep]
    -- Remaining: reorder (R ++ W₁) = reorder (R ++ reorder W₁).
    -- Both sides have R all non-starters and W₁ all non-starters, so
    -- this is the all-non-starter case, which reduces via
    -- `sortNonStarterRun_right_absorbing`.
    have hRW₁NS : ∀ w ∈ (R ++ W₁).toList, 0 < Lookup.canonicalCombiningClass w := by
      intro w hw
      rw [Array.toList_append] at hw
      rcases List.mem_append.mp hw with h1 | h2
      · exact hR w h1
      · exact hW₁NS w h2
    have hReorderW₁ : reorder W₁ = (sortNonStarterRun W₁.toList).toArray :=
      reorder_all_nonStarter_eq_sort W₁ hW₁NS
    have hSortedW₁NS : ∀ w ∈ (sortNonStarterRun W₁.toList),
                         0 < Lookup.canonicalCombiningClass w := by
      intro w hw
      have hBool := sortNonStarterRun_preserves_all
        (fun n => decide (0 < Lookup.canonicalCombiningClass n))
        W₁.toList
        (fun y hy => by simp [hW₁NS y hy])
        w hw
      exact of_decide_eq_true hBool
    have hRreorderW₁NS :
        ∀ w ∈ (R ++ reorder W₁).toList, 0 < Lookup.canonicalCombiningClass w := by
      intro w hw
      rw [Array.toList_append] at hw
      rcases List.mem_append.mp hw with h1 | h2
      · exact hR w h1
      · rw [hReorderW₁, List.toList_toArray] at h2
        exact hSortedW₁NS w h2
    have hLhsSort :
        reorder (R ++ W₁) = (sortNonStarterRun (R.toList ++ W₁.toList)).toArray := by
      rw [reorder_all_nonStarter_eq_sort (R ++ W₁) hRW₁NS]
      rw [Array.toList_append]
    have hRhsSort :
        reorder (R ++ reorder W₁)
          = (sortNonStarterRun (R.toList ++ sortNonStarterRun W₁.toList)).toArray := by
      rw [reorder_all_nonStarter_eq_sort (R ++ reorder W₁) hRreorderW₁NS]
      rw [Array.toList_append, hReorderW₁, List.toList_toArray]
    have hSortAbsorb :
        sortNonStarterRun (R.toList ++ W₁.toList)
          = sortNonStarterRun (R.toList ++ sortNonStarterRun W₁.toList) :=
      sortNonStarterRun_right_absorbing R.toList W₁.toList
    rw [hLhsSort, hRhsSort, hSortAbsorb]

/-- **Reorder right-absorbing.**  For any arrays `P, Q`,
    pre-reordering `Q` does not change `reorder (P ++ Q)`.  Proof
    reduces `P` to its trailing non-starter run via the
    state-machine characterization, then applies
    `reorder_absorbing_right_on_nonStarterRun`. -/
theorem reorder_absorbing_right (P Q : Array Nat) :
    reorder (P ++ Q) = reorder (P ++ reorder Q) := by
  -- Analyze state(P) to reduce to the non-starter-run-left case.
  have hInvOut : ReorderOutputInvariant
                    (P.foldl stepReorder { emitted := #[], currentRun := [] }) := by
    have h := foldl_stepReorder_output_invariant P.toList
    rw [Array.foldl_toList] at h
    exact h
  have hRunNS : ∀ x ∈ (P.foldl stepReorder { emitted := #[], currentRun := [] }).currentRun,
                   0 < Lookup.canonicalCombiningClass x := hInvOut.2.2
  let sP := P.foldl stepReorder { emitted := #[], currentRun := [] }
  have hRrevNS : ∀ r ∈ sP.currentRun, 0 < Lookup.canonicalCombiningClass r :=
    fun r hr => hRunNS r hr
  -- Step 1: reduce reorder (P ++ Q) via state of P.
  have hLhsStep :
      reorder (P ++ Q)
        = sP.emitted ++ reorder (sP.currentRun.reverse.toArray ++ Q) := by
    show ((P ++ Q).foldl stepReorder { emitted := #[], currentRun := [] }).emitted
           ++ flushRun ((P ++ Q).foldl stepReorder { emitted := #[], currentRun := [] })
         = sP.emitted ++ reorder (sP.currentRun.reverse.toArray ++ Q)
    rw [Array.foldl_append]
    exact reorder_with_prefixed_run_state Q sP.emitted sP.currentRun hRrevNS
  have hRhsStep :
      reorder (P ++ reorder Q)
        = sP.emitted ++ reorder (sP.currentRun.reverse.toArray ++ reorder Q) := by
    show ((P ++ reorder Q).foldl stepReorder { emitted := #[], currentRun := [] }).emitted
           ++ flushRun ((P ++ reorder Q).foldl stepReorder
                           { emitted := #[], currentRun := [] })
         = sP.emitted ++ reorder (sP.currentRun.reverse.toArray ++ reorder Q)
    rw [Array.foldl_append]
    exact reorder_with_prefixed_run_state (reorder Q) sP.emitted sP.currentRun hRrevNS
  -- Step 2: apply reorder_absorbing_right_on_nonStarterRun to the reduced problem.
  have hRunArrNS : ∀ r ∈ sP.currentRun.reverse.toArray.toList,
                     0 < Lookup.canonicalCombiningClass r := by
    intro r hr
    have hrL : r ∈ sP.currentRun.reverse.toArray.toList := hr
    rw [List.toList_toArray, List.mem_reverse] at hrL
    exact hRunNS r hrL
  have hCore :=
    reorder_absorbing_right_on_nonStarterRun sP.currentRun.reverse.toArray hRunArrNS Q
  rw [hLhsStep, hRhsStep, hCore]

end Unicode.Normalization.ReorderAppend
