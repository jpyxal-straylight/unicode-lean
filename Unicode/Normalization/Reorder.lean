/-
  Unicode.Normalization.Reorder

  The Canonical Ordering Algorithm from UAX #15 §1.3 / D109-D110.
  Given a sequence of codepoints, reorders consecutive non-starter
  runs (CCC > 0) by non-decreasing Canonical_Combining_Class,
  preserving relative order among codepoints with equal CCC (stable).
  Starter codepoints (CCC = 0) act as boundaries and are never moved.

  Implementation: single left-to-right fold. Non-starter codepoints
  accumulate into a pending run; on the next starter (or end of input)
  the run is sorted by CCC via insertion sort and emitted. Insertion
  sort is stable by construction when the insertion predicate uses
  strict `<` — equal-CCC elements stay in scan order.
-/

import Unicode.Normalization.Lookup

namespace Unicode.Normalization.Reorder

open Unicode.Normalization

/-- Stable insertion of a codepoint into a list already sorted by CCC.
    Places `x` immediately before the first element whose CCC is
    strictly greater; equal-CCC elements already in the list stay
    ahead of `x`, preserving stability. -/
def insertByCCC (x : Nat) : List Nat → List Nat
  | []      => [x]
  | y :: ys =>
    if Lookup.canonicalCombiningClass x < Lookup.canonicalCombiningClass y then
      x :: y :: ys
    else
      y :: insertByCCC x ys

/-- Stable sort a list of non-starter codepoints by CCC. -/
def sortNonStarterRun (run : List Nat) : List Nat :=
  run.foldl (fun sorted cp => insertByCCC cp sorted) []

/-- Fold state for the reorder pass. `currentRun` accumulates non-
    starter codepoints in REVERSE scan order so prepending is O(1);
    when flushed, the list is reversed back into scan order before
    sorting. -/
structure ReorderState where
  emitted    : Array Nat
  currentRun : List Nat
  deriving Inhabited

/-- Sort the accumulated non-starter run and return its sorted array. -/
def flushRun (s : ReorderState) : Array Nat :=
  (sortNonStarterRun s.currentRun.reverse).toArray

/-- Step: process one codepoint. -/
def stepReorder (s : ReorderState) (cp : Nat) : ReorderState :=
  if Lookup.canonicalCombiningClass cp = 0 then
    { emitted := s.emitted ++ flushRun s ++ #[cp], currentRun := [] }
  else
    { s with currentRun := cp :: s.currentRun }

/-- Canonical reordering of a codepoint sequence per UAX #15 §1.3. -/
def reorder (cps : Array Nat) : Array Nat :=
  let final := cps.foldl stepReorder { emitted := #[], currentRun := [] }
  final.emitted ++ flushRun final

-- ─────────────────────────────────────────────────────────────────────────────
--                                        // reorder // insertion-sort-stability
-- ─────────────────────────────────────────────────────────────────────────────

/-- A list of codepoints is CCC-non-decreasing if every adjacent pair
    `(x, y)` satisfies `CCC(x) ≤ CCC(y)`. Nil and singletons hold
    vacuously. This is the invariant `reorder` establishes on each
    non-starter run. -/
def IsCCCSorted : List Nat → Prop
  | []          => True
  | [_]         => True
  | x :: y :: t =>
    Lookup.canonicalCombiningClass x ≤ Lookup.canonicalCombiningClass y
      ∧ IsCCCSorted (y :: t)

@[simp] theorem IsCCCSorted_nil : IsCCCSorted [] = True := rfl
@[simp] theorem IsCCCSorted_singleton (x : Nat) : IsCCCSorted [x] = True := rfl
theorem IsCCCSorted_cons_cons (x y : Nat) (t : List Nat) :
    IsCCCSorted (x :: y :: t)
      ↔ Lookup.canonicalCombiningClass x ≤ Lookup.canonicalCombiningClass y
          ∧ IsCCCSorted (y :: t) := Iff.rfl

/-- Every element of a CCC-sorted list has CCC at most the CCC of the
    tail starting element, when considered across the whole list. The
    tail-bound transitivity invariant. -/
theorem IsCCCSorted_head_le_all {x : Nat} {rest : List Nat}
    (h : IsCCCSorted (x :: rest)) :
    ∀ y ∈ rest, Lookup.canonicalCombiningClass x ≤ Lookup.canonicalCombiningClass y := by
  induction rest generalizing x with
  | nil => intro y hy; cases hy
  | cons z zs ih =>
    obtain ⟨hxz, hrest⟩ := h
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hxz
    · have hzle : Lookup.canonicalCombiningClass z ≤ Lookup.canonicalCombiningClass y :=
        ih hrest y hy
      exact Nat.le_trans hxz hzle

/-- Bridge: for a CCC-sorted list `x :: rest`, every element of `rest`
    (not just the head) is ≥ x in CCC. Restated for direct use in the
    insertByCCC proof. -/
theorem IsCCCSorted_tail_all_ge {x : Nat} {rest : List Nat}
    (h : IsCCCSorted (x :: rest)) (y : Nat) (hy : y ∈ rest) :
    Lookup.canonicalCombiningClass x ≤ Lookup.canonicalCombiningClass y :=
  IsCCCSorted_head_le_all h y hy

/-- A sorted list with the head dropped is still sorted. -/
theorem IsCCCSorted_tail {x : Nat} {rest : List Nat}
    (h : IsCCCSorted (x :: rest)) : IsCCCSorted rest := by
  match rest with
  | []     => trivial
  | head :: tail => exact h.2

/-- Append an element whose CCC is ≥ every element's CCC in a sorted
    list: the resulting list is still sorted. -/
theorem IsCCCSorted_append_right {xs : List Nat} {x : Nat}
    (hxs : IsCCCSorted xs)
    (hbound : ∀ y ∈ xs, Lookup.canonicalCombiningClass y
                          ≤ Lookup.canonicalCombiningClass x) :
    IsCCCSorted (xs ++ [x]) := by
  induction xs with
  | nil => trivial
  | cons a as ih =>
    match as with
    | [] =>
      -- xs = [a]; xs ++ [x] = [a, x]; sorted iff CCC(a) ≤ CCC(x).
      refine ⟨?aLeX, ?tailSorted⟩
      · exact hbound a (by simp)
      · trivial
    | b :: bs =>
      -- xs = a :: b :: bs. xs ++ [x] = a :: (b :: bs ++ [x]).
      obtain ⟨hab, hrest⟩ := hxs
      refine ⟨hab, ?tailSortedCons⟩
      -- Need: IsCCCSorted ((b :: bs) ++ [x]).
      apply ih hrest
      intro y hy
      apply hbound
      exact List.mem_cons_of_mem a hy

/-- Inserting an element whose CCC is ≥ every element in `ys` yields
    `ys ++ [x]`. The classical insertion-sort "append-stable" step. -/
theorem insertByCCC_append_of_all_le (x : Nat) (ys : List Nat)
    (h : ∀ y ∈ ys, Lookup.canonicalCombiningClass y ≤ Lookup.canonicalCombiningClass x) :
    insertByCCC x ys = ys ++ [x] := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    unfold insertByCCC
    have hy : Lookup.canonicalCombiningClass y ≤ Lookup.canonicalCombiningClass x :=
      h y (by simp)
    have hnlt : ¬ Lookup.canonicalCombiningClass x < Lookup.canonicalCombiningClass y := by
      omega
    simp only [hnlt, ↓reduceIte]
    have hrest : ∀ z ∈ ys, Lookup.canonicalCombiningClass z
                            ≤ Lookup.canonicalCombiningClass x := fun z hz =>
      h z (List.mem_cons_of_mem y hz)
    rw [ih hrest]
    rfl

/-- Across a sorted list of the shape `pre ++ x :: rest`, every element
    of `pre` has CCC ≤ CCC(x). Top-level statement so the induction on
    `pre` carries the needed `hbridge` hypothesis without generalization
    gymnastics in the caller. -/
theorem ccc_sorted_pre_all_le_next {pre : List Nat} {x : Nat} {rest : List Nat}
    (h : IsCCCSorted (pre ++ x :: rest)) :
    ∀ y ∈ pre, Lookup.canonicalCombiningClass y ≤ Lookup.canonicalCombiningClass x := by
  induction pre with
  | nil => intro y hy; cases hy
  | cons a as ihp =>
    intro y hy
    simp only [List.mem_cons] at hy
    cases hy with
    | inl heq =>
      rw [heq]
      -- Goal: CCC(a) ≤ CCC(x). From h : IsCCCSorted (a :: (as ++ x :: rest))
      -- every tail element is ≥ CCC(a); x is in that tail.
      exact IsCCCSorted_head_le_all h x (by simp)
    | inr hy' =>
      -- Apply IH with the tail of h.
      exact ihp (IsCCCSorted_tail h) y hy'

/-- Generalized foldl lemma: folding `insertByCCC` over a suffix that is
    CCC-sorted with respect to a sorted prefix yields the concatenation.
    Generalization is necessary because the induction step grows the
    prefix by one element. -/
theorem insertByCCC_foldl_append (pre suf : List Nat)
    (hpre : IsCCCSorted pre)
    (hbridge : IsCCCSorted (pre ++ suf)) :
    suf.foldl (fun acc cp => insertByCCC cp acc) pre = pre ++ suf := by
  induction suf generalizing pre with
  | nil => simp
  | cons x rest ih =>
    show (x :: rest).foldl (fun acc cp => insertByCCC cp acc) pre
        = pre ++ (x :: rest)
    simp only [List.foldl_cons]
    -- Step 1: insertByCCC x pre = pre ++ [x], using the bridge sortedness.
    have hallLE : ∀ y ∈ pre, Lookup.canonicalCombiningClass y
                              ≤ Lookup.canonicalCombiningClass x :=
      ccc_sorted_pre_all_le_next hbridge
    rw [insertByCCC_append_of_all_le x pre hallLE]
    -- Step 2: apply IH with pre' = pre ++ [x] and suf' = rest.
    have hpre' : IsCCCSorted (pre ++ [x]) := by
      apply IsCCCSorted_append_right hpre
      exact hallLE
    have hbridge' : IsCCCSorted ((pre ++ [x]) ++ rest) := by
      have heq : (pre ++ [x]) ++ rest = pre ++ (x :: rest) := by
        rw [List.append_assoc]; rfl
      rw [heq]; exact hbridge
    -- Goal: foldl _ (pre ++ [x]) rest = pre ++ (x :: rest)
    -- IH gives: ... = (pre ++ [x]) ++ rest, which equals pre ++ (x :: rest).
    have := ih (pre ++ [x]) hpre' hbridge'
    rw [List.append_assoc] at this
    exact this

/-- `sortNonStarterRun run = run` when `run` is already CCC-sorted. The
    insertion-sort fixed-point theorem specialized to our CCC ordering. -/
theorem sortNonStarterRun_fixed_on_sorted (run : List Nat)
    (h : IsCCCSorted run) : sortNonStarterRun run = run := by
  unfold sortNonStarterRun
  have := insertByCCC_foldl_append [] run (by trivial) (by simpa using h)
  simpa using this

/-- In a CCC-sorted list of the shape `front ++ [last]`, every element
    of `front` has CCC ≤ CCC(last). The non-decreasing sort guarantees
    the last element is maximal. -/
theorem IsCCCSorted_front_le_last {front : List Nat} {last : Nat}
    (h : IsCCCSorted (front ++ [last])) :
    ∀ y ∈ front, Lookup.canonicalCombiningClass y
                   ≤ Lookup.canonicalCombiningClass last := by
  induction front with
  | nil => intro y hy; cases hy
  | cons a rest ih =>
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy'
    · apply IsCCCSorted_head_le_all h
      exact List.mem_append_right rest (by simp)
    · exact ih (IsCCCSorted_tail h) y hy'

-- ─────────────────────────────────────────────────────────────────────────────
--                                                     // reorder // idempotence
-- ─────────────────────────────────────────────────────────────────────────────

/-- `flushRun` on a state whose `currentRun.reverse` is CCC-sorted
    returns that reversed sequence unchanged — there is no reordering
    to do. -/
theorem flushRun_sorted_noop (s : ReorderState)
    (h : IsCCCSorted s.currentRun.reverse) :
    flushRun s = s.currentRun.reverse.toArray := by
  unfold flushRun
  rw [sortNonStarterRun_fixed_on_sorted s.currentRun.reverse h]

attribute [local irreducible] Lookup.canonicalCombiningClass

/-- Unfolding equation for `insertByCCC` on a non-empty list — exposes
    the internal if-then-else so the main proof can case-split without
    triggering the decidable-instance recursion that `unfold` inside
    `by_cases` otherwise causes. -/
theorem insertByCCC_cons (x y : Nat) (ys : List Nat) :
    insertByCCC x (y :: ys) =
      (if Lookup.canonicalCombiningClass x < Lookup.canonicalCombiningClass y
       then x :: y :: ys
       else y :: insertByCCC x ys) := rfl

/-- Inserting a codepoint into a CCC-sorted list via `insertByCCC`
    produces a CCC-sorted list — single-step insertion-sort correctness. -/
theorem insertByCCC_preserves_sorted (x : Nat) (ys : List Nat)
    (h : IsCCCSorted ys) : IsCCCSorted (insertByCCC x ys) := by
  induction ys with
  | nil => trivial
  | cons y ys ih =>
    rw [insertByCCC_cons]
    split
    next hlt =>
      exact ⟨Nat.le_of_lt hlt, h⟩
    next hnlt =>
      match hys : ys with
      | [] =>
        subst hys
        exact ⟨by omega, by trivial⟩
      | z :: zs =>
        subst hys
        have hzz : IsCCCSorted (insertByCCC x (z :: zs)) := ih h.2
        rw [insertByCCC_cons] at hzz
        rw [insertByCCC_cons]
        split at hzz
        · next hxz =>
          split
          · next hsplit => exact ⟨by omega, hzz⟩
          · next hxz' => exact absurd hxz hxz'
        · next hnxz =>
          split
          · next hxz' => exact absurd hxz' hnxz
          · next hsplit => exact ⟨h.1, hzz⟩

/-- `sortNonStarterRun` produces a CCC-sorted list — insertion-sort
    correctness: every output is CCC-non-decreasing. -/
theorem sortNonStarterRun_sorted (run : List Nat) :
    IsCCCSorted (sortNonStarterRun run) := by
  unfold sortNonStarterRun
  -- Fold insertByCCC over run starting from []. Maintain invariant:
  -- the accumulator is always CCC-sorted.
  suffices H : ∀ (acc : List Nat), IsCCCSorted acc →
      IsCCCSorted (run.foldl (fun a cp => insertByCCC cp a) acc) by
    exact H [] (by trivial)
  intro acc hacc
  induction run generalizing acc with
  | nil => simpa using hacc
  | cons r rs ih =>
    simp only [List.foldl_cons]
    exact ih (insertByCCC r acc) (insertByCCC_preserves_sorted r acc hacc)

/-- Intrinsic characterization of a reordered output: every consecutive
    pair `(x, y)` where `y` is a non-starter (`CCC(y) > 0`) satisfies
    `CCC(x) ≤ CCC(y)`. Because starters have `CCC = 0`, the inequality
    is vacuously satisfied when the predecessor is a starter; the real
    content is that consecutive non-starters are CCC-non-decreasing,
    i.e. each non-starter run is sorted. -/
def HasSortedRuns : List Nat → Prop
  | []          => True
  | [_]         => True
  | x :: y :: t =>
    (0 < Lookup.canonicalCombiningClass y →
      Lookup.canonicalCombiningClass x ≤ Lookup.canonicalCombiningClass y)
    ∧ HasSortedRuns (y :: t)

@[simp] theorem HasSortedRuns_nil : HasSortedRuns [] = True := rfl
@[simp] theorem HasSortedRuns_singleton (x : Nat) : HasSortedRuns [x] = True := rfl

theorem HasSortedRuns_cons_cons (x y : Nat) (t : List Nat) :
    HasSortedRuns (x :: y :: t)
      ↔ (0 < Lookup.canonicalCombiningClass y →
          Lookup.canonicalCombiningClass x ≤ Lookup.canonicalCombiningClass y)
         ∧ HasSortedRuns (y :: t) := Iff.rfl

/-- A sorted list with head dropped remains with sorted runs. -/
theorem HasSortedRuns_tail {x : Nat} {rest : List Nat}
    (h : HasSortedRuns (x :: rest)) : HasSortedRuns rest := by
  match rest with
  | []     => trivial
  | head :: tail => exact h.2

/-- A CCC-sorted list of non-starters has sorted runs — the inequality
    premise `CCC y > 0` is available; the conclusion follows from
    `IsCCCSorted` directly. -/
theorem HasSortedRuns_of_IsCCCSorted (xs : List Nat) (h : IsCCCSorted xs) :
    HasSortedRuns xs := by
  match xs with
  | []              => trivial
  | [single]        => trivial
  | x :: y :: rest =>
    obtain ⟨hxy, hrest⟩ := h
    refine ⟨fun hyPos => hxy, ?tailHsr⟩
    exact HasSortedRuns_of_IsCCCSorted (y :: rest) hrest

/-- Prepending a starter (CCC = 0) to a HasSortedRuns list preserves
    the property — the starter's CCC is 0, which is ≤ anything. -/
theorem HasSortedRuns_cons_starter {x : Nat} {rest : List Nat}
    (hccc : Lookup.canonicalCombiningClass x = 0)
    (h : HasSortedRuns rest) : HasSortedRuns (x :: rest) := by
  match rest with
  | [] => trivial
  | y :: ys =>
    refine ⟨fun hyPos => ?leZero, h⟩
    rw [hccc]
    exact Nat.zero_le (Lookup.canonicalCombiningClass y)

/-- Appending one element to a HasSortedRuns list preserves the
    property provided the bridge condition holds between the last
    element and the new one. -/
theorem HasSortedRuns_append_right {xs : List Nat} {x : Nat}
    (hxs : HasSortedRuns xs)
    (hbridge : ∀ last, xs = [] ∨ (∃ pre, xs = pre ++ [last]) →
                0 < Lookup.canonicalCombiningClass x →
                xs.getLast? = some last →
                Lookup.canonicalCombiningClass last
                  ≤ Lookup.canonicalCombiningClass x) :
    HasSortedRuns (xs ++ [x]) := by
  induction xs with
  | nil => trivial
  | cons a as ih =>
    match as with
    | [] =>
      -- xs = [a]. xs ++ [x] = [a, x].
      refine ⟨fun hcx => ?headLeX, by trivial⟩
      exact hbridge a (Or.inr ⟨[], rfl⟩) hcx rfl
    | b :: bs =>
      -- xs = a :: b :: bs. xs ++ [x] = a :: (b :: bs ++ [x]).
      refine ⟨hxs.1, ?tailHsr⟩
      apply ih hxs.2
      intro last hcase hcx hlast
      -- The "last" of (b :: bs) matches the "last" of (a :: b :: bs).
      apply hbridge last
      · rcases hcase with hnil | ⟨pre, hpre⟩
        · exact absurd hnil (List.cons_ne_nil b bs)
        · exact Or.inr ⟨a :: pre, by rw [hpre]; rfl⟩
      · exact hcx
      · simp [List.getLast?] at hlast ⊢
        exact hlast

/-- Dropping the last element of a HasSortedRuns list preserves the
    property — the consecutive-pair conditions on the remaining list
    are a subset of those on the full list. -/
theorem HasSortedRuns_of_append_singleton (xs : List Nat) (cp : Nat)
    (h : HasSortedRuns (xs ++ [cp])) : HasSortedRuns xs := by
  induction xs with
  | nil => trivial
  | cons a as ih =>
    match as with
    | [] => trivial
    | b :: bs =>
      refine ⟨h.1, ?tailHsr⟩
      exact ih h.2

/-- For a HasSortedRuns list of the form `xs ++ [cp]` where `cp` is a
    non-starter, the last element of `xs` (if it exists) has CCC ≤
    CCC(cp). -/
theorem HasSortedRuns_last_le {xs : List Nat} {cp : Nat}
    (h : HasSortedRuns (xs ++ [cp]))
    (hcp : 0 < Lookup.canonicalCombiningClass cp)
    (last : Nat) (hlast : xs.getLast? = some last) :
    Lookup.canonicalCombiningClass last
      ≤ Lookup.canonicalCombiningClass cp := by
  induction xs with
  | nil => cases hlast
  | cons a as ih =>
    match as with
    | [] =>
      have heq : last = a := by
        have : ([a] : List Nat).getLast? = some a := rfl
        rw [this] at hlast
        exact Option.some.inj hlast.symm
      subst heq
      exact h.1 hcp
    | b :: bs =>
      have htail : (b :: bs).getLast? = some last := by
        have : (a :: b :: bs).getLast? = (b :: bs).getLast? := rfl
        rw [this] at hlast
        exact hlast
      exact ih h.2 htail

/-- Non-empty list decomposition: every non-empty list can be written
    as a prefix followed by a single trailing element. -/
theorem List.exists_append_singleton_of_ne_nil {xs : List Nat} (hne : xs ≠ []) :
    ∃ front last, xs = front ++ [last] := by
  induction xs with
  | nil => exact absurd rfl hne
  | cons x rest ih =>
    match rest with
    | [] => exact ⟨[], x, rfl⟩
    | y :: more =>
      obtain ⟨front, last, heq⟩ := ih (by intro htail; cases htail)
      exact ⟨x :: front, last, by rw [heq]; rfl⟩

/-- Reverse (snoc) induction principle for lists — prove `motive xs`
    by showing it for `[]` and showing it is preserved by appending a
    single element. Derived via forward induction on `xs.reverse`
    because `List.reverseRecOn` is not in Lean 4 core under that name. -/
theorem list_snoc_induction {motive : List Nat → Prop}
    (hnil : motive [])
    (hsnoc : ∀ (xs : List Nat) (x : Nat), motive xs → motive (xs ++ [x])) :
    ∀ (xs : List Nat), motive xs := by
  intro xs
  have h_rev : ∀ (rxs : List Nat), motive rxs.reverse := by
    intro rxs
    induction rxs with
    | nil => exact hnil
    | cons x rest ih =>
      rw [List.reverse_cons]
      exact hsnoc rest.reverse x ih
  have : xs.reverse.reverse = xs := List.reverse_reverse xs
  rw [← this]
  exact h_rev xs.reverse

/-- `getLast?` of a snoc-shaped list returns the appended element. -/
theorem getLast?_append_singleton (xs : List Nat) (x : Nat) :
    (xs ++ [x]).getLast? = some x := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    match rest with
    | []              => rfl
    | b :: more       => exact ih

/-- The initial reorder state used by `reorder` at the start of the
    fold. Given a name so theorems can refer to it without repeating
    the anonymous record literal. -/
def initState : ReorderState := { emitted := #[], currentRun := [] }

/-- Evaluation lemma for `stepReorder` on a starter codepoint. -/
theorem stepReorder_starter (S : ReorderState) (cp : Nat)
    (hccc : Lookup.canonicalCombiningClass cp = 0) :
    stepReorder S cp
      = { emitted := S.emitted ++ flushRun S ++ #[cp], currentRun := [] } := by
  unfold stepReorder
  rw [if_pos hccc]

/-- Evaluation lemma for `stepReorder` on a non-starter codepoint. -/
theorem stepReorder_nonstarter (S : ReorderState) (cp : Nat)
    (hccc : Lookup.canonicalCombiningClass cp ≠ 0) :
    stepReorder S cp = { S with currentRun := cp :: S.currentRun } := by
  unfold stepReorder
  rw [if_neg hccc]

/-- Aggregate invariant carried by the reorder fold, kept as a single
    `Prop` so the `list_snoc_induction` motive is flat (no `let`). -/
def ReorderFoldInvariant (S : ReorderState) (xs : List Nat) : Prop :=
  S.emitted.toList ++ S.currentRun.reverse = xs
    ∧ IsCCCSorted S.currentRun.reverse
    ∧ (∀ x ∈ S.currentRun.reverse, 0 < Lookup.canonicalCombiningClass x)

/-- Starter-step preservation: when `cp` is a starter, stepping from a
    state satisfying the invariant for `xs` gives a state satisfying
    the invariant for `xs ++ [cp]`. -/
theorem reorderFoldInvariant_step_starter
    (S : ReorderState) (xs : List Nat) (cp : Nat)
    (hInv : ReorderFoldInvariant S xs)
    (hccc : Lookup.canonicalCombiningClass cp = 0) :
    ReorderFoldInvariant (stepReorder S cp) (xs ++ [cp]) := by
  obtain ⟨hP1, hP2, hP3⟩ := hInv
  rw [stepReorder_starter S cp hccc]
  have h_arr_eq : (S.emitted ++ S.currentRun.reverse.toArray ++ #[cp]).toList
                = S.emitted.toList ++ S.currentRun.reverse ++ [cp] := by
    rw [Array.toList_append, Array.toList_append]
  refine ⟨?stateEq, ?runSorted, ?runNonStarters⟩
  · show (S.emitted ++ flushRun S ++ #[cp]).toList ++ ([] : List Nat).reverse
        = xs ++ [cp]
    rw [List.reverse_nil, List.append_nil]
    rw [flushRun_sorted_noop S hP2]
    rw [h_arr_eq, hP1]
  · show IsCCCSorted ([] : List Nat).reverse
    rw [List.reverse_nil]
    trivial
  · intro x hx
    rw [List.reverse_nil] at hx
    cases hx

/-- Non-starter-step preservation. The "sorted pending run" invariant
    uses `HasSortedRuns (xs ++ [cp])` to derive that the previously
    buffered run's last element has CCC ≤ CCC(cp). -/
theorem reorderFoldInvariant_step_nonstarter
    (S : ReorderState) (xs : List Nat) (cp : Nat)
    (hInv : ReorderFoldInvariant S xs)
    (hccc : Lookup.canonicalCombiningClass cp ≠ 0)
    (hSR : HasSortedRuns (xs ++ [cp])) :
    ReorderFoldInvariant (stepReorder S cp) (xs ++ [cp]) := by
  obtain ⟨hP1, hP2, hP3⟩ := hInv
  have hcpPos : 0 < Lookup.canonicalCombiningClass cp := Nat.pos_of_ne_zero hccc
  rw [stepReorder_nonstarter S cp hccc]
  refine ⟨?stateEq, ?runSorted, ?runNonStarters⟩
  · show S.emitted.toList ++ (cp :: S.currentRun).reverse = xs ++ [cp]
    rw [List.reverse_cons]
    rw [← List.append_assoc, hP1]
  · show IsCCCSorted (cp :: S.currentRun).reverse
    rw [List.reverse_cons]
    apply IsCCCSorted_append_right hP2
    intro y hy
    have hNonempty : S.currentRun.reverse ≠ [] := fun heq => by
      rw [heq] at hy; cases hy
    obtain ⟨front, last, hfl⟩ :=
      List.exists_append_singleton_of_ne_nil hNonempty
    have hy' : y ∈ front ++ [last] := by rw [← hfl]; exact hy
    have hP2' : IsCCCSorted (front ++ [last]) := by rw [← hfl]; exact hP2
    have hxs_concat : xs = (S.emitted.toList ++ front) ++ [last] := by
      rw [← hP1, hfl, List.append_assoc]
    have hlast_xs : xs.getLast? = some last := by
      rw [hxs_concat]
      exact getLast?_append_singleton (S.emitted.toList ++ front) last
    have hlast_le : Lookup.canonicalCombiningClass last
                      ≤ Lookup.canonicalCombiningClass cp :=
      HasSortedRuns_last_le hSR hcpPos last hlast_xs
    rw [List.mem_append] at hy'
    rcases hy' with hyf | hys
    · have hy_le_last : Lookup.canonicalCombiningClass y
                          ≤ Lookup.canonicalCombiningClass last :=
        IsCCCSorted_front_le_last hP2' y hyf
      exact Nat.le_trans hy_le_last hlast_le
    · rw [List.mem_singleton] at hys
      subst hys
      exact hlast_le
  · intro x hx
    rw [List.reverse_cons] at hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hP3 x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact hcpPos

/-- Fold invariant on the reorder state machine. For a list `xs`
    satisfying `HasSortedRuns`, folding `stepReorder` over `xs` from
    `initState` produces a state `S` such that `S.emitted.toList ++
    S.currentRun.reverse` equals `xs`, the pending run is
    CCC-non-decreasing, and every buffered codepoint is a non-starter.
    The sorted-pending-run part makes `flushRun` on `S` the identity
    on that run, which lets the final `reorder` output reconstruct
    `xs` exactly. -/
theorem reorder_fold_invariant (xs : List Nat) (h : HasSortedRuns xs) :
    ReorderFoldInvariant (xs.foldl stepReorder initState) xs := by
  refine list_snoc_induction
    (motive := fun xs => HasSortedRuns xs →
      ReorderFoldInvariant (xs.foldl stepReorder initState) xs)
    ?baseNil ?inductiveSnoc xs h
  · intro hNil
    refine ⟨?stateEq, ?runSorted, ?runNonStarters⟩
    · rfl
    · trivial
    · intro x hx; cases hx
  · intro xs cp ih hSR
    have hxs : HasSortedRuns xs := HasSortedRuns_of_append_singleton xs cp hSR
    have hInv : ReorderFoldInvariant (xs.foldl stepReorder initState) xs :=
      ih hxs
    rw [List.foldl_append]
    show ReorderFoldInvariant
           (stepReorder (xs.foldl stepReorder initState) cp) (xs ++ [cp])
    by_cases hccc : Lookup.canonicalCombiningClass cp = 0
    · exact reorderFoldInvariant_step_starter
              (xs.foldl stepReorder initState) xs cp hInv hccc
    · exact reorderFoldInvariant_step_nonstarter
              (xs.foldl stepReorder initState) xs cp hInv hccc hSR

-- ═══════════════════════════════════════════════════════════════════════════════
-- REORDER IDEMPOTENCE
--
-- `reorder` applied twice equals `reorder` applied once. The proof builds
-- on `reorder_fold_invariant`: for any `xs` satisfying `HasSortedRuns`,
-- the fold's pending-run is already CCC-sorted, so `flushRun` is the
-- identity on it, and the final output reconstructs `xs`. Combined with
-- the fact that `reorder` output always satisfies `HasSortedRuns` (the
-- state machine produces exactly that structure), `reorder (reorder xs) =
-- reorder xs`.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `reorder` is the identity on any `Array Nat` whose list form already
    satisfies `HasSortedRuns`. Every fold step preserves the invariant
    from `reorder_fold_invariant`, and the final flush is a no-op on
    the already-sorted pending run. -/
theorem reorder_id_on_HasSortedRuns (cps : Array Nat)
    (h : HasSortedRuns cps.toList) : reorder cps = cps := by
  have hInv := reorder_fold_invariant cps.toList h
  obtain ⟨hP1, hP2, hP3⟩ := hInv
  rw [Array.foldl_toList] at hP1 hP2
  show ((cps.foldl stepReorder initState).emitted
          ++ flushRun (cps.foldl stepReorder initState)) = cps
  rw [flushRun_sorted_noop (cps.foldl stepReorder initState) hP2]
  apply Array.toList_inj.mp
  simp [Array.toList_append]
  exact hP1

/-- Concat lemma: if `pre ++ [starter]` is `HasSortedRuns`, `starter` is
    a starter (CCC = 0), and `run` is `IsCCCSorted`, then
    `pre ++ [starter] ++ run` is `HasSortedRuns`. Local structural argument:
    HSR is a constraint on consecutive pairs, and the only new pair
    introduced at the junction is `(starter, head run)`, which is
    satisfied because `CCC(starter) = 0 ≤ CCC(head run)`. -/
theorem HasSortedRuns_append_after_starter
    (pre : List Nat) (starter : Nat) (run : List Nat)
    (hStart : Lookup.canonicalCombiningClass starter = 0)
    (hRun : IsCCCSorted run) :
    HasSortedRuns (pre ++ [starter]) →
    HasSortedRuns (pre ++ [starter] ++ run) := by
  induction pre with
  | nil =>
    intro hPreHSR
    simp only [List.nil_append]
    cases run with
    | nil => trivial
    | cons r rs =>
      refine ⟨fun hccrPos => ?leZero, HasSortedRuns_of_IsCCCSorted (r :: rs) hRun⟩
      rw [hStart]; exact Nat.zero_le (Lookup.canonicalCombiningClass r)
  | cons p rest ih =>
    intro hFront
    cases rest with
    | nil =>
      simp only [List.nil_append, List.cons_append] at hFront ⊢
      cases run with
      | nil => exact hFront
      | cons r rs =>
        refine ⟨fun hStartPos => ?absurd, ?recur⟩
        · rw [hStart] at hStartPos; exact absurd hStartPos (Nat.lt_irrefl 0)
        · refine ⟨fun hccrPos => ?leZeroSecond, HasSortedRuns_of_IsCCCSorted (r :: rs) hRun⟩
          rw [hStart]; exact Nat.zero_le (Lookup.canonicalCombiningClass r)
    | cons r' rs' =>
      simp only [List.cons_append] at hFront ⊢
      obtain ⟨h1, hRestHSR⟩ := hFront
      refine ⟨h1, ?tailHsr⟩
      have := ih hRestHSR
      simp only [List.cons_append] at this
      exact this

/-- Output-side invariant on the reorder fold state. Unlike
    `ReorderFoldInvariant`, this holds for ANY input because it tracks
    only the shape produced by `stepReorder`: `emitted` is
    `HasSortedRuns` and either empty or ends with a starter;
    `currentRun` contains only non-starters. -/
def ReorderOutputInvariant (S : ReorderState) : Prop :=
  HasSortedRuns S.emitted.toList
    ∧ (S.emitted.toList = []
        ∨ ∃ pre last, S.emitted.toList = pre ++ [last]
                       ∧ Lookup.canonicalCombiningClass last = 0)
    ∧ (∀ x ∈ S.currentRun, 0 < Lookup.canonicalCombiningClass x)

/-- The empty initial state satisfies `ReorderOutputInvariant`. -/
theorem initState_output_invariant :
    ReorderOutputInvariant initState := by
  refine ⟨?emitHsr, ?emitEnd, ?runNonStarters⟩
  · trivial
  · left; rfl
  · intro x hx; cases hx

/-- Appending a starter to any `HasSortedRuns` list preserves the
    property — starters (CCC = 0) impose no constraint via the
    `0 < CCC y → ...` clause. -/
theorem HasSortedRuns_append_starter (xs : List Nat) (s : Nat)
    (hxs : HasSortedRuns xs)
    (hs : Lookup.canonicalCombiningClass s = 0) :
    HasSortedRuns (xs ++ [s]) := by
  apply HasSortedRuns_append_right hxs
  intro last hcase hCCC hlast
  rw [hs] at hCCC
  exact absurd hCCC (Nat.lt_irrefl 0)

/-- Per-step preservation of `ReorderOutputInvariant`. -/
theorem stepReorder_output_invariant (S : ReorderState) (cp : Nat)
    (hInv : ReorderOutputInvariant S) :
    ReorderOutputInvariant (stepReorder S cp) := by
  obtain ⟨hHSR, hEnd, hRun⟩ := hInv
  by_cases hccc : Lookup.canonicalCombiningClass cp = 0
  · rw [stepReorder_starter S cp hccc]
    have hFlushSortedList :
        IsCCCSorted (sortNonStarterRun S.currentRun.reverse) :=
      sortNonStarterRun_sorted S.currentRun.reverse
    have hFlushListEq :
        (flushRun S).toList = sortNonStarterRun S.currentRun.reverse := by
      unfold flushRun
      rfl
    have hEmittedPlusFlush :
        HasSortedRuns (S.emitted.toList ++ (flushRun S).toList) := by
      rw [hFlushListEq]
      rcases hEnd with hNil | ⟨pre, last, hAEq, hLast⟩
      · rw [hNil]
        simp
        exact HasSortedRuns_of_IsCCCSorted
          (sortNonStarterRun S.currentRun.reverse) hFlushSortedList
      · rw [hAEq]
        apply HasSortedRuns_append_after_starter pre last
          (sortNonStarterRun S.currentRun.reverse) hLast hFlushSortedList
        rw [← hAEq]; exact hHSR
    refine ⟨?emitHsr, ?emitEnd, ?runNonStarters⟩
    · show HasSortedRuns
        (S.emitted ++ flushRun S ++ #[cp]).toList
      rw [Array.toList_append, Array.toList_append]
      show HasSortedRuns
        (S.emitted.toList ++ (flushRun S).toList ++ [cp])
      exact HasSortedRuns_append_starter
        (S.emitted.toList ++ (flushRun S).toList) cp hEmittedPlusFlush hccc
    · right
      refine ⟨(S.emitted ++ flushRun S).toList, cp, ?listEq, hccc⟩
      rw [Array.toList_append, Array.toList_append]
    · intro x hx; cases hx
  · rw [stepReorder_nonstarter S cp hccc]
    have hcpPos : 0 < Lookup.canonicalCombiningClass cp := Nat.pos_of_ne_zero hccc
    refine ⟨hHSR, hEnd, ?runNonStartersNs⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hRest
    · exact hcpPos
    · exact hRun x hRest

/-- The full fold preserves `ReorderOutputInvariant`, starting from
    `initState`. -/
theorem foldl_stepReorder_output_invariant (xs : List Nat) :
    ReorderOutputInvariant (xs.foldl stepReorder initState) := by
  refine list_snoc_induction
    (motive := fun xs => ReorderOutputInvariant (xs.foldl stepReorder initState))
    ?baseNil ?inductiveSnoc xs
  · exact initState_output_invariant
  · intro pre cp ih
    rw [List.foldl_append]
    exact stepReorder_output_invariant (pre.foldl stepReorder initState) cp ih

/-- **Output has sorted runs.** The output of `reorder` on any input
    satisfies `HasSortedRuns`. Combined with
    `reorder_id_on_HasSortedRuns`, this yields `reorder_idempotent`. -/
theorem reorder_output_HasSortedRuns (cps : Array Nat) :
    HasSortedRuns (reorder cps).toList := by
  have hInv := foldl_stepReorder_output_invariant cps.toList
  rw [Array.foldl_toList] at hInv
  obtain ⟨hHSR, hEnd, hRun⟩ := hInv
  show HasSortedRuns
    ((cps.foldl stepReorder initState).emitted ++
      flushRun (cps.foldl stepReorder initState)).toList
  rw [Array.toList_append]
  have hFlushSortedList :
      IsCCCSorted
        (sortNonStarterRun (cps.foldl stepReorder initState).currentRun.reverse) :=
    sortNonStarterRun_sorted (cps.foldl stepReorder initState).currentRun.reverse
  have hFlushListEq :
      (flushRun (cps.foldl stepReorder initState)).toList =
        sortNonStarterRun (cps.foldl stepReorder initState).currentRun.reverse := by
    unfold flushRun
    rfl
  rw [hFlushListEq]
  rcases hEnd with hNil | ⟨pre, last, hAEq, hLast⟩
  · rw [hNil]
    simp
    exact HasSortedRuns_of_IsCCCSorted
      (sortNonStarterRun (cps.foldl stepReorder initState).currentRun.reverse)
      hFlushSortedList
  · rw [hAEq]
    apply HasSortedRuns_append_after_starter pre last
      (sortNonStarterRun (cps.foldl stepReorder initState).currentRun.reverse)
      hLast hFlushSortedList
    rw [← hAEq]; exact hHSR

/-- **`reorder` is idempotent.** Applying `reorder` twice equals applying
    it once: the output always has sorted runs, and `reorder` is the
    identity on sorted-runs inputs. -/
theorem reorder_idempotent (cps : Array Nat) :
    reorder (reorder cps) = reorder cps :=
  reorder_id_on_HasSortedRuns (reorder cps) (reorder_output_HasSortedRuns cps)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty input reorders to empty. -/
theorem reorder_empty : reorder #[] = #[] := by native_decide

/-- Pure-starter input passes through unchanged (no non-starter runs). -/
theorem reorder_ascii :
    reorder #[0x0048, 0x0069] = #[0x0048, 0x0069] := by native_decide  -- "Hi"

/-- Already-sorted non-starter run is unchanged. COMBINING CEDILLA
    (CCC = 202) followed by COMBINING GRAVE ACCENT (CCC = 230) is
    canonical order. -/
theorem reorder_already_sorted :
    reorder #[0x0041, 0x0327, 0x0300]
      = #[0x0041, 0x0327, 0x0300] := by native_decide

/-- Out-of-order non-starters get swapped. GRAVE (230) then CEDILLA
    (202) should reorder to CEDILLA then GRAVE. -/
theorem reorder_swap :
    reorder #[0x0041, 0x0300, 0x0327]
      = #[0x0041, 0x0327, 0x0300] := by native_decide

/-- Stability: GRAVE (230) and ACUTE (230) both have CCC = 230. Their
    relative scan order must be preserved even after reorder passes
    against a lower-CCC mark. -/
theorem reorder_stable_equal_ccc :
    reorder #[0x0041, 0x0300, 0x0301, 0x0327]
      = #[0x0041, 0x0327, 0x0300, 0x0301] := by native_decide

/-- Starter boundary: a starter between two non-starter runs partitions
    the sort; runs are sorted independently. -/
theorem reorder_starter_partition :
    reorder #[0x0041, 0x0300, 0x0327, 0x0042, 0x0300, 0x0327]
      = #[0x0041, 0x0327, 0x0300, 0x0042, 0x0327, 0x0300] := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- MEMBERSHIP PRESERVATION
--
-- Canonical reordering permutes its input without introducing new codepoints.
-- The downstream PRECIS proofs need the specialization: any Bool predicate `P`
-- that holds on every input codepoint also holds on every output codepoint.
-- Proven by building `P` up through the reordering stages (`insertByCCC`,
-- `sortNonStarterRun`, `stepReorder`, the final `foldl` plus flush).
-- ═══════════════════════════════════════════════════════════════════════════════

section PropertyPreservation

variable (P : Nat → Bool)

/-- Inserting an element into a CCC-sorted list preserves a universal
    Bool predicate: every output element is either the inserted one or
    one already present. -/
theorem insertByCCC_preserves_all (x : Nat) (ys : List Nat)
    (hX : P x = true) (hYs : ∀ y ∈ ys, P y = true) :
    ∀ z ∈ insertByCCC x ys, P z = true := by
  induction ys with
  | nil =>
    intro z hz
    simp [insertByCCC] at hz
    rw [hz]
    exact hX
  | cons hd tl ih =>
    intro z hz
    unfold insertByCCC at hz
    split at hz
    · rcases List.mem_cons.mp hz with hZX | hZRest
      · rw [hZX]; exact hX
      · exact hYs z hZRest
    · rcases List.mem_cons.mp hz with hZHd | hZTail
      · rw [hZHd]; exact hYs hd (by simp)
      · exact ih (fun y hY => hYs y (by simp [hY])) z hZTail

/-- `sortNonStarterRun` preserves a universal Bool predicate. -/
theorem sortNonStarterRun_preserves_all (run : List Nat)
    (h : ∀ x ∈ run, P x = true) :
    ∀ z ∈ sortNonStarterRun run, P z = true := by
  unfold sortNonStarterRun
  have key : ∀ (l : List Nat) (acc : List Nat),
      (∀ x ∈ l, P x = true) → (∀ x ∈ acc, P x = true) →
      ∀ z ∈ l.foldl (fun sorted cp => insertByCCC cp sorted) acc, P z = true := by
    intro l
    induction l with
    | nil =>
      intro acc hL hAcc z hz
      simpa using hAcc z hz
    | cons hd tl ih =>
      intro acc hL hAcc z hz
      simp only [List.foldl_cons] at hz
      apply ih (insertByCCC hd acc)
      · intro y hy; exact hL y (by simp [hy])
      · exact insertByCCC_preserves_all P hd acc (hL hd (by simp)) hAcc
      · exact hz
  exact key run [] h (fun x hz => by simp at hz)

/-- `flushRun` output elements are all drawn from the state's `currentRun`. -/
theorem flushRun_preserves_all (s : ReorderState)
    (h : ∀ x ∈ s.currentRun, P x = true) :
    ∀ z ∈ flushRun s, P z = true := by
  unfold flushRun
  intro z hz
  rw [List.mem_toArray] at hz
  apply sortNonStarterRun_preserves_all P s.currentRun.reverse
  · intro y hy
    rw [List.mem_reverse] at hy
    exact h y hy
  · exact hz

/-- `stepReorder` propagates: if all emitted+currentRun elements and the
    input `cp` satisfy `P`, then the successor state's emitted+currentRun
    elements also satisfy `P`. -/
theorem stepReorder_preserves_all (s : ReorderState) (cp : Nat)
    (hEmit : ∀ x ∈ s.emitted, P x = true)
    (hRun : ∀ x ∈ s.currentRun, P x = true) (hCp : P cp = true) :
    (∀ x ∈ (stepReorder s cp).emitted, P x = true)
      ∧ (∀ x ∈ (stepReorder s cp).currentRun, P x = true) := by
  unfold stepReorder
  split
  · refine ⟨?emitAll, ?runEmpty⟩
    · intro x hx
      simp at hx
      rcases hx with h1 | h2 | h3
      · exact hEmit x h1
      · exact flushRun_preserves_all P s hRun x h2
      · rw [h3]; exact hCp
    · intro x hx; simp at hx
  · refine ⟨hEmit, ?runAll⟩
    intro x hx
    simp at hx
    rcases hx with hCpEq | hRest
    · rw [hCpEq]; exact hCp
    · exact hRun x hRest

/-- `reorder` preserves a universal Bool predicate: every output codepoint
    satisfies `P` whenever every input codepoint does. -/
theorem reorder_preserves_all (cps : Array Nat)
    (h : ∀ cp ∈ cps, P cp = true) :
    ∀ j ∈ reorder cps, P j = true := by
  unfold reorder
  have hFold : (∀ x ∈ (cps.foldl stepReorder initState).emitted, P x = true)
                ∧ (∀ x ∈ (cps.foldl stepReorder initState).currentRun, P x = true) := by
    rw [← Array.foldl_toList]
    have key : ∀ (l : List Nat) (s : ReorderState),
        (∀ x ∈ l, P x = true) →
        (∀ x ∈ s.emitted, P x = true) → (∀ x ∈ s.currentRun, P x = true) →
        (∀ x ∈ (l.foldl stepReorder s).emitted, P x = true)
          ∧ (∀ x ∈ (l.foldl stepReorder s).currentRun, P x = true) := by
      intro l
      induction l with
      | nil =>
        intro s hL hE hR
        exact ⟨hE, hR⟩
      | cons hd tl ih =>
        intro s hL hE hR
        simp only [List.foldl_cons]
        obtain ⟨hE', hR'⟩ := stepReorder_preserves_all P s hd hE hR (hL hd (by simp))
        exact ih (stepReorder s hd) (fun y hy => hL y (by simp [hy])) hE' hR'
    exact key cps.toList initState (fun x hx => h x (by simpa using hx))
      (fun x hz => by simp [initState] at hz) (fun x hz => by simp [initState] at hz)
  intro j hj
  rcases Array.mem_append.mp hj with hLeft | hRight
  · exact hFold.1 j hLeft
  · exact flushRun_preserves_all P (cps.foldl stepReorder initState) hFold.2 j hRight

end PropertyPreservation

end Unicode.Normalization.Reorder
