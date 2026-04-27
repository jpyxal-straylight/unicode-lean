/-
  Unicode.Normalization.Distribute

  Append-distribution helpers for concatMap-style normalization stages.
  Both `decomposeSequence` and `caseFold` are realized as a `foldl` that
  appends a per-codepoint expansion to an accumulator:

      F xs = xs.foldl (fun acc cp => acc ++ f cp) #[]

  These functions distribute over array concatenation:

      F (xs ++ ys) = F xs ++ F ys

  This module proves that distribution property once, parameterised in
  the per-codepoint expansion `f`, then specialises it to
  `decomposeSequence` (via `fullCanonicalDecompose`) and the
  `caseFold` fold (via `caseFoldCodepoint`).

  The lemmas are standalone foundations for a sequence-level lift of
  the pointwise `caseFold_commutes_with_NFD_singleton` identity in
  `CaseFoldCommutation.lean`; they do not themselves depend on
  `Reorder` or the CaseFolding / UnicodeData tables, and compile in
  milliseconds.
-/

import Unicode.Normalization.Decompose
import Unicode.Normalization.Decomposability
import Unicode.Normalization.NFD
import Unicode.Precis.CaseMapping

namespace Unicode.Normalization.Distribute

-- ═══════════════════════════════════════════════════════════════════════════════
-- GENERIC CONCATMAP-FOLDL DISTRIBUTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The init value of a `foldl (fun acc cp => acc ++ f cp) init ys` accumulates
    at the front: it equals `init ++ (foldl with #[] init)`. -/
theorem foldl_append_init
    (f : Nat → Array Nat) (ys : Array Nat) (init : Array Nat) :
    ys.foldl (fun acc cp => acc ++ f cp) init
      = init ++ ys.foldl (fun acc cp => acc ++ f cp) #[] := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  have key : ∀ (l : List Nat) (init : Array Nat),
      l.foldl (fun acc cp => acc ++ f cp) init
        = init ++ l.foldl (fun acc cp => acc ++ f cp) #[] := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons hd tl ih =>
      intro init
      simp only [List.foldl_cons]
      rw [ih (init ++ f hd), ih (#[] ++ f hd)]
      simp [Array.append_assoc]
  exact key ys.toList init

/-- **Generic `foldl` append-distribution.** For any per-codepoint expansion
    `f : Nat → Array Nat`, the `foldl` that appends `f cp` distributes over
    array concatenation. -/
theorem foldl_append_distribute
    (f : Nat → Array Nat) (xs ys : Array Nat) :
    (xs ++ ys).foldl (fun acc cp => acc ++ f cp) #[]
      = xs.foldl (fun acc cp => acc ++ f cp) #[]
        ++ ys.foldl (fun acc cp => acc ++ f cp) #[] := by
  rw [Array.foldl_append]
  rw [foldl_append_init f ys (xs.foldl (fun acc cp => acc ++ f cp) #[])]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SPECIALISATION: decomposeSequence
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **`decomposeSequence` distributes over `++`.** Immediate specialisation of
    `foldl_append_distribute` to `Decompose.fullCanonicalDecompose`. -/
theorem decomposeSequence_append (xs ys : Array Nat) :
    Decompose.decomposeSequence (xs ++ ys) =
      Decompose.decomposeSequence xs ++ Decompose.decomposeSequence ys := by
  unfold Decompose.decomposeSequence
  exact foldl_append_distribute Decompose.fullCanonicalDecompose xs ys

-- ═══════════════════════════════════════════════════════════════════════════════
-- SPECIALISATION: caseFold
-- ═══════════════════════════════════════════════════════════════════════════════

open Unicode.Precis.CaseMapping

/-- **`caseFold` distributes over `++`.** Immediate specialisation of
    `foldl_append_distribute` to `caseFoldCodepoint`. -/
theorem caseFold_append (xs ys : Array Nat) :
    caseFold (xs ++ ys) = caseFold xs ++ caseFold ys := by
  unfold caseFold
  exact foldl_append_distribute caseFoldCodepoint xs ys

-- ═══════════════════════════════════════════════════════════════════════════════
-- SINGLETON EXPANSIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `decomposeSequence` on a singleton is the per-codepoint full canonical
    decomposition. -/
theorem decomposeSequence_singleton (cp : Nat) :
    Decompose.decomposeSequence #[cp] = Decompose.fullCanonicalDecompose cp := by
  unfold Decompose.decomposeSequence
  simp

/-- `caseFold` on a singleton is the per-codepoint case fold. -/
theorem caseFold_singleton (cp : Nat) :
    caseFold #[cp] = caseFoldCodepoint cp := by
  unfold caseFold
  simp

-- ═══════════════════════════════════════════════════════════════════════════════
-- DECOMPOSESEQUENCE IDEMPOTENCE
--
-- `decomposeSequence` applied twice equals once. Follows directly from
-- `decomposeSequence_fullyDecomposed` (output is fully decomposed) and
-- `decomposeSequence_id_on_FullyDecomposed` (identity on fully-decomposed input).
--
-- Foundation for the sequence lift of `caseFold_commutes_with_NFD_singleton`:
-- the pointwise commutation uses `decomposeSequence #[cp] = fullCanonicalDecompose cp`,
-- and idempotence of `decomposeSequence` is what lets us strip the outer decompose
-- in `decomposeSequence (caseFold (decomposeSequence xs))`.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **`decomposeSequence` is idempotent.** Applying `decomposeSequence` twice
    equals applying it once. Composed from the existing `Decomposability`
    output-fully-decomposed theorem with the `NFD` identity-on-fully-decomposed
    theorem. -/
theorem decomposeSequence_idempotent (xs : Array Nat) :
    Decompose.decomposeSequence (Decompose.decomposeSequence xs)
      = Decompose.decomposeSequence xs := by
  exact Unicode.Normalization.NFD.decomposeSequence_id_on_FullyDecomposed
    (Decompose.decomposeSequence xs)
    (Decomposability.decomposeSequence_fullyDecomposed xs)

end Unicode.Normalization.Distribute
