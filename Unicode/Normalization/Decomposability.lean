/-
  Unicode.Normalization.Decomposability

  Structural witness that `fullCanonicalDecompose` output is fully
  decomposed — every resulting codepoint has no further canonical
  decomposition and is not a Hangul syllable. Upstream, this establishes
  `IsFullyDecomposed` on `decomposeSequence` output, the key precondition
  for feeding `compose` (pillar 2 of NFC idempotence).

  Architecture: the two `native_decide` table facts here cover the
  interesting codepoints — rows of `UnicodeData` (3045 cases) and Hangul
  syllables (11172 cases). Codepoints outside both sets decompose
  trivially to themselves, and the non-decomposability of the trivial
  case is established structurally.
-/

import Unicode.Normalization.Decompose

namespace Unicode.Normalization.Decomposability

open Unicode.Normalization
open Unicode.Generated

-- ═══════════════════════════════════════════════════════════════════════════════
-- TABLE-LEVEL WITNESSES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- For every row in `UnicodeData.rows`, the full canonical decomposition
    of its codepoint produces output codepoints that all have no further
    canonical decomposition and are not Hangul syllables. Closed by
    `native_decide` over the 3045 rows with fuel = 32 (well above the
    maximum canonical chain depth of 4 in UCD 17.0). -/
theorem rows_decompose_fullyDecomposed :
    UnicodeData.rows.all (fun row =>
      (Decompose.fullCanonicalDecompose row.codepoint).all (fun cp =>
        decide (Lookup.canonicalDecomposition cp = #[]
                ∧ Hangul.isHangulSyllable cp = false))) = true := by
  native_decide

/-- Every Hangul syllable's canonical decomposition produces only jamo
    codepoints that have no canonical decomposition and are not Hangul
    syllables themselves. Closed by `native_decide` over the 11172-
    syllable range. -/
theorem hangul_decompose_fullyDecomposed :
    (List.range 11172).all (fun i =>
      (Decompose.fullCanonicalDecompose (0xAC00 + i)).all (fun cp =>
        decide (Lookup.canonicalDecomposition cp = #[]
                ∧ Hangul.isHangulSyllable cp = false))) = true := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- POINTWISE WITNESS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Pointwise: for any codepoint `cp`, every element of
    `fullCanonicalDecompose cp` has no further canonical decomposition
    and is not a Hangul syllable. Case analysis:

    * Hangul syllable (`isHangulSyllable cp = true`): output is a jamo
      sequence; covered by `hangul_decompose_fullyDecomposed`.
    * Non-Hangul with empty canonical decomposition: output is `#[cp]`
      itself; the conjunction holds trivially from the case hypothesis.
    * Non-Hangul with non-empty canonical decomposition: `cp` must be a
      row in `UnicodeData.rows` (only rows carry non-empty
      decompositions); covered by `rows_decompose_fullyDecomposed`. -/
theorem fullCanonicalDecompose_fullyDecomposed (cp : Nat) :
    ∀ j ∈ Decompose.fullCanonicalDecompose cp,
      Lookup.canonicalDecomposition j = #[] ∧ Hangul.isHangulSyllable j = false := by
  intro j hj
  by_cases hHangul : Hangul.isHangulSyllable cp = true
  · -- Hangul case: use the Hangul table fact.
    have hRange : 0xAC00 ≤ cp ∧ cp < 0xAC00 + 11172 := by
      unfold Hangul.isHangulSyllable Hangul.SBase Hangul.SCount
             Hangul.LCount Hangul.NCount Hangul.VCount Hangul.TCount at hHangul
      exact of_decide_eq_true hHangul
    have hTable := hangul_decompose_fullyDecomposed
    rw [List.all_eq_true] at hTable
    have hiLt : cp - 0xAC00 < 11172 := by omega
    have hCpEq : 0xAC00 + (cp - 0xAC00) = cp := by omega
    have hIdx : (cp - 0xAC00) ∈ List.range 11172 := List.mem_range.mpr hiLt
    have hAt := hTable (cp - 0xAC00) hIdx
    rw [hCpEq] at hAt
    rw [Array.all_eq_true] at hAt
    rcases Array.getElem_of_mem hj with ⟨i, hi, hElem⟩
    have hJProp := hAt i hi
    rw [hElem] at hJProp
    exact of_decide_eq_true hJProp
  · -- Non-Hangul case: use the UnicodeData rows fact or triviality.
    -- Either cp is in rows (then rows table fact applies) or not (then
    -- fullCanonicalDecompose cp = #[cp] and the property reduces to
    -- canonicalDecomposition cp = #[] ∧ isHangulSyllable cp = false).
    by_cases hRow : ∃ row, row ∈ UnicodeData.rows ∧ row.codepoint = cp
    · -- cp is a row codepoint.
      obtain ⟨row, hRowMem, hRowEq⟩ := hRow
      have hTable := rows_decompose_fullyDecomposed
      rw [Array.all_eq_true] at hTable
      rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
      have hAt := hTable i hi
      rw [hElem] at hAt
      rw [Array.all_eq_true] at hAt
      rw [hRowEq] at hAt
      rcases Array.getElem_of_mem hj with ⟨k, hk, hElemJ⟩
      have hJProp := hAt k hk
      rw [hElemJ] at hJProp
      exact of_decide_eq_true hJProp
    · -- cp is not in rows: fullCanonicalDecompose cp = #[cp].
      have hRowNone : ∀ row ∈ UnicodeData.rows, row.codepoint ≠ cp := by
        intro row hMem heq
        exact hRow ⟨row, hMem, heq⟩
      have hLookup : Lookup.lookupRow cp = none := by
        unfold Lookup.lookupRow
        rw [Array.find?_eq_none]
        intro row hMem
        have hNe : row.codepoint ≠ cp := hRowNone row hMem
        simp [hNe]
      have hDecomp : Lookup.canonicalDecomposition cp = #[] := by
        unfold Lookup.canonicalDecomposition
        rw [hLookup]
      have hNotHangul : Hangul.isHangulSyllable cp = false :=
        Bool.not_eq_true (Hangul.isHangulSyllable cp) |>.mp hHangul
      have hDsyl : Hangul.decomposeSyllable? cp = none := by
        unfold Hangul.decomposeSyllable?
        rw [hNotHangul]
        simp
      -- fullCanonicalDecompose cp reduces to #[cp].
      have hFCD : Decompose.fullCanonicalDecompose cp = #[cp] := by
        show Decompose.fullCanonicalDecomposeFuel Decompose.maxDepth cp = #[cp]
        unfold Decompose.maxDepth
        unfold Decompose.fullCanonicalDecomposeFuel
        rw [hDsyl]
        simp [hDecomp]
      rw [hFCD] at hj
      simp at hj
      rw [hj]
      exact ⟨hDecomp, hNotHangul⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- SEQUENCE-LEVEL WITNESS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Generic: membership in a `foldl`-with-append over an array factors
    through one of the source elements. (Local copy of the private helper
    from `Decompose`; kept here to avoid modifying that module.) -/
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

/-- `decomposeSequence` output is fully decomposed. Lifted from the
    per-codepoint witness via `mem_foldl_append`. -/
theorem decomposeSequence_fullyDecomposed (cps : Array Nat) :
    ∀ j ∈ Decompose.decomposeSequence cps,
      Lookup.canonicalDecomposition j = #[] ∧ Hangul.isHangulSyllable j = false := by
  intro j hj
  unfold Decompose.decomposeSequence at hj
  obtain ⟨x, hxInCps, hxF⟩ :=
    mem_foldl_append Decompose.fullCanonicalDecompose cps j hj
  clear hxInCps
  exact fullCanonicalDecompose_fullyDecomposed x j hxF

end Unicode.Normalization.Decomposability
