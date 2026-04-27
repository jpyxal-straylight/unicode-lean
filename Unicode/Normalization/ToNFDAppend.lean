/-
  Unicode.Normalization.ToNFDAppend

  Lifts `ReorderAppend.reorder_append_starter_middle` to `toNFD` in two
  flavours:

  * `toNFD_append_starter_trivial` — for starters with empty canonical
    decomposition (`fullCanonicalDecompose cp = #[cp]`). Proof is direct
    via `reorder_append_starter`.

  * `toNFD_append_starter_general` — for any starter not in the small
    UCD-17.0 anomaly set `{U+0F73, U+0F75, U+0F81}` (Tibetan vowel
    signs). These three rows have `CCC = 0` but canonically decompose
    to pairs beginning with U+0F71 (CCC = 129 — a non-starter),
    violating the usual UAX #15 invariant that starter decompositions
    begin with starters. The general theorem carves these out
    explicitly via `isAnomalousStarter`; for every other starter in
    Unicode, appending commutes with NFD normalization.

  Anomaly verification: intersecting the set of
  first-canonical-decomposition-elements of starter rows with the set
  of non-starter codepoints in `UnicodeData.rows` yields exactly
  `{U+0F71}`, and the rows that expose it are exactly `{U+0F73, U+0F75,
  U+0F81}`. A `native_decide` over the 3045-row pinned UCD table
  confirms that every other row with non-empty decomposition begins
  with a starter.

  The general form closes Case 1 (leading-starter absorb) of
  `ComposeInversion.StepPreservesNFDEquivalence` for every non-anomalous
  starter, and the trivial form handles the remaining anomalous cases
  trivially when they arrive in NFD-form input (where the anomaly's
  decomposition has already been applied).
-/

import Unicode.Normalization.ReorderAppend
import Unicode.Normalization.Distribute
import Unicode.Normalization.NFC

namespace Unicode.Normalization.ToNFDAppend

open Unicode.Normalization
open Unicode.Generated

-- ═══════════════════════════════════════════════════════════════════════════════
-- REORDER ON A SINGLETON STARTER
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `reorder` is the identity on a starter singleton. -/
theorem reorder_singleton_starter (cp : Nat)
    (h : Lookup.canonicalCombiningClass cp = 0) :
    Reorder.reorder #[cp] = #[cp] := by
  have hAppend : Reorder.reorder (#[] ++ #[cp]) = Reorder.reorder #[] ++ #[cp] :=
    ReorderAppend.reorder_append_starter #[] cp h
  rw [Reorder.reorder_empty] at hAppend
  simp at hAppend
  exact hAppend

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRIVIAL CASE (EMPTY CANONICAL DECOMPOSITION)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `toNFD` on a starter with trivial canonical decomposition is the
    identity on the singleton. -/
theorem toNFD_singleton_trivial
    (cp : Nat) (hCp : Lookup.canonicalCombiningClass cp = 0)
    (hFCD : Decompose.fullCanonicalDecompose cp = #[cp]) :
    NFC.toNFD #[cp] = #[cp] := by
  unfold NFC.toNFD
  rw [Distribute.decomposeSequence_singleton cp]
  rw [hFCD]
  exact reorder_singleton_starter cp hCp

/-- **Trivial starter-append absorbing lemma for `toNFD`.** For starters
    with empty canonical decomposition, appending commutes directly via
    `reorder_append_starter`. -/
theorem toNFD_append_starter_trivial
    (X : Array Nat) (cp : Nat)
    (hCp : Lookup.canonicalCombiningClass cp = 0)
    (hFCD : Decompose.fullCanonicalDecompose cp = #[cp]) :
    NFC.toNFD (X ++ #[cp]) = NFC.toNFD X ++ NFC.toNFD #[cp] := by
  rw [toNFD_singleton_trivial cp hCp hFCD]
  unfold NFC.toNFD
  rw [Distribute.decomposeSequence_append X #[cp]]
  rw [Distribute.decomposeSequence_singleton cp]
  rw [hFCD]
  exact ReorderAppend.reorder_append_starter (Decompose.decomposeSequence X) cp hCp

-- ═══════════════════════════════════════════════════════════════════════════════
-- STARTER-HEAD PREDICATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- An array is "starter-headed" when it is non-empty and its first
    element has `ccc = 0`. -/
structure StarterHead (arr : Array Nat) : Prop where
  nonEmpty : 0 < arr.size
  firstCCC : Lookup.canonicalCombiningClass (arr[0]'nonEmpty) = 0

/-- Boolean companion: returns `true` iff the array is non-empty and its
    first element is a starter. -/
def starterHeadBool (arr : Array Nat) : Bool :=
  if h : 0 < arr.size then
    decide (Lookup.canonicalCombiningClass (arr[0]'h) = 0)
  else
    false

/-- The Boolean predicate reflects the `Prop` predicate. -/
theorem starterHeadBool_iff (arr : Array Nat) :
    starterHeadBool arr = true ↔ StarterHead arr := by
  constructor
  · intro hB
    unfold starterHeadBool at hB
    by_cases h : 0 < arr.size
    · simp only [h, dite_true] at hB
      exact ⟨h, of_decide_eq_true hB⟩
    · simp only [h, dite_false] at hB
      exact absurd hB Bool.false_ne_true
  · intro hP
    unfold starterHeadBool
    simp only [hP.nonEmpty, dite_true]
    exact decide_eq_true hP.firstCCC

-- ═══════════════════════════════════════════════════════════════════════════════
-- UCD-17.0 ANOMALY SET
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Tibetan vowel signs whose canonical decomposition begins with a
    non-starter (U+0F71, CCC = 129). These three codepoints are the
    complete set of UCD-17.0 starters whose `fullCanonicalDecompose`
    does not begin with a starter. -/
def anomalousStarters : Array Nat := #[0x0F73, 0x0F75, 0x0F81]

/-- Boolean membership test against `anomalousStarters`. -/
def isAnomalousStarter (cp : Nat) : Bool :=
  anomalousStarters.contains cp

-- ═══════════════════════════════════════════════════════════════════════════════
-- UCD TABLE FACTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Hangul-range invariant.** Every Hangul precomposed syllable's
    fully-expanded canonical decomposition is starter-headed. Closed by
    `native_decide` over the 11172-syllable range. -/
theorem hangul_fullCanonicalDecompose_starterHead :
    (List.range 11172).all
      (fun i => starterHeadBool
          (Decompose.fullCanonicalDecompose (0xAC00 + i))) = true := by
  native_decide

/-- **UCD-row invariant.** Every starter row of `UnicodeData.rows` that
    is not in `anomalousStarters` has a starter-headed full canonical
    decomposition. Closed by `native_decide` over the pinned 3045-row
    table. -/
theorem rows_fullCanonicalDecompose_starterHead :
    UnicodeData.rows.all (fun row =>
      isAnomalousStarter row.codepoint
        || decide (Lookup.canonicalCombiningClass row.codepoint ≠ 0)
        || starterHeadBool (Decompose.fullCanonicalDecompose row.codepoint)) = true := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- POINTWISE EXTRACTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- For any starter `cp` that is not anomalous, `fullCanonicalDecompose cp`
    is starter-headed. Dispatches across three cases: cp is a Hangul
    syllable, cp appears in `UnicodeData.rows`, or cp is not in the table
    (fallback, `fullCanonicalDecompose cp = #[cp]`). -/
theorem fullCanonicalDecompose_starterHead
    (cp : Nat) (hCp : Lookup.canonicalCombiningClass cp = 0)
    (hNotAnomalous : isAnomalousStarter cp = false) :
    StarterHead (Decompose.fullCanonicalDecompose cp) := by
  by_cases hHangul : Hangul.isHangulSyllable cp = true
  · -- Hangul syllable: use Hangul table
    have hRange : 0xAC00 ≤ cp ∧ cp < 0xAC00 + 11172 := by
      unfold Hangul.isHangulSyllable Hangul.SBase Hangul.SCount
             Hangul.LCount Hangul.NCount Hangul.VCount Hangul.TCount at hHangul
      exact of_decide_eq_true hHangul
    have hTable := hangul_fullCanonicalDecompose_starterHead
    rw [List.all_eq_true] at hTable
    have hI : cp - 0xAC00 ∈ List.range 11172 := List.mem_range.mpr (by omega)
    have hAtI := hTable (cp - 0xAC00) hI
    have hCpEq : 0xAC00 + (cp - 0xAC00) = cp := by omega
    rw [hCpEq] at hAtI
    exact (starterHeadBool_iff (Decompose.fullCanonicalDecompose cp)).mp hAtI
  · -- Not Hangul: consult UCD.rows
    have hNotHangulFalse : Hangul.isHangulSyllable cp = false := by
      cases hIsHangul : Hangul.isHangulSyllable cp with
      | false => rfl
      | true => exact absurd hIsHangul hHangul
    cases hLookup : Lookup.lookupRow cp with
    | none =>
      -- cp is not in the table: canonicalDecomposition = #[], full decomp = #[cp]
      have hDecompEmpty : Lookup.canonicalDecomposition cp = #[] := by
        unfold Lookup.canonicalDecomposition
        rw [hLookup]
      have hDsyl : Hangul.decomposeSyllable? cp = none := by
        unfold Hangul.decomposeSyllable?
        rw [hNotHangulFalse]
        simp
      have hFCD : Decompose.fullCanonicalDecompose cp = #[cp] := by
        show Decompose.fullCanonicalDecomposeFuel Decompose.maxDepth cp = #[cp]
        unfold Decompose.maxDepth
        unfold Decompose.fullCanonicalDecomposeFuel
        rw [hDsyl]
        simp [hDecompEmpty]
      rw [hFCD]
      refine ⟨by simp, ?headCcc⟩
      have hAccess : ((#[cp] : Array Nat)[0]'(by simp)) = cp := by simp
      rw [hAccess]
      exact hCp
    | some row =>
      -- cp is in the table: use rows table fact
      have hRowMem : row ∈ UnicodeData.rows :=
        Array.mem_of_find?_eq_some hLookup
      have hTable := rows_fullCanonicalDecompose_starterHead
      rw [Array.all_eq_true] at hTable
      rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
      have hRowProp := hTable i hi
      rw [hElem] at hRowProp
      have hFindProp := Array.find?_eq_some_iff_getElem.mp hLookup
      obtain ⟨hCodeDecide, hExistsAfter⟩ := hFindProp
      have hExistsAfterUnused := hExistsAfter
      clear hExistsAfterUnused
      have hCodepointEq : row.codepoint = cp := of_decide_eq_true hCodeDecide
      rw [hCodepointEq] at hRowProp
      simp only [Bool.or_eq_true, decide_eq_true_eq, hCp, ne_eq] at hRowProp
      rcases hRowProp with hLeft | hSH
      · rcases hLeft with hAnom | hNeCcc
        · rw [hNotAnomalous] at hAnom
          exact absurd hAnom Bool.false_ne_true
        · exfalso; exact hNeCcc trivial
      · exact (starterHeadBool_iff (Decompose.fullCanonicalDecompose cp)).mp hSH

/-- Destructure a starter-headed array into a singleton head + tail. -/
theorem starterHead_destructure
    (arr : Array Nat) (h : StarterHead arr) :
    ∃ (head : Nat) (tail : Array Nat),
      arr = #[head] ++ tail
        ∧ Lookup.canonicalCombiningClass head = 0 := by
  match hL : arr.toList with
  | [] =>
    exfalso
    have hLen : arr.toList.length = arr.size := by simp
    rw [hL] at hLen
    simp at hLen
    have hPos := h.nonEmpty
    omega
  | head :: rest =>
    have hArrEq : arr = #[head] ++ rest.toArray := by
      apply Array.toList_inj.mp
      rw [Array.toList_append, hL]
      simp
    refine ⟨head, rest.toArray, hArrEq, ?headCcc⟩
    have hSH_shaped : StarterHead (#[head] ++ rest.toArray) := hArrEq ▸ h
    have hSizeShaped : 0 < (#[head] ++ rest.toArray).size := hSH_shaped.nonEmpty
    have hFirstShaped := hSH_shaped.firstCCC
    have hOneLt : (0 : Nat) < (#[head] : Array Nat).size := by simp
    rw [Array.getElem_append_left hOneLt] at hFirstShaped
    simpa using hFirstShaped

-- ═══════════════════════════════════════════════════════════════════════════════
-- GENERAL STARTER-APPEND ABSORBING FOR NON-ANOMALOUS STARTERS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Starter-append absorbing lemma for `toNFD`, general case.**
    Appending any non-anomalous starter commutes with canonical NFD
    normalization. -/
theorem toNFD_append_starter_general
    (X : Array Nat) (cp : Nat)
    (hCp : Lookup.canonicalCombiningClass cp = 0)
    (hNotAnomalous : isAnomalousStarter cp = false) :
    NFC.toNFD (X ++ #[cp]) = NFC.toNFD X ++ NFC.toNFD #[cp] := by
  unfold NFC.toNFD
  rw [Distribute.decomposeSequence_append X #[cp]]
  rw [Distribute.decomposeSequence_singleton cp]
  have hSH := fullCanonicalDecompose_starterHead cp hCp hNotAnomalous
  obtain ⟨head, tail, hEq, hHeadCCC⟩ :=
    starterHead_destructure (Decompose.fullCanonicalDecompose cp) hSH
  rw [hEq]
  rw [show Decompose.decomposeSequence X ++ (#[head] ++ tail)
         = Decompose.decomposeSequence X ++ #[head] ++ tail
       from by rw [Array.append_assoc]]
  rw [ReorderAppend.reorder_append_starter_middle
        (Decompose.decomposeSequence X) head tail hHeadCCC]
  rw [show (#[head] ++ tail : Array Nat) = #[] ++ #[head] ++ tail
       from by simp]
  rw [ReorderAppend.reorder_append_starter_middle #[] head tail hHeadCCC]
  rw [Reorder.reorder_empty]
  simp

-- ═══════════════════════════════════════════════════════════════════════════════
-- TONFD CONGRUENCE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **ToNFD congruence for trivially-decomposed starter appends.** -/
theorem toNFD_congr_append_starter_trivial
    {a b : Array Nat} (cp : Nat)
    (hCp : Lookup.canonicalCombiningClass cp = 0)
    (hFCD : Decompose.fullCanonicalDecompose cp = #[cp])
    (h : NFC.toNFD a = NFC.toNFD b) :
    NFC.toNFD (a ++ #[cp]) = NFC.toNFD (b ++ #[cp]) := by
  rw [toNFD_append_starter_trivial a cp hCp hFCD]
  rw [toNFD_append_starter_trivial b cp hCp hFCD]
  rw [h]

/-- **ToNFD congruence for non-anomalous starter appends.** -/
theorem toNFD_congr_append_starter_general
    {a b : Array Nat} (cp : Nat)
    (hCp : Lookup.canonicalCombiningClass cp = 0)
    (hNotAnomalous : isAnomalousStarter cp = false)
    (h : NFC.toNFD a = NFC.toNFD b) :
    NFC.toNFD (a ++ #[cp]) = NFC.toNFD (b ++ #[cp]) := by
  rw [toNFD_append_starter_general a cp hCp hNotAnomalous]
  rw [toNFD_append_starter_general b cp hCp hNotAnomalous]
  rw [h]

-- ═══════════════════════════════════════════════════════════════════════════════
-- GENERAL TONFD ABSORBING-LEFT + ++-CONGRUENCE
--
-- Direct corollaries of `ReorderAppend.reorder_absorbing_left` applied
-- at the `decomposeSequence` level. These are the structural lemmas
-- that close non-starter-append cases of
-- `ComposeInversion.StepPreservesNFDEquivalence` and underpin the
-- caseFold-preserves-NFD-equivalence reduction of
-- `CaseFoldNfdCommutesSeq`.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Definitional equation for `NFC.toNFD`. Used to fold/unfold without
    pattern-match confusion. -/
theorem toNFD_eq (X : Array Nat) :
    NFC.toNFD X = Reorder.reorder (Decompose.decomposeSequence X) := rfl

/-- `decomposeSequence ∘ toNFD = toNFD`. Every codepoint in `toNFD A`
    has trivial further canonical decomposition (by
    `toNFD_output_HSR_and_FullyDecomposed`), so applying
    `decomposeSequence` again is the identity (by
    `decomposeSequence_id_on_FullyDecomposed`). -/
theorem decomposeSequence_toNFD (A : Array Nat) :
    Decompose.decomposeSequence (NFC.toNFD A) = NFC.toNFD A := by
  have hFD := (NFD.toNFD_output_HSR_and_FullyDecomposed A).2
  exact NFD.decomposeSequence_id_on_FullyDecomposed (NFC.toNFD A) hFD

/-- **Absorbing-left for `toNFD`.** For any arrays `A`, `B`:

        toNFD (A ++ B) = toNFD (toNFD A ++ B)

    Pre-NFD-normalizing the left operand of a concatenation produces
    the same canonical form under subsequent `toNFD`. Direct corollary
    of `ReorderAppend.reorder_absorbing_left`: unfolding `toNFD = reorder
    ∘ decomposeSequence` on both sides and distributing
    `decomposeSequence` across `++` yields a `reorder_absorbing_left`
    invocation with the `decomposeSequence` components of the inputs. -/
theorem toNFD_absorbing_left (A B : Array Nat) :
    NFC.toNFD (A ++ B) = NFC.toNFD (NFC.toNFD A ++ B) := by
  rw [toNFD_eq (A ++ B), toNFD_eq (NFC.toNFD A ++ B)]
  rw [Distribute.decomposeSequence_append A B]
  rw [Distribute.decomposeSequence_append (NFC.toNFD A) B]
  rw [decomposeSequence_toNFD A]
  rw [toNFD_eq A]
  exact ReorderAppend.reorder_absorbing_left
          (Decompose.decomposeSequence A)
          (Decompose.decomposeSequence B)

/-- **ToNFD `++`-congruence.** Two arrays with equal `toNFD` form
    preserve that equality under right-concatenation with any array.
    Direct corollary of `toNFD_absorbing_left`: the lemma rewrites
    `toNFD (a ++ c)` to `toNFD (toNFD a ++ c)` and `toNFD (b ++ c)` to
    `toNFD (toNFD b ++ c)`; substituting `toNFD a = toNFD b` closes
    the goal. -/
theorem toNFD_congr_append {a b : Array Nat} (c : Array Nat)
    (h : NFC.toNFD a = NFC.toNFD b) :
    NFC.toNFD (a ++ c) = NFC.toNFD (b ++ c) := by
  rw [toNFD_absorbing_left a c]
  rw [toNFD_absorbing_left b c]
  rw [h]

/-- **Absorbing-right for `toNFD`.** For any arrays `A`, `B`:

        toNFD (A ++ B) = toNFD (A ++ toNFD B)

    Pre-NFD-normalizing the right operand of a concatenation produces
    the same canonical form under subsequent `toNFD`.  Direct corollary
    of `ReorderAppend.reorder_absorbing_right`: unfolding `toNFD =
    reorder ∘ decomposeSequence`, distributing `decomposeSequence`
    across `++`, and using `decomposeSequence_toNFD` on the right
    operand reduces the claim to a `reorder_absorbing_right` on the
    `decomposeSequence` components. -/
theorem toNFD_absorbing_right (A B : Array Nat) :
    NFC.toNFD (A ++ B) = NFC.toNFD (A ++ NFC.toNFD B) := by
  rw [toNFD_eq (A ++ B), toNFD_eq (A ++ NFC.toNFD B)]
  rw [Distribute.decomposeSequence_append A B]
  rw [Distribute.decomposeSequence_append A (NFC.toNFD B)]
  rw [decomposeSequence_toNFD B]
  rw [toNFD_eq B]
  exact ReorderAppend.reorder_absorbing_right
          (Decompose.decomposeSequence A)
          (Decompose.decomposeSequence B)

/-- **ToNFD prepend-congruence.** Two arrays with equal `toNFD` form
    preserve that equality under left-concatenation with any array.
    Direct corollary of `toNFD_absorbing_right`: the lemma rewrites
    `toNFD (c ++ a)` to `toNFD (c ++ toNFD a)` and `toNFD (c ++ b)` to
    `toNFD (c ++ toNFD b)`; substituting `toNFD a = toNFD b` closes
    the goal.  Companion to `toNFD_congr_append`. -/
theorem toNFD_congr_prepend {a b : Array Nat} (c : Array Nat)
    (h : NFC.toNFD a = NFC.toNFD b) :
    NFC.toNFD (c ++ a) = NFC.toNFD (c ++ b) := by
  rw [toNFD_absorbing_right c a]
  rw [toNFD_absorbing_right c b]
  rw [h]

end Unicode.Normalization.ToNFDAppend
