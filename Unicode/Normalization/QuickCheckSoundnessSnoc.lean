/-
  Unicode.Normalization.QuickCheckSoundnessSnoc

  Snoc-induction support for `isNFCQuickCheck` soundness (UAX #15 §A.1).

  The companion `QuickCheckSoundness` module ships:
    * the empty-paragraph case (`empty_sound`)
    * the singleton-nonstarter case (`singleton_sound_nonstarter`)
    * the three Fact lifts (Fact 1 inlined; Fact 2 imported; Fact 3 proved here).

  This module fills in the structural foundation that the full snoc
  induction needs:

    * `hasSortedRunsBool` is preserved under prefix-truncation of a
      cons-cons list (§1).
    * `isNFCQuickCheck` is preserved when a trailing element is
      stripped from the input (§2).
    * Two more singleton-starter base cases close the singleton family
      modulo the size-`> 2` decomposition cases:
        - empty canonical decomposition (§3)
        - size-2 canonical decomposition that recomposes via Fact 2 (§4)

  The inductive step over `cps = xs ++ #[cp]` consumes the
  prefix-preservation lemma below (reducing the hypothesis on `xs ++
  #[cp]` to one on `xs`), the singleton cases (per-step closure for
  the three `cp` shapes), and `ToNFDAppend.toNFD_absorbing_right` /
  `toNFD_append_starter_general` (factoring `toNFD (xs ++ #[cp])`).
-/

import Unicode.Normalization.QuickCheckSoundness
import Unicode.Normalization.QuickCheckFacts
import Unicode.Normalization.NFC
import Unicode.Normalization.NFD
import Unicode.Normalization.Compose
import Unicode.Normalization.Decompose
import Unicode.Normalization.Reorder
import Unicode.Normalization.Hangul
import Unicode.Normalization.Distribute

namespace Unicode.Normalization.QuickCheckSoundnessSnoc

open Unicode.Normalization
open Unicode.Normalization.NFC
  (toNFC toNFD isNFCQuickCheck hasSortedRunsBool nfcQCValue)
open Unicode.Normalization.QuickCheckFacts
  (qcY_nonstarter_cp_no_decomp qcY_starter_2decomp_cp_composes)

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1 HASSORTEDRUNSBOOL PREFIX PRESERVATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `hasSortedRunsBool` on a `cons-cons` head pair decomposes through
    the cons-cons unfolding equation and Boolean conjunction. Used as
    the base lemma for cons-prefix truncation. -/
theorem hasSortedRunsBool_cons_tail
    (x y : Nat) (t : List Nat)
    (h : hasSortedRunsBool (x :: y :: t) = true) :
    hasSortedRunsBool (y :: t) = true := by
  have eq : hasSortedRunsBool (x :: y :: t) =
      ((decide (Lookup.canonicalCombiningClass y = 0) ||
        decide (Lookup.canonicalCombiningClass x
                  ≤ Lookup.canonicalCombiningClass y))
        && hasSortedRunsBool (y :: t)) := by
    unfold hasSortedRunsBool
    simp [List.tail_cons, List.zip_cons_cons]
  rw [eq] at h
  rw [Bool.and_eq_true] at h
  exact h.2

/-- A `hasSortedRunsBool` truth on `x :: rest` carries to `rest`
    when `rest` is non-empty. The empty-rest case is trivial: any
    singleton list is HSR-true. -/
theorem hasSortedRunsBool_tail
    (x : Nat) (rest : List Nat)
    (h : hasSortedRunsBool (x :: rest) = true) :
    hasSortedRunsBool rest = true := by
  cases rest with
  | nil      => unfold hasSortedRunsBool; rfl
  | cons y t => exact hasSortedRunsBool_cons_tail x y t h

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2 ISNFCQUICKCHECK PREFIX PRESERVATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `Array.all` membership: every element of an `Array.all = true`
    array satisfies the predicate. -/
theorem array_all_of_mem (arr : Array Nat) (p : Nat → Bool)
    (h : arr.all p = true) : ∀ x ∈ arr, p x = true := by
  rw [Array.all_eq_true] at h
  intro x hx
  rcases Array.getElem_of_mem hx with ⟨i, hi, hElem⟩
  have := h i hi
  rw [hElem] at this
  exact this

/-- `Array.all` on an `xs ++ #[cp]` is true iff every member of `xs`
    satisfies the predicate AND `cp` does. The forward direction is
    the form needed to strip the trailing element. -/
theorem all_append_singleton_of_all
    (xs : Array Nat) (cp : Nat) (p : Nat → Bool)
    (h : (xs ++ #[cp]).all p = true) :
    xs.all p = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hMem : xs[i] ∈ xs ++ #[cp] := by
    apply Array.mem_append.mpr
    left
    exact Array.getElem_mem hi
  exact array_all_of_mem (xs ++ #[cp]) p h xs[i] hMem

/-- Helper: every pair in the zip-with-tail of `l` is also in the
    zip-with-tail of `l ++ [x]`. The append `[x]` adds at most one new
    boundary pair `(last l, x)`; existing pairs are preserved. -/
theorem zipTail_pair_mem_append_singleton {α : Type _}
    (l : List α) (x : α) (pair : α × α)
    (h : pair ∈ l.zip l.tail) :
    pair ∈ (l ++ [x]).zip (l ++ [x]).tail := by
  induction l with
  | nil =>
    simp at h
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp at h
    | cons hd2 tl2 =>
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at h
      simp only [List.cons_append, List.tail_cons, List.zip_cons_cons,
                 List.mem_cons]
      rcases h with hHead | hTail
      · exact Or.inl hHead
      · exact Or.inr (ih hTail)

/-- `hasSortedRunsBool` on `(xs ++ #[cp]).toList` carries to `xs.toList`.
    The `++ #[cp]` step appends at most one new boundary pair to the
    zip-with-tail; every pre-existing pair satisfies the predicate by
    hypothesis, so the prefix's predicate-conjunction holds too. -/
theorem hasSortedRunsBool_dropLast
    (xs : Array Nat) (cp : Nat)
    (h : hasSortedRunsBool (xs ++ #[cp]).toList = true) :
    hasSortedRunsBool xs.toList = true := by
  unfold hasSortedRunsBool at h ⊢
  have hCpList : (#[cp] : Array Nat).toList = [cp] := rfl
  rw [Array.toList_append, hCpList] at h
  rw [List.all_eq_true] at h ⊢
  intro pair hPair
  exact h pair (zipTail_pair_mem_append_singleton xs.toList cp pair hPair)

/-- The full prefix-preservation: `isNFCQuickCheck` truth on
    `xs ++ #[cp]` carries to `xs`. -/
theorem isNFCQuickCheck_dropLast
    (xs : Array Nat) (cp : Nat)
    (h : isNFCQuickCheck (xs ++ #[cp]) = true) :
    isNFCQuickCheck xs = true := by
  unfold isNFCQuickCheck at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  obtain ⟨hAll, hHSR⟩ := h
  refine ⟨?prefixAllQcY, ?prefixHsr⟩
  · exact all_append_singleton_of_all xs cp
      (fun cp => decide (nfcQCValue cp = .Y)) hAll
  · exact hasSortedRunsBool_dropLast xs cp hHSR

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3 SINGLETON STARTER WITH EMPTY CANONICAL DECOMPOSITION
--
-- A QC=Y starter `cp` whose canonical decomposition is empty AND that
-- is not a Hangul precomposed syllable is its own NFC. CCC=0
-- specialization of the singleton-nonstarter case (§3 of the
-- companion module).
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Singleton starter, empty decomposition.** A QC=Y starter codepoint
    whose canonical decomposition is empty and that is not a Hangul
    precomposed syllable is in NFC unchanged. -/
theorem singleton_sound_atomic
    (cp : Nat)
    (hCcc : Lookup.canonicalCombiningClass cp = 0)
    (hDecomp : Lookup.canonicalDecomposition cp = #[])
    (hNotHangul : Hangul.isHangulSyllable cp = false) :
    toNFC #[cp] = #[cp] := by
  -- decomposeSequence #[cp] = #[cp]
  have hDsyl : Hangul.decomposeSyllable? cp = none := by
    unfold Hangul.decomposeSyllable?
    rw [hNotHangul]
    simp
  have hFCD : Decompose.fullCanonicalDecompose cp = #[cp] := by
    show Decompose.fullCanonicalDecomposeFuel Decompose.maxDepth cp = #[cp]
    unfold Decompose.maxDepth Decompose.fullCanonicalDecomposeFuel
    rw [hDsyl]
    simp [hDecomp]
  have hDS : Decompose.decomposeSequence #[cp] = #[cp] := by
    rw [Distribute.decomposeSequence_singleton]
    exact hFCD
  -- reorder #[cp] = #[cp]
  have hR : Reorder.reorder #[cp] = #[cp] := by
    apply Reorder.reorder_id_on_HasSortedRuns
    show Reorder.HasSortedRuns [cp]
    trivial
  -- compose on a single starter: emit it directly.
  show Compose.compose (toNFD #[cp]) = #[cp]
  unfold toNFD
  rw [hDS, hR]
  unfold Compose.compose Compose.flushCompose Compose.stepCompose
         Compose.initialState
  simp [hCcc]

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4 SINGLETON STARTER WITH SIZE-2 CANONICAL DECOMPOSITION
--
-- A QC=Y starter with a size-2 canonical decomposition recomposes via
-- Fact 2: `primaryComposite? d e = some cp` for `[d, e] = canonical
-- decomp of cp`. The singleton case is the cleanest application of
-- this fact and is a building block for the snoc induction.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Singleton starter, size-2 decomposition.** A QC=Y starter whose
    canonical decomposition is `#[d, e]` with `d` a starter and `e` a
    nonstarter recomposes back to `cp` under the NFC pipeline.

    The proof unfolds the pipeline, applies `decomposeSequence_singleton`
    to expose `[d, e]`, observes that `[d, e]` is HSR (single-element
    nonstarter run), then closes via Fact 2 inside `compose`.

    Provided as a documented theorem statement; the proof reduces to
    the same computation that `Lookup.canonicalDecomposition`-based
    test vectors close via `native_decide`. -/
theorem singleton_sound_pair
    (cp d e : Nat)
    (hQC : nfcQCValue cp = .Y)
    (hCcc : Lookup.canonicalCombiningClass cp = 0)
    (hDecomp : Lookup.canonicalDecomposition cp = #[d, e]) :
    Compose.primaryComposite? d e = some cp := by
  have hSize : (Lookup.canonicalDecomposition cp).size = 2 := by
    rw [hDecomp]; rfl
  have hLift := qcY_starter_2decomp_cp_composes cp hQC hCcc hSize
  rw [hDecomp] at hLift
  -- hLift now reads: primaryComposite? (#[d,e][0]!) (#[d,e][1]!) = some cp.
  -- The two array indices reduce to d and e.
  have h0 : (#[d, e] : Array Nat)[0]! = d := by simp
  have h1 : (#[d, e] : Array Nat)[1]! = e := by simp
  rw [h0, h1] at hLift
  exact hLift

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4b SINGLETON HANGUL PRECOMPOSED SYLLABLE
--
-- For every Hangul precomposed syllable `cp` in the range
-- `0xAC00 .. 0xD7A3`, the NFC pipeline is the identity on `#[cp]`:
-- the algorithmic decomposition produces L+V or L+V+T jamo, the reorder
-- stage is identity (jamo are starters), and the compose stage's
-- `Hangul.composePair?` recombines the jamo back into the original
-- syllable. Closed by `native_decide` over the 11172-syllable range.
-- ═══════════════════════════════════════════════════════════════════════════════

theorem hangul_singleton_nfc_id_table :
    (List.range Hangul.SCount).all
      (fun i => decide (toNFC #[Hangul.SBase + i] = #[Hangul.SBase + i])) = true := by
  native_decide

/-- **Singleton Hangul.** Every Hangul precomposed syllable is in NFC
    form unchanged. -/
theorem singleton_sound_hangul (cp : Nat)
    (hHangul : Hangul.isHangulSyllable cp = true) :
    toNFC #[cp] = #[cp] := by
  have hRange : Hangul.SBase ≤ cp ∧ cp < Hangul.SBase + Hangul.SCount := by
    unfold Hangul.isHangulSyllable Hangul.SBase Hangul.SCount
           Hangul.LCount Hangul.NCount Hangul.VCount Hangul.TCount at hHangul
    exact of_decide_eq_true hHangul
  have hIdxLt : cp - Hangul.SBase < Hangul.SCount := by omega
  have hCpEq : Hangul.SBase + (cp - Hangul.SBase) = cp := by omega
  have hTable := hangul_singleton_nfc_id_table
  rw [List.all_eq_true] at hTable
  have hI : cp - Hangul.SBase ∈ List.range Hangul.SCount :=
    List.mem_range.mpr hIdxLt
  have hAt := hTable (cp - Hangul.SBase) hI
  rw [hCpEq] at hAt
  exact of_decide_eq_true hAt

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4c SINGLETON STARTER, SIZE-2 DECOMPOSITION — FULL PIPELINE
--
-- Strengthens §4 from the `primaryComposite? d e = some cp` conclusion
-- to the full pipeline identity `toNFC #[cp] = #[cp]`. The proof
-- evaluates each pipeline stage on the singleton:
--
--   * `fullCanonicalDecompose cp = #[d, e]` (via Hangul-gate + decomp
--     recursion at depth 32 → 31, with `d, e` atomic),
--   * `reorder #[d, e] = #[d, e]` (HSR is trivial: starter + single
--     non-starter run),
--   * `compose #[d, e] = #[cp]` (state machine: starter `d` registers,
--     non-starter `e` triggers `primaryComposite? d e = some cp`).
--
-- The atomicity hypotheses on `d` and `e` (empty canonical decomposition,
-- not Hangul) are UCD-level facts about how canonical pairs are
-- structured: every QC=Y starter's canonical pair components are
-- themselves atomic. The master theorem will discharge them via a
-- table-level `native_decide` over `UnicodeData.rows`.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Singleton starter, size-2 decomposition: full NFC identity.**
    Strengthens `singleton_sound_pair` to the
    full pipeline conclusion `toNFC #[cp] = #[cp]`. -/
theorem singleton_sound_pair_full
    (cp d e : Nat)
    (hQC : nfcQCValue cp = .Y)
    (hCcc : Lookup.canonicalCombiningClass cp = 0)
    (hDecomp : Lookup.canonicalDecomposition cp = #[d, e])
    (hDStarter : Lookup.canonicalCombiningClass d = 0)
    (hENonStarter : 0 < Lookup.canonicalCombiningClass e)
    (hNotHangul : Hangul.isHangulSyllable cp = false)
    (hDDecompEmpty : Lookup.canonicalDecomposition d = #[])
    (hEDecompEmpty : Lookup.canonicalDecomposition e = #[])
    (hDNotHangul : Hangul.isHangulSyllable d = false)
    (hENotHangul : Hangul.isHangulSyllable e = false) :
    toNFC #[cp] = #[cp] := by
  -- Fact 2: primaryComposite? d e = some cp.
  have hPC := singleton_sound_pair cp d e hQC hCcc hDecomp
  -- Hangul gates: cp, d, e are all not Hangul precomposed syllables.
  have hDsylCp : Hangul.decomposeSyllable? cp = none := by
    unfold Hangul.decomposeSyllable?; rw [hNotHangul]; simp
  have hDsylD : Hangul.decomposeSyllable? d = none := by
    unfold Hangul.decomposeSyllable?; rw [hDNotHangul]; simp
  have hDsylE : Hangul.decomposeSyllable? e = none := by
    unfold Hangul.decomposeSyllable?; rw [hENotHangul]; simp
  -- Atomic decomposition for d and e at fuel 31.
  have hFCD_d_31 : Decompose.fullCanonicalDecomposeFuel 31 d = #[d] := by
    unfold Decompose.fullCanonicalDecomposeFuel
    rw [hDsylD]; simp [hDDecompEmpty]
  have hFCD_e_31 : Decompose.fullCanonicalDecomposeFuel 31 e = #[e] := by
    unfold Decompose.fullCanonicalDecomposeFuel
    rw [hDsylE]; simp [hEDecompEmpty]
  -- cp at fuel 32 → none branch, decomp = #[d, e], foldl over the pair.
  have hFCD_cp : Decompose.fullCanonicalDecompose cp = #[d, e] := by
    show Decompose.fullCanonicalDecomposeFuel Decompose.maxDepth cp = #[d, e]
    unfold Decompose.maxDepth
    show Decompose.fullCanonicalDecomposeFuel 32 cp = #[d, e]
    unfold Decompose.fullCanonicalDecomposeFuel
    rw [hDsylCp]
    simp only []
    rw [hDecomp]
    show ((#[d, e] : Array Nat).foldl
            (fun acc cp' => acc ++ Decompose.fullCanonicalDecomposeFuel 31 cp') #[])
        = #[d, e]
    have hFold : (#[d, e] : Array Nat).foldl
            (fun acc cp' => acc ++ Decompose.fullCanonicalDecomposeFuel 31 cp') #[]
          = (#[] ++ Decompose.fullCanonicalDecomposeFuel 31 d) ++
              Decompose.fullCanonicalDecomposeFuel 31 e := rfl
    rw [hFold, hFCD_d_31, hFCD_e_31]
    rfl
  -- decomposeSequence #[cp] = #[d, e].
  have hDS : Decompose.decomposeSequence #[cp] = #[d, e] := by
    rw [Distribute.decomposeSequence_singleton]
    exact hFCD_cp
  -- HSR on [d, e]: starter premise discharges the inequality.
  have hHSR : Reorder.HasSortedRuns [d, e] := by
    refine ⟨?starterImplication, ?singletonRun⟩
    · intro hENs
      clear hENs
      rw [hDStarter]
      exact Nat.zero_le (Lookup.canonicalCombiningClass e)
    · trivial
  have hR : Reorder.reorder #[d, e] = #[d, e] := by
    apply Reorder.reorder_id_on_HasSortedRuns
    show Reorder.HasSortedRuns [d, e]
    exact hHSR
  -- Pipeline assembly: toNFC = compose ∘ toNFD = compose ∘ reorder ∘ decomposeSequence.
  show Compose.compose (toNFD #[cp]) = #[cp]
  unfold toNFD
  rw [hDS, hR]
  -- Goal: compose #[d, e] = #[cp].
  unfold Compose.compose
  show Compose.flushCompose
        ((#[d, e] : Array Nat).foldl Compose.stepCompose Compose.initialState) = #[cp]
  have hFold2 : (#[d, e] : Array Nat).foldl Compose.stepCompose Compose.initialState
              = Compose.stepCompose (Compose.stepCompose Compose.initialState d) e := by
    rw [← Array.foldl_toList]
    show ([d, e] : List Nat).foldl Compose.stepCompose Compose.initialState
       = Compose.stepCompose (Compose.stepCompose Compose.initialState d) e
    simp only [List.foldl_cons, List.foldl_nil]
  rw [hFold2]
  -- Step 1: stepCompose initialState d. Starter is none, ccc d = 0 → register d.
  have hStep1 : Compose.stepCompose Compose.initialState d
              = { emitted := #[], starter := some d, buffer := [], maxCCC := 0 } := by
    unfold Compose.stepCompose Compose.initialState
    rw [hDStarter]
    rfl
  rw [hStep1]
  -- Step 2: stepCompose with starter = some d, ccc e > 0, buffer empty.
  -- ccc e ≠ 0, ccc e > maxCCC = 0, primaryComposite? d e = some cp → register cp.
  have hENotZero : Lookup.canonicalCombiningClass e ≠ 0 := Nat.ne_of_gt hENonStarter
  have hENotLeMax : ¬ (Lookup.canonicalCombiningClass e ≤ 0) := by
    intro hLe; omega
  have hStep2 : Compose.stepCompose
                  { emitted := #[], starter := some d, buffer := [], maxCCC := 0 } e
              = { emitted := #[], starter := some cp, buffer := [], maxCCC := 0 } := by
    unfold Compose.stepCompose
    simp only [hENotZero, ↓reduceIte, hENotLeMax, hPC]
  rw [hStep2]
  -- Step 3: flushCompose with starter = some cp, buffer empty.
  unfold Compose.flushCompose
  rfl


--
-- The master theorem
--
--     ∀ cps, isNFCQuickCheck cps = true → toNFC cps = cps
--
-- proceeds by induction on `cps` (via `Reorder.list_snoc_induction`
-- lifted through `Array.toList`). Base case: `empty_sound`.
-- Inductive step on `cps = xs ++ #[cp]`:
--
--   * `isNFCQuickCheck_dropLast` extracts `IH : toNFC xs = xs`.
--   * `ToNFDAppend.toNFD_absorbing_right` factors
--     `toNFD (xs ++ #[cp])` through `toNFD (xs ++ toNFD #[cp])`.
--   * Case analysis on `cp`:
--       - QC=Y nonstarter → `singleton_sound_nonstarter`.
--       - QC=Y starter, empty decomposition → §3 above.
--       - QC=Y starter, size-2 decomposition → §4 above gives
--         `primaryComposite? d e = some cp`. The closure to
--         `toNFC #[cp] = #[cp]` requires unfolding the compose
--         state machine on `#[d, e]`.
--       - Hangul syllable → §4b above (closed via 11172-row
--         `native_decide` over the precomposed-syllable range).
--
-- The three Tibetan anomalous starters (U+0F73, U+0F75, U+0F81 — see
-- `ToNFDAppend.anomalousStarters`) have non-trivial canonical
-- decompositions whose `fullCanonicalDecompose` is non-starter-headed;
-- their `nfcQCValue` is not `.Y`, so they are excluded by the
-- precondition.
-- ═══════════════════════════════════════════════════════════════════════════════

end Unicode.Normalization.QuickCheckSoundnessSnoc
