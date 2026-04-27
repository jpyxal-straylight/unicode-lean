/-
  Unicode.Normalization.Decompose

  Recursive canonical decomposition per UAX #15 §3.7. For each
  codepoint, either:

    * apply the Hangul algorithmic decomposition when the codepoint
      is a precomposed syllable in `0xAC00 .. 0xD7A3`; the result is
      always a primary L/V(/T) sequence needing no further recursion.
    * look up `canonicalDecomposition` in the UnicodeData table and
      recursively decompose each target codepoint until a fixed point
      is reached.

  Recursion is fuel-bounded for trivial termination. UAX #15 guarantees
  Unicode canonical decomposition has no cycles and bounded chain
  depth (in practice ≤ 4 rounds); the fuel constant here is well above
  any known real chain.
-/

import Unicode.Normalization.Lookup
import Unicode.Normalization.Hangul
import Unicode.Precis.WidthMapping

namespace Unicode.Normalization.Decompose

open Unicode.Normalization

/-- Maximum recursion depth for canonical decomposition. UAX #15
    bounds the longest real canonical decomposition chain at a small
    integer (≤ 4 for every Unicode release to date); 32 leaves a
    large safety margin. -/
def maxDepth : Nat := 32

/-- Fully canonically decompose a single codepoint, recursively until
    a fixed point. Returns the `#[cp]` singleton when the codepoint
    has no decomposition (primary character). Returns the expanded
    sequence otherwise.

    `fuel` bounds recursion depth; if exhausted the function returns
    the partial expansion, but this is unreachable under the `maxDepth`
    default on any real UCD release. -/
def fullCanonicalDecomposeFuel : Nat → Nat → Array Nat
  | 0,        cp => #[cp]
  | fuel + 1, cp =>
    match Hangul.decomposeSyllable? cp with
    | some jamo => jamo
    | none =>
      let step := Lookup.canonicalDecomposition cp
      if step.isEmpty then
        #[cp]
      else
        step.foldl
          (fun acc cp' => acc ++ fullCanonicalDecomposeFuel fuel cp')
          #[]

/-- Fully canonical decomposition of a single codepoint. Thin wrapper
    that fixes `fuel = maxDepth`. -/
def fullCanonicalDecompose (cp : Nat) : Array Nat :=
  fullCanonicalDecomposeFuel maxDepth cp

/-- Fully canonical decomposition of a codepoint sequence. Applies
    `fullCanonicalDecompose` to each input codepoint and concatenates
    the results in order. -/
def decomposeSequence (cps : Array Nat) : Array Nat :=
  cps.foldl (fun acc cp => acc ++ fullCanonicalDecompose cp) #[]

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `A` (no decomposition) round-trips as its own singleton. -/
theorem decompose_latin_A :
    fullCanonicalDecompose 0x0041 = #[0x0041] := by native_decide

/-- LATIN CAPITAL LETTER A WITH GRAVE decomposes to `A` + combining grave
    in one step. -/
theorem decompose_A_grave :
    fullCanonicalDecompose 0x00C0 = #[0x0041, 0x0300] := by native_decide

/-- ANGSTROM SIGN decomposes in TWO steps: first to LATIN CAPITAL A WITH
    RING ABOVE (0x00C5), then to `A` + combining ring above (0x030A).
    This exercises the recursive flattening. -/
theorem decompose_angstrom :
    fullCanonicalDecompose 0x212B = #[0x0041, 0x030A] := by native_decide

/-- HANGUL SYLLABLE GAG decomposes to `L + V + T` via the algorithmic
    path; no UnicodeData lookup involved. -/
theorem decompose_GAG :
    fullCanonicalDecompose 0xAC01 = #[0x1100, 0x1161, 0x11A8] := by native_decide

/-- Sequence decomposition concatenates per-codepoint decompositions. -/
theorem decompose_sequence_mixed :
    decomposeSequence #[0x0041, 0x00C0, 0x212B]
      = #[0x0041, 0x0041, 0x0300, 0x0041, 0x030A] := by native_decide

/-- Decomposition of an empty sequence is empty. -/
theorem decompose_empty : decomposeSequence #[] = #[] := by native_decide

/-- Decomposition of a pure-ASCII sequence is the input unchanged. -/
theorem decompose_ascii :
    decomposeSequence #[0x0068, 0x0065, 0x006C, 0x006C, 0x006F] -- "hello"
      = #[0x0068, 0x0065, 0x006C, 0x006C, 0x006F] := by native_decide

end Unicode.Normalization.Decompose

-- ═══════════════════════════════════════════════════════════════════════════════
-- WIDTH-COMPAT NON-INTERFERENCE
--
-- The cross-module preservation lemma: if a codepoint is not a width-compat
-- source (per the PRECIS `WidthMapping` table), its full canonical decomposition
-- output sequence contains no width-compat sources either.
--
-- Used by `Unicode.Precis.Preparation` to discharge
-- `NfcPreservesNonWidthCompatSource` through the toNFD → Reorder → Compose chain.
-- ═══════════════════════════════════════════════════════════════════════════════

namespace Unicode.Normalization.Decompose

open Unicode.Normalization
open Unicode.Generated
open Unicode.Precis.WidthMapping (isWidthCompatSource)

/-- Every Hangul jamo codepoint (0x1100..0x11C2) is a non-width-compat-source. -/
theorem hangulJamo_non_widthCompatSource :
    ((List.range 195).map (fun i => 0x1100 + i)).all
      (fun cp => !isWidthCompatSource cp) = true := by
  native_decide

/-- Every codepoint that appears in `UnicodeData.rows.canonicalDecomposition`
    (i.e. every direct canonical-decomposition target) is a non-width-compat-source.
    Also covers any recursive decomposition output since all canonical decomposition
    targets come from exactly this column. -/
theorem canonicalDecompTargets_non_widthCompatSource :
    UnicodeData.rows.all
      (fun row => row.canonicalDecomposition.all
        (fun cp => !isWidthCompatSource cp)) = true := by
  native_decide

/-- Every Hangul precomposed syllable in `0xAC00..0xD7A3` decomposes to
    a sequence of codepoints that are all non-width-compat-sources. Closed
    by `native_decide` over the entire 11172-syllable range. -/
theorem hangulSyllable_decompose_output_non_widthCompatSource :
    (List.range 11172).all
      (fun i => match Hangul.decomposeSyllable? (0xAC00 + i) with
                | some arr => arr.all (fun j => !isWidthCompatSource j)
                | none     => true) = true := by
  native_decide

/-- Pointwise version of `hangulSyllable_decompose_output_non_widthCompatSource`:
    any successful `decomposeSyllable?` output contains only non-width-compat-sources.
    The proof extracts the Hangul-range membership from the hypothesis and applies
    the enumerated table fact. -/
theorem decomposeSyllable_output_non_widthCompatSource
    (cp : Nat) (arr : Array Nat)
    (h : Hangul.decomposeSyllable? cp = some arr) (j : Nat) (hj : j ∈ arr) :
    isWidthCompatSource j = false := by
  have hSyl : Hangul.isHangulSyllable cp = true := by
    unfold Hangul.decomposeSyllable? at h
    split at h
    · next hYes => exact hYes
    · simp at h
  have hRange : 0xAC00 ≤ cp ∧ cp < 0xAC00 + 11172 := by
    unfold Hangul.isHangulSyllable Hangul.SBase Hangul.SCount
           Hangul.LCount Hangul.NCount Hangul.VCount Hangul.TCount at hSyl
    exact of_decide_eq_true hSyl
  have hiLt : cp - 0xAC00 < 11172 := by omega
  have hCpEq : 0xAC00 + (cp - 0xAC00) = cp := by omega
  have hTable := hangulSyllable_decompose_output_non_widthCompatSource
  rw [List.all_eq_true] at hTable
  have hI : cp - 0xAC00 ∈ List.range 11172 := List.mem_range.mpr hiLt
  have hAtI := hTable (cp - 0xAC00) hI
  rw [hCpEq, h] at hAtI
  rw [Array.all_eq_true] at hAtI
  rcases Array.getElem_of_mem hj with ⟨k, hk, hElem⟩
  have hBool := hAtI k hk
  rw [hElem] at hBool
  simpa using hBool

/-- Pointwise version of `canonicalDecompTargets_non_widthCompatSource`:
    every element of `Lookup.canonicalDecomposition cp` is a non-width-compat-source.
    Does not require a hypothesis on `cp` — the property holds vacuously when
    `cp` has no canonical decomposition (empty output). -/
theorem canonicalDecomposition_output_non_widthCompatSource
    (cp : Nat) (j : Nat) (hj : j ∈ Lookup.canonicalDecomposition cp) :
    isWidthCompatSource j = false := by
  unfold Lookup.canonicalDecomposition at hj
  split at hj
  · next row hRow =>
    have hRowMem : row ∈ UnicodeData.rows := Array.mem_of_find?_eq_some hRow
    have hTable := canonicalDecompTargets_non_widthCompatSource
    rw [Array.all_eq_true] at hTable
    rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
    have hRowAll := hTable i hi
    rw [hElem] at hRowAll
    rw [Array.all_eq_true] at hRowAll
    rcases Array.getElem_of_mem hj with ⟨k, hk, hElemJ⟩
    have hBool := hRowAll k hk
    rw [hElemJ] at hBool
    simpa using hBool
  · simp at hj

/-- Generic: membership in a `foldl`-with-append over an array factors
    through one of the source elements. -/
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

/-- **Fuel-bounded preservation.** If the input codepoint is a non-width-compat-source,
    every codepoint in its fuel-bounded canonical decomposition is also a
    non-width-compat-source. Proven by induction on `fuel`:

    * `fuel = 0` — output is `#[cp]`, direct from the hypothesis.
    * `fuel + 1` — case on the Hangul / table-lookup / no-decomposition branches:
      - Hangul: output is a jamo sequence; all jamo are non-sources.
      - table lookup nonempty: output is concatenation of recursive calls on the
        canonical decomposition targets; those targets are themselves non-sources
        (by the pinned `canonicalDecompTargets_non_widthCompatSource`), so the
        inductive hypothesis gives the conclusion for each recursive call.
      - empty lookup: output is `#[cp]`, direct from the hypothesis. -/
theorem fullCanonicalDecomposeFuel_preserves_non_widthCompatSource (fuel : Nat) :
    ∀ cp, isWidthCompatSource cp = false →
    ∀ j ∈ fullCanonicalDecomposeFuel fuel cp, isWidthCompatSource j = false := by
  induction fuel with
  | zero =>
    intro cp hCp j hj
    unfold fullCanonicalDecomposeFuel at hj
    simp at hj
    rw [hj]
    exact hCp
  | succ fuel ih =>
    intro cp hCp j hj
    unfold fullCanonicalDecomposeFuel at hj
    split at hj
    · next arr hSome =>
      exact decomposeSyllable_output_non_widthCompatSource cp arr hSome j hj
    · next hNone =>
      generalize hStep : Lookup.canonicalDecomposition cp = step at hj
      change j ∈ (if step.isEmpty = true then #[cp]
                  else step.foldl (fun acc cp' => acc ++ fullCanonicalDecomposeFuel fuel cp') #[])
        at hj
      split at hj
      · next hEmpty =>
        simp at hj
        rw [hj]
        exact hCp
      · next hNotEmpty =>
        obtain ⟨x, hxIn, hxF⟩ :=
          mem_foldl_append (fullCanonicalDecomposeFuel fuel) step j hj
        rw [← hStep] at hxIn
        have hxNonSource : isWidthCompatSource x = false :=
          canonicalDecomposition_output_non_widthCompatSource cp x hxIn
        exact ih x hxNonSource j hxF

/-- **Single-codepoint preservation.** Specialization of the fuel-bounded
    version at `fuel = maxDepth`. -/
theorem fullCanonicalDecompose_preserves_non_widthCompatSource
    (cp : Nat) (h : isWidthCompatSource cp = false) :
    ∀ j ∈ fullCanonicalDecompose cp, isWidthCompatSource j = false := by
  unfold fullCanonicalDecompose
  exact fullCanonicalDecomposeFuel_preserves_non_widthCompatSource maxDepth cp h

/-- **Sequence-level preservation.** If every input codepoint is a
    non-width-compat-source, then every output codepoint of
    `decomposeSequence` is also a non-width-compat-source. -/
theorem decomposeSequence_preserves_non_widthCompatSource
    (cps : Array Nat) (h : ∀ cp ∈ cps, isWidthCompatSource cp = false) :
    ∀ j ∈ decomposeSequence cps, isWidthCompatSource j = false := by
  intro j hj
  unfold decomposeSequence at hj
  obtain ⟨x, hxIn, hxF⟩ := mem_foldl_append fullCanonicalDecompose cps j hj
  exact fullCanonicalDecompose_preserves_non_widthCompatSource x (h x hxIn) j hxF

end Unicode.Normalization.Decompose
