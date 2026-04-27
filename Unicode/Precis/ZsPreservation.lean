/-
  Unicode.Precis.ZsPreservation

  Pre-compiled `native_decide` facts and structural preservation
  lemmas for the "no non-ASCII Zs" predicate, factored out of
  `Unicode.Precis.OpaqueString` so that the heavy UCD-table
  compilation costs stay isolated to one olean. `OpaqueString.lean`
  imports this module's pre-compiled oleans without reloading the
  underlying tables during its own `native_decide` evaluation.

  Exports:

    * `nonAsciiZsCodepoints`, `isNonAsciiZs` — the 16 hardcoded Zs
      codepoints and predicate.
    * `remapZsToAscii` — RFC 8265 §4.2.2 remap to U+0020.
    * `remapZsToAscii_output_no_nonAsciiZs`,
      `remapZsToAscii_id_of_no_nonAsciiZs` — remap invariants.
    * `decomposeSequence_preserves_no_nonAsciiZs`,
      `toNFD_preserves_no_nonAsciiZs`,
      `toNFC_preserves_no_nonAsciiZs` — structural preservation
      through the normalization pipeline.

  Deliberately does NOT import `Unicode.Precis.Categories` or
  `Unicode.Precis.BidiRule`; doing so would pull
  `DerivedGeneralCategory` and `DerivedBidiClass` into the
  `native_decide` compilation closure here, which is what caused the
  M5 build to exhaust WSL memory.
-/

import Unicode.Normalization.NFC
import Unicode.Normalization.Decompose
import Unicode.Normalization.Decomposability
import Unicode.Normalization.Hangul
import Unicode.Normalization.ComposeInversion
import Unicode.CaseFoldRoundtrip

namespace Unicode.Precis.ZsPreservation

open Unicode.Normalization
open Unicode.Normalization.NFC (toNFC)
open Unicode.Generated

-- ═══════════════════════════════════════════════════════════════════════════════
-- ZS IDENTIFICATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The 16 Zs (space-separator) codepoints defined by Unicode 16.0,
    excluding U+0020 SPACE. Stable across Unicode releases since 1.1
    (1993). -/
def nonAsciiZsCodepoints : Array Nat := #[
  0x00A0, 0x1680, 0x2000, 0x2001, 0x2002, 0x2003, 0x2004, 0x2005,
  0x2006, 0x2007, 0x2008, 0x2009, 0x200A, 0x202F, 0x205F, 0x3000
]

/-- `isNonAsciiZs cp` iff `cp` is a Zs category codepoint other than
    U+0020. -/
def isNonAsciiZs (cp : Nat) : Bool :=
  nonAsciiZsCodepoints.contains cp

/-- U+0020 is not a non-ASCII Zs. -/
theorem isNonAsciiZs_ascii_space : isNonAsciiZs 0x0020 = false := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- REMAP STEP (RFC 8265 §4.2.2)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- RFC 8265 §4.2.2: remap every non-ASCII Zs codepoint to U+0020 SPACE. -/
def remapZsToAscii (cps : Array Nat) : Array Nat :=
  cps.map (fun cp => if isNonAsciiZs cp then 0x0020 else cp)

/-- `remapZsToAscii` output contains no non-ASCII Zs codepoints. -/
theorem remapZsToAscii_output_no_nonAsciiZs (cps : Array Nat) :
    ∀ cp ∈ remapZsToAscii cps, isNonAsciiZs cp = false := by
  intro cp hcp
  unfold remapZsToAscii at hcp
  rw [Array.mem_map] at hcp
  obtain ⟨a, hMem, ha⟩ := hcp
  clear hMem
  by_cases hAZs : isNonAsciiZs a = true
  · rw [if_pos hAZs] at ha
    rw [← ha]
    exact isNonAsciiZs_ascii_space
  · rw [if_neg hAZs] at ha
    rw [← ha]
    simpa using hAZs

/-- `remapZsToAscii` is the identity on inputs that already have no
    non-ASCII Zs. -/
theorem remapZsToAscii_id_of_no_nonAsciiZs (cps : Array Nat)
    (h : ∀ cp ∈ cps, isNonAsciiZs cp = false) :
    remapZsToAscii cps = cps := by
  unfold remapZsToAscii
  have hAllEq : cps.map (fun cp => if isNonAsciiZs cp then 0x0020 else cp) =
                cps.map id := by
    apply Array.map_congr_left
    intro a ha
    have hA : isNonAsciiZs a = false := h a ha
    simp [hA]
  rw [hAllEq, Array.map_id]

-- ═══════════════════════════════════════════════════════════════════════════════
-- UCD NATIVE_DECIDE FACTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Non-non-ASCII-Zs codepoints' canonical decompositions contain no
    non-ASCII Zs. -/
theorem nonNonAsciiZs_decomp_no_nonAsciiZs :
    UnicodeData.rows.all (fun row =>
      isNonAsciiZs row.codepoint ||
      row.canonicalDecomposition.all (fun d => !isNonAsciiZs d)) = true := by
  native_decide

/-- Hangul jamo are not non-ASCII Zs. -/
theorem hangulJamo_no_nonAsciiZs :
    ((List.range 195).map (fun i => 0x1100 + i)).all
      (fun cp => !isNonAsciiZs cp) = true := by native_decide

/-- Hangul syllable decompositions contain no non-ASCII Zs. -/
theorem hangulSyllable_decompose_no_nonAsciiZs :
    (List.range 11172).all
      (fun i => match Hangul.decomposeSyllable? (0xAC00 + i) with
                | some arr => arr.all (fun j => !isNonAsciiZs j)
                | none     => true) = true := by native_decide

/-- Every non-ASCII Zs codepoint `c` has a non-ASCII Zs in its
    `fullCanonicalDecompose` (either `c` itself when it has no
    decomposition, or a non-ASCII Zs among its decomposition targets).
    This anchors the `decompose_compose_inversion`-based argument that
    `toNFC` cannot introduce non-ASCII Zs. -/
theorem nonAsciiZs_fullDecompose_contains_nonAsciiZs :
    nonAsciiZsCodepoints.all (fun c =>
      (Decompose.fullCanonicalDecompose c).any isNonAsciiZs) = true := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- POINTWISE LIFTS FROM UCD FACTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Pointwise Hangul analog. -/
theorem decomposeSyllable_output_no_nonAsciiZs
    (cp : Nat) (arr : Array Nat)
    (h : Hangul.decomposeSyllable? cp = some arr) (j : Nat) (hj : j ∈ arr) :
    isNonAsciiZs j = false := by
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
  have hTable := hangulSyllable_decompose_no_nonAsciiZs
  rw [List.all_eq_true] at hTable
  have hI : cp - 0xAC00 ∈ List.range 11172 := List.mem_range.mpr hiLt
  have hAtI := hTable (cp - 0xAC00) hI
  rw [hCpEq, h] at hAtI
  rw [Array.all_eq_true] at hAtI
  rcases Array.getElem_of_mem hj with ⟨k, hk, hElem⟩
  have hBool := hAtI k hk
  rw [hElem] at hBool
  simpa using hBool

/-- Pointwise: for a non-non-ASCII-Zs `cp`, every element of
    `Lookup.canonicalDecomposition cp` is also non-non-ASCII-Zs. -/
theorem canonicalDecomposition_output_no_nonAsciiZs
    (cp : Nat) (hCp : isNonAsciiZs cp = false)
    (j : Nat) (hj : j ∈ Lookup.canonicalDecomposition cp) :
    isNonAsciiZs j = false := by
  unfold Lookup.canonicalDecomposition at hj
  split at hj
  · next row hRow =>
    have hRowMem : row ∈ UnicodeData.rows := Array.mem_of_find?_eq_some hRow
    have hRowCp : row.codepoint = cp := by
      have hFind : UnicodeData.rows.find? (fun r => r.codepoint = cp) = some row := hRow
      have hP := Array.find?_some hFind
      exact of_decide_eq_true hP
    have hTable := nonNonAsciiZs_decomp_no_nonAsciiZs
    rw [Array.all_eq_true] at hTable
    rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
    have hEntry := hTable i hi
    rw [hElem] at hEntry
    simp only [Bool.or_eq_true] at hEntry
    rcases hEntry with hSrcZs | hTgtAllNonZs
    · rw [hRowCp, hCp] at hSrcZs
      exact Bool.noConfusion hSrcZs
    · rw [Array.all_eq_true] at hTgtAllNonZs
      rcases Array.getElem_of_mem hj with ⟨k, hk, hElemJ⟩
      have hBool := hTgtAllNonZs k hk
      rw [hElemJ] at hBool
      simpa using hBool
  · simp at hj

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRUCTURAL LIFTS: toNFD PRESERVES NO-NON-ASCII-Zs
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Membership through a `foldl`-with-append over an array. -/
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

/-- Forward membership through `foldl`-with-append. -/
theorem mem_foldl_append_of (f : Nat → Array Nat) (cps : Array Nat)
    (c : Nat) (hc : c ∈ cps) (d : Nat) (hd : d ∈ f c) :
    d ∈ cps.foldl (fun acc x => acc ++ f x) #[] := by
  rw [← Array.foldl_toList]
  have key : ∀ (l : List Nat) (init : Array Nat),
      (d ∈ init ∨ ∃ c' ∈ l, d ∈ f c') →
      d ∈ l.foldl (fun acc x => acc ++ f x) init := by
    intro l
    induction l with
    | nil =>
      intro init hCase
      rcases hCase with hInit | ⟨c', hc', hdf⟩
      · simpa using hInit
      · cases hc'
    | cons hd' tl ih =>
      intro init hCase
      simp only [List.foldl_cons]
      apply ih (init ++ f hd')
      rcases hCase with hInit | ⟨c', hc', hcf⟩
      · left; exact Array.mem_append.mpr (Or.inl hInit)
      · rcases List.mem_cons.mp hc' with rfl | hRest
        · left; exact Array.mem_append.mpr (Or.inr hcf)
        · right; exact ⟨c', hRest, hcf⟩
  apply key cps.toList #[]
  right
  exact ⟨c, by simpa using hc, hd⟩

/-- Fuel-bounded preservation of no-non-ASCII-Zs through
    `fullCanonicalDecomposeFuel`. -/
theorem fullCanonicalDecomposeFuel_preserves_no_nonAsciiZs (fuel : Nat) :
    ∀ cp, isNonAsciiZs cp = false →
    ∀ j ∈ Decompose.fullCanonicalDecomposeFuel fuel cp, isNonAsciiZs j = false := by
  induction fuel with
  | zero =>
    intro cp hCp j hj
    unfold Decompose.fullCanonicalDecomposeFuel at hj
    simp at hj
    rw [hj]
    exact hCp
  | succ fuel ih =>
    intro cp hCp j hj
    unfold Decompose.fullCanonicalDecomposeFuel at hj
    split at hj
    · next arr hSome =>
      exact decomposeSyllable_output_no_nonAsciiZs cp arr hSome j hj
    · next hNone =>
      generalize hStep : Lookup.canonicalDecomposition cp = step at hj
      change j ∈ (if step.isEmpty = true then #[cp]
                  else step.foldl (fun acc cp' =>
                        acc ++ Decompose.fullCanonicalDecomposeFuel fuel cp') #[]) at hj
      split at hj
      · next hEmpty =>
        simp at hj
        rw [hj]
        exact hCp
      · next hNotEmpty =>
        obtain ⟨x, hxIn, hxF⟩ :=
          mem_foldl_append (Decompose.fullCanonicalDecomposeFuel fuel) step j hj
        rw [← hStep] at hxIn
        have hxNonZs : isNonAsciiZs x = false :=
          canonicalDecomposition_output_no_nonAsciiZs cp hCp x hxIn
        exact ih x hxNonZs j hxF

/-- `decomposeSequence` preserves no-non-ASCII-Zs. -/
theorem decomposeSequence_preserves_no_nonAsciiZs
    (cps : Array Nat) (h : ∀ cp ∈ cps, isNonAsciiZs cp = false) :
    ∀ j ∈ Decompose.decomposeSequence cps, isNonAsciiZs j = false := by
  intro j hj
  unfold Decompose.decomposeSequence at hj
  obtain ⟨x, hxIn, hxF⟩ := mem_foldl_append Decompose.fullCanonicalDecompose cps j hj
  unfold Decompose.fullCanonicalDecompose at hxF
  exact fullCanonicalDecomposeFuel_preserves_no_nonAsciiZs Decompose.maxDepth x
    (h x hxIn) j hxF

/-- `toNFD` preserves no-non-ASCII-Zs. -/
theorem toNFD_preserves_no_nonAsciiZs
    (cps : Array Nat) (h : ∀ cp ∈ cps, isNonAsciiZs cp = false) :
    ∀ j ∈ NFC.toNFD cps, isNonAsciiZs j = false := by
  unfold NFC.toNFD
  intro j hj
  have hDecAll : ∀ cp ∈ Decompose.decomposeSequence cps,
                   (fun x => !isNonAsciiZs x) cp = true := by
    intro cp hcp
    have := decomposeSequence_preserves_no_nonAsciiZs cps h cp hcp
    simpa using this
  have hR := Reorder.reorder_preserves_all (fun x => !isNonAsciiZs x)
               (Decompose.decomposeSequence cps) hDecAll j hj
  simpa using hR

-- ═══════════════════════════════════════════════════════════════════════════════
-- toNFC PRESERVES NO-NON-ASCII-Zs
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **`toNFC` preserves no-non-ASCII-Zs.**

    Strategy: if `toNFC x` contained a non-ASCII Zs `c`, then
    `fullCanonicalDecompose c` contains some non-ASCII Zs `d` (UCD
    fact `nonAsciiZs_fullDecompose_contains_nonAsciiZs`). Then `d ∈
    decomposeSequence (toNFC x)` ⊆ `toNFD (toNFC x)` = `toNFD x` (via
    `decompose_compose_inversion`-derived `toNFD_toNFC_eq_toNFD`).
    But `toNFD x` has no non-ASCII Zs by hypothesis, contradiction. -/
theorem toNFC_preserves_no_nonAsciiZs
    (cps : Array Nat) (h : ∀ cp ∈ cps, isNonAsciiZs cp = false) :
    ∀ cp ∈ toNFC cps, isNonAsciiZs cp = false := by
  intro c hc
  cases hZsC : isNonAsciiZs c with
  | false => rfl
  | true =>
    exfalso
    have hCinZs : c ∈ nonAsciiZsCodepoints := by
      unfold isNonAsciiZs at hZsC
      exact Array.mem_of_contains_eq_true hZsC
    have hTable := nonAsciiZs_fullDecompose_contains_nonAsciiZs
    rw [Array.all_eq_true] at hTable
    rcases Array.getElem_of_mem hCinZs with ⟨i, hi, hElem⟩
    have hAtI := hTable i hi
    rw [hElem] at hAtI
    rw [Array.any_eq_true] at hAtI
    obtain ⟨idx, hIdx, hIsZs⟩ := hAtI
    let d : Nat := (Decompose.fullCanonicalDecompose c)[idx]
    have hdInDecomp : d ∈ Decompose.fullCanonicalDecompose c :=
      Array.getElem_mem hIdx
    have hdIsZs : isNonAsciiZs d = true := hIsZs
    have hdInDecSeq : d ∈ Decompose.decomposeSequence (toNFC cps) := by
      unfold Decompose.decomposeSequence
      exact mem_foldl_append_of Decompose.fullCanonicalDecompose (toNFC cps)
        c hc d hdInDecomp
    have hdInNfd : d ∈ NFC.toNFD (toNFC cps) := by
      unfold NFC.toNFD
      exact Unicode.CaseFoldRoundtrip.reorder_mem_of_mem
        (Decompose.decomposeSequence (toNFC cps)) d hdInDecSeq
    rw [ComposeInversion.toNFD_toNFC_eq_toNFD] at hdInNfd
    have hdNotZs : isNonAsciiZs d = false :=
      toNFD_preserves_no_nonAsciiZs cps h d hdInNfd
    rw [hdNotZs] at hdIsZs
    exact Bool.noConfusion hdIsZs

end Unicode.Precis.ZsPreservation
