/-
  Unicode.Precis.CaseMapping

  Unicode default full case
  folding per UAX #21 and RFC 8265 §5.2.4 as consumed by the
  UsernameCaseMapped profile built on PRECIS IdentifierClass.

  Source of truth: the pinned `CaseFolding.txt` entries with status
  `C` (common, simple=full) and `F` (full-only, length-changing) —
  the union RFC 8265 calls "default full case folding". Entries with
  status `S` (simple, length-preserving) are redundant with `C` or
  paired with `F` and are not in the pinned table. Entries with
  status `T` (Turkic-locale-specific) are excluded from the default
  path.

  Codepoints with no CaseFolding entry fold to themselves; callers
  receive the original codepoint as a singleton sequence.
-/

import Unicode.Generated.CaseFolding
import Unicode.Precis.WidthMapping

namespace Unicode.Precis.CaseMapping

open Unicode.Generated

/-- Look up a codepoint's default-full case-folded target. Returns
    `some target` when the codepoint has a status-C or status-F
    entry in CaseFolding.txt, otherwise `none`. -/
def lookupCaseFolding? (cp : Nat) : Option (Array Nat) :=
  CaseFolding.foldings.findSome?
    (fun entry => if entry.1 = cp then some entry.2 else none)

/-- Apply default full case folding to a single codepoint,
    substituting with the fold target if one exists, otherwise
    returning the codepoint unchanged (as a singleton sequence). -/
def caseFoldCodepoint (cp : Nat) : Array Nat :=
  match lookupCaseFolding? cp with
  | some target => target
  | none        => #[cp]

/-- Apply default full case folding to a codepoint sequence,
    flattening each per-codepoint result back into a single
    sequence. -/
def caseFold (cps : Array Nat) : Array Nat :=
  cps.foldl (fun acc cp => acc ++ caseFoldCodepoint cp) #[]

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- Anchored on canonical case-folding examples: ASCII uppercase →
-- ASCII lowercase (status C), SHARP S → "ss" (status F, the
-- classic length-growing case), DOTLESS I and DOTTED CAPITAL I
-- (edge cases omitted from Turkic fold — their `C` / `F`
-- mappings here match the default non-locale-specific path).
-- ═══════════════════════════════════════════════════════════════════════════════

/-- LATIN CAPITAL LETTER A folds to LATIN SMALL LETTER A. -/
theorem caseFold_latin_A : caseFoldCodepoint 0x0041 = #[0x0061] := by native_decide

/-- LATIN CAPITAL LETTER Z folds to LATIN SMALL LETTER Z. -/
theorem caseFold_latin_Z : caseFoldCodepoint 0x005A = #[0x007A] := by native_decide

/-- LATIN SMALL LETTER SHARP S (ß) folds to "ss" — the length-growing
    status-F case RFC 8265 requires. -/
theorem caseFold_sharp_s :
    caseFoldCodepoint 0x00DF = #[0x0073, 0x0073] := by native_decide

/-- LATIN CAPITAL LETTER I folds to LATIN SMALL LETTER I (non-Turkic
    default path — status C). -/
theorem caseFold_capital_I : caseFoldCodepoint 0x0049 = #[0x0069] := by native_decide

/-- LATIN CAPITAL LETTER I WITH DOT ABOVE folds to LATIN SMALL
    LETTER I + COMBINING DOT ABOVE per the status-F entry. -/
theorem caseFold_I_with_dot_above :
    caseFoldCodepoint 0x0130 = #[0x0069, 0x0307] := by native_decide

/-- Already-lowercase ASCII is unchanged. -/
theorem caseFold_lowercase_a : caseFoldCodepoint 0x0061 = #[0x0061] := by native_decide

/-- Digit has no case mapping. -/
theorem caseFold_digit : caseFoldCodepoint 0x0030 = #[0x0030] := by native_decide

/-- Sequence-level fold lowercases each ASCII letter. -/
theorem caseFold_ascii_word :
    caseFold #[0x0041, 0x0042, 0x0043] = #[0x0061, 0x0062, 0x0063] := by native_decide

/-- The sharp-s substitution grows a 1-codepoint input into a 2-codepoint output. -/
theorem caseFold_straße_style :
    caseFold #[0x0073, 0x00DF] = #[0x0073, 0x0073, 0x0073] := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- IDEMPOTENCE
--
-- `caseFold` is idempotent on every input. The structural reason:
-- every target codepoint of a CaseFolding entry (in the retained
-- full-fold subset — status C + F) is itself absent from the
-- source column of `foldings`, so the output of `caseFold` is a
-- sequence of codepoints on which `lookupCaseFolding?` returns
-- `none`, and `caseFold` of such a sequence is the identity.
--
-- The "targets absent from source" fact is closed by `native_decide`
-- over the pinned table below. The concrete-vector idempotence
-- theorems that follow anchor the testable surface.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Predicate: `cp` is a source codepoint of some default-full case
    folding entry, i.e. `lookupCaseFolding?` would return a `Some`
    value on it. -/
def isCaseFoldSource (cp : Nat) : Bool :=
  CaseFolding.foldings.any (fun entry => decide (entry.1 = cp))

/-- Every target codepoint of `foldings` is itself absent from the
    source column — the table is a one-step substitution that
    produces a fixed point. Closed by `native_decide` over the
    pinned 1,585-entry table. -/
theorem caseFoldTargets_not_in_source :
    CaseFolding.foldings.all
      (fun entry => entry.2.all (fun cp => !isCaseFoldSource cp)) = true := by
  native_decide

/-- A codepoint that is not a case-fold source has no
    `lookupCaseFolding?` result. -/
theorem lookupCaseFolding_none_of_non_source (cp : Nat)
    (h : isCaseFoldSource cp = false) :
    lookupCaseFolding? cp = none := by
  unfold lookupCaseFolding?
  apply Array.findSome?_eq_none_iff.mpr
  intro entry hMem
  obtain ⟨src, tgt⟩ := entry
  have hNotEq : src ≠ cp := by
    intro hEq
    have hAny : CaseFolding.foldings.any
                  (fun e => decide (e.1 = cp)) = true := by
      rw [Array.any_eq_true]
      rcases Array.getElem_of_mem hMem with ⟨i, hi, hElem⟩
      refine ⟨i, hi, by rw [hElem]; exact decide_eq_true hEq⟩
    unfold isCaseFoldSource at h
    rw [hAny] at h
    exact Bool.noConfusion h
  simp only [hNotEq, if_false]

/-- A codepoint that is not a case-fold source maps to its own
    singleton under `caseFoldCodepoint`. -/
theorem caseFoldCodepoint_id_of_non_source (cp : Nat)
    (h : isCaseFoldSource cp = false) :
    caseFoldCodepoint cp = #[cp] := by
  unfold caseFoldCodepoint
  rw [lookupCaseFolding_none_of_non_source cp h]

/-- Generic lift: on any `Array Nat` whose codepoints each satisfy
    `f cp = #[cp]`, the foldl-with-append pipeline is the identity. -/
theorem arr_foldl_map_id_of_all_identity (cps : Array Nat)
    (f : Nat → Array Nat) (hAll : ∀ cp ∈ cps, f cp = #[cp]) :
    cps.foldl (fun acc cp => acc ++ f cp) #[] = cps := by
  rw [← Array.foldl_toList]
  have hAllList : ∀ cp ∈ cps.toList, f cp = #[cp] :=
    fun cp hMem => hAll cp (by simpa using hMem)
  have key : ∀ (l : List Nat) (init : Array Nat),
      (∀ cp ∈ l, f cp = #[cp]) →
      l.foldl (fun acc cp => acc ++ f cp) init = init ++ l.toArray := by
    intro l
    induction l with
    | nil => intro init hH; simp
    | cons hd tl ih =>
      intro init hH
      have hHd : f hd = #[hd] := hH hd (by simp)
      have hTl : ∀ cp ∈ tl, f cp = #[cp] := fun cp hMem => hH cp (by simp [hMem])
      simp only [List.foldl_cons, hHd]
      rw [ih (init ++ #[hd]) hTl]
      simp
  rw [key cps.toList #[] hAllList]
  simp

/-- `caseFold` is the identity on any sequence whose codepoints are
    all non-sources. -/
theorem caseFold_id_of_all_non_source (cps : Array Nat)
    (h : ∀ cp ∈ cps, isCaseFoldSource cp = false) :
    caseFold cps = cps := by
  unfold caseFold
  apply arr_foldl_map_id_of_all_identity cps caseFoldCodepoint
  intro cp hMem
  exact caseFoldCodepoint_id_of_non_source cp (h cp hMem)

/-- Converse of `lookupCaseFolding_none_of_non_source`: a codepoint
    with no `lookupCaseFolding?` result is not a source. -/
theorem non_source_of_lookupCaseFolding_none (cp : Nat)
    (h : lookupCaseFolding? cp = none) :
    isCaseFoldSource cp = false := by
  unfold lookupCaseFolding? at h
  unfold isCaseFoldSource
  rw [Array.findSome?_eq_none_iff] at h
  rw [Array.any_eq_false]
  intro i hi hDec
  have hSrcEq : CaseFolding.foldings[i].1 = cp := of_decide_eq_true hDec
  have hEntry := h CaseFolding.foldings[i] (Array.getElem_mem hi)
  obtain ⟨src, tgt⟩ := CaseFolding.foldings[i]
  simp at hSrcEq
  subst hSrcEq
  simp at hEntry

/-- Membership decomposition: a codepoint in `caseFold cps` comes
    from `caseFoldCodepoint x` for some `x ∈ cps`. -/
theorem mem_caseFold_iff (cps : Array Nat) (cp : Nat)
    (hMem : cp ∈ caseFold cps) :
    ∃ x ∈ cps, cp ∈ caseFoldCodepoint x := by
  unfold caseFold at hMem
  rw [← Array.foldl_toList] at hMem
  have key : ∀ (l : List Nat) (init : Array Nat),
      cp ∈ l.foldl (fun acc x => acc ++ caseFoldCodepoint x) init →
      cp ∈ init ∨ ∃ x ∈ l, cp ∈ caseFoldCodepoint x := by
    intro l
    induction l with
    | nil => intro init hM; left; simpa using hM
    | cons hd tl ih =>
      intro init hM
      simp [List.foldl_cons] at hM
      rcases ih (init ++ caseFoldCodepoint hd) hM with hInit | ⟨x, hxM, hxF⟩
      · rcases Array.mem_append.mp hInit with h1 | h2
        · left; exact h1
        · right; exact ⟨hd, by simp, h2⟩
      · right; exact ⟨x, by simp [hxM], hxF⟩
  rcases key cps.toList #[] hMem with hEmpty | ⟨x, hxM, hxF⟩
  · simp at hEmpty
  · exact ⟨x, by simpa using hxM, hxF⟩

/-- Recover the source codepoint of a successful case-fold lookup. -/
theorem caseFold_exists_entry_of_lookup
    (x : Nat) (tgt : Array Nat)
    (h : lookupCaseFolding? x = some tgt) :
    ∃ (src : Nat), (src, tgt) ∈ CaseFolding.foldings ∧ src = x := by
  unfold lookupCaseFolding? at h
  rw [Array.findSome?_eq_some_iff] at h
  obtain ⟨ys, entry, zs, hShape, hIfSome, hNoneInYs⟩ := h
  obtain ⟨src, tgt'⟩ := entry
  simp only at hIfSome
  split at hIfSome
  · next hEq =>
    have hTgtEq : tgt = tgt' := by
      have hExtract := hIfSome
      simp at hExtract
      exact hExtract.symm
    subst hTgtEq
    refine ⟨src, ?membership, hEq⟩
    rw [hShape]
    simp
  · exact absurd hIfSome (by simp)

/-- Every codepoint in the output of `caseFold` is a non-source. -/
theorem caseFold_output_all_non_source (cps : Array Nat) :
    ∀ cp ∈ caseFold cps, isCaseFoldSource cp = false := by
  intro cp hMem
  obtain ⟨x, hxInCps, hxF⟩ := mem_caseFold_iff cps cp hMem
  clear hxInCps
  unfold caseFoldCodepoint at hxF
  cases hLook : lookupCaseFolding? x with
  | none =>
    rw [hLook] at hxF
    simp at hxF
    have hCpEqX : cp = x := hxF
    rw [hCpEqX]
    exact non_source_of_lookupCaseFolding_none x hLook
  | some tgt =>
    rw [hLook] at hxF
    obtain ⟨src, hEntryMem, hSrcEqX⟩ :=
      caseFold_exists_entry_of_lookup x tgt hLook
    clear hSrcEqX
    have hTable := caseFoldTargets_not_in_source
    rw [Array.all_eq_true] at hTable
    rcases Array.getElem_of_mem hEntryMem with ⟨i, hi, hElem⟩
    have hEntryAll := hTable i hi
    rw [hElem] at hEntryAll
    rw [Array.all_eq_true] at hEntryAll
    rcases Array.getElem_of_mem hxF with ⟨j, hj, hElemCp⟩
    have hCp := hEntryAll j hj
    rw [hElemCp] at hCp
    simpa using hCp

/-- **`caseFold` is idempotent.** For every codepoint sequence,
    applying RFC 8265 §5.2.4 default full case folding twice
    produces the same result as applying it once. -/
theorem caseFold_idempotent (cps : Array Nat) :
    caseFold (caseFold cps) = caseFold cps :=
  caseFold_id_of_all_non_source (caseFold cps) (caseFold_output_all_non_source cps)

-- ═══════════════════════════════════════════════════════════════════════════════
-- CROSS-TABLE NON-INTERFERENCE WITH WidthMapping
-- The PRECIS pipeline applies width-mapping BEFORE case-folding. For
-- the composition to preserve the "no width-compat sources" invariant
-- established by widthMap, case-folding must not reintroduce any
-- width-compat source. The check below witnesses this:
-- on any input whose codepoints are all non-width-compat-sources, the
-- case-folded output is still all non-width-compat-sources.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Table-level fact: for every case-fold entry whose source is not
    a width-compat source, every target codepoint is also not a
    width-compat source. Closed by `native_decide` over the pinned
    1,585-entry CaseFolding table × the 226-entry WidthCompatMappings
    table. -/
theorem caseFold_preserves_non_widthCompatSource :
    CaseFolding.foldings.all
      (fun entry => WidthMapping.isWidthCompatSource entry.1
                    || entry.2.all
                         (fun cp => !WidthMapping.isWidthCompatSource cp)) = true := by
  native_decide

/-- Structural lift: on any sequence whose codepoints are all
    non-width-compat-sources, the case-folded output is still all
    non-width-compat-sources. -/
theorem caseFold_output_non_widthCompatSource (cps : Array Nat)
    (hIn : ∀ cp ∈ cps, WidthMapping.isWidthCompatSource cp = false) :
    ∀ cp ∈ caseFold cps, WidthMapping.isWidthCompatSource cp = false := by
  intro cp hMem
  obtain ⟨x, hxInCps, hxF⟩ := mem_caseFold_iff cps cp hMem
  have hxNonWidth : WidthMapping.isWidthCompatSource x = false := hIn x hxInCps
  unfold caseFoldCodepoint at hxF
  cases hLook : lookupCaseFolding? x with
  | none =>
    -- caseFoldCodepoint x = #[x]; cp = x; x is already a non-width-source by hIn.
    rw [hLook] at hxF
    simp at hxF
    have hCpEqX : cp = x := hxF
    rw [hCpEqX]
    exact hxNonWidth
  | some tgt =>
    -- caseFoldCodepoint x = tgt. Use the table-level preservation fact:
    -- since x is not a width-source, x's fold target tgt has no width-sources.
    rw [hLook] at hxF
    obtain ⟨src, hEntryMem, hSrcEqX⟩ :=
      caseFold_exists_entry_of_lookup x tgt hLook
    have hTable := caseFold_preserves_non_widthCompatSource
    rw [Array.all_eq_true] at hTable
    rcases Array.getElem_of_mem hEntryMem with ⟨i, hi, hElem⟩
    have hEntry := hTable i hi
    rw [hElem] at hEntry
    simp only [Bool.or_eq_true] at hEntry
    rcases hEntry with hSrcIsWidth | hTgtAllNonWidth
    · -- src is width-source, but src = x and x is non-width-source: contradiction.
      subst hSrcEqX
      rw [hxNonWidth] at hSrcIsWidth
      exact Bool.noConfusion hSrcIsWidth
    · -- All targets are non-width-sources.
      rw [Array.all_eq_true] at hTgtAllNonWidth
      rcases Array.getElem_of_mem hxF with ⟨j, hj, hElemCp⟩
      have hCp := hTgtAllNonWidth j hj
      rw [hElemCp] at hCp
      simpa using hCp


/-- Double case-fold on capital A equals single case-fold. -/
theorem caseFold_idempotent_A :
    caseFold (caseFold #[0x0041]) = caseFold #[0x0041] := by native_decide

/-- Double case-fold on sharp-s equals single case-fold. -/
theorem caseFold_idempotent_sharp_s :
    caseFold (caseFold #[0x00DF]) = caseFold #[0x00DF] := by native_decide

/-- Double case-fold on a mixed ASCII word equals single case-fold. -/
theorem caseFold_idempotent_ascii_word :
    caseFold (caseFold #[0x0041, 0x0062, 0x0043])
      = caseFold #[0x0041, 0x0062, 0x0043] := by native_decide

end Unicode.Precis.CaseMapping
