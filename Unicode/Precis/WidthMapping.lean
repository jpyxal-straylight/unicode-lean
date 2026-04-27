/-
  Unicode.Precis.WidthMapping

  The "Width Mapping Rule" of RFC
  8265 §5.2.3 for the UsernameCaseMapped / UsernameCasePreserved
  profiles built on PRECIS IdentifierClass.

  Per RFC 8265:

      Fullwidth and halfwidth characters MUST be mapped to their
      decomposition equivalents.

  The source of truth for that mapping is the Decomposition_Mapping
  field of UnicodeData.txt whenever the decomposition is tagged
  `<wide>` (a fullwidth codepoint mapping to its narrow equivalent)
  or `<narrow>` (a halfwidth codepoint mapping to its non-halfwidth
  equivalent). Those 226 mappings are pinned in
  `Unicode.Generated.WidthCompatMappings` by the UcdGen
  preprocessor; this module consumes them through the `widthMap`
  function below.

  Codepoints that do not carry a `<wide>` or `<narrow>` compatibility
  decomposition are not affected.
-/

import Unicode.Generated.WidthCompatMappings

namespace Unicode.Precis.WidthMapping

open Unicode.Generated

/-- Look up a codepoint's width-compat mapping target. Returns `some
    target` if the codepoint carries a `<wide>` or `<narrow>`
    compatibility decomposition per the pinned UCD tables, otherwise
    `none`. -/
def lookupWidthMapping? (cp : Nat) : Option (Array Nat) :=
  WidthCompatMappings.widthCompatMappings.findSome?
    (fun ⟨src, tgt⟩ => if src = cp then some tgt else none)

/-- Apply the width mapping to a single codepoint, substituting with
    its compat target if one exists, otherwise returning the
    codepoint unchanged (as a singleton sequence). -/
def widthMapCodepoint (cp : Nat) : Array Nat :=
  match lookupWidthMapping? cp with
  | some target => target
  | none        => #[cp]

/-- Apply the width mapping to a codepoint sequence, flattening each
    per-codepoint result back into a single sequence. -/
def widthMap (cps : Array Nat) : Array Nat :=
  cps.foldl (fun acc cp => acc ++ widthMapCodepoint cp) #[]

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- Anchored on RFC 8265 canonical examples plus ASCII identity to
-- exercise the no-match path. FULLWIDTH LATIN CAPITAL A (U+FF21)
-- maps to LATIN CAPITAL A (U+0041). IDEOGRAPHIC SPACE (U+3000) maps
-- to ASCII SPACE (U+0020). ASCII letters carry no `<wide>`/`<narrow>`
-- decomposition and are preserved.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- FULLWIDTH LATIN CAPITAL LETTER A maps to LATIN CAPITAL LETTER A. -/
theorem widthMap_fullwidth_A :
    widthMapCodepoint 0xFF21 = #[0x0041] := by native_decide

/-- IDEOGRAPHIC SPACE maps to ASCII SPACE. -/
theorem widthMap_ideographic_space :
    widthMapCodepoint 0x3000 = #[0x0020] := by native_decide

/-- HALFWIDTH KATAKANA LETTER A (U+FF71) maps to KATAKANA LETTER A (U+30A2). -/
theorem widthMap_halfwidth_katakana_a :
    widthMapCodepoint 0xFF71 = #[0x30A2] := by native_decide

/-- ASCII letter has no width mapping. -/
theorem widthMap_ascii_a : widthMapCodepoint 0x0061 = #[0x0061] := by native_decide

/-- The sequence-level mapping preserves pure-ASCII input. -/
theorem widthMap_ascii_identity :
    widthMap #[0x0041, 0x0042, 0x0043] = #[0x0041, 0x0042, 0x0043] := by native_decide

/-- Mixed input: a fullwidth A followed by ASCII B maps fullwidth A
    to plain A while leaving B unchanged. -/
theorem widthMap_mixed :
    widthMap #[0xFF21, 0x0042] = #[0x0041, 0x0042] := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- IDEMPOTENCE
--
-- `widthMap` is idempotent on every input. The structural reason:
-- every `<wide>`/`<narrow>` compat target in UCD 17.0 is itself absent
-- from the source column of `widthCompatMappings`, so the output of
-- `widthMap` is a sequence of codepoints on which
-- `lookupWidthMapping?` returns `none`, and `widthMap` of such a
-- sequence is the identity.
--
-- The "targets absent from source" table-level fact is closed by
-- `native_decide` over the 226-entry table below and carries the
-- load for the abstract idempotence claim. The identity-on-miss
-- half lifts to `Array` level via `widthMap_id_on_non_sources` by
-- structural induction on the input sequence; the concrete-vector
-- idempotence results below anchor the testable surface via
-- `native_decide`.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Predicate: `cp` is a source codepoint of some `<wide>`/`<narrow>`
    compat decomposition, i.e. `lookupWidthMapping?` would return a
    `Some` value on it. -/
def isWidthCompatSource (cp : Nat) : Bool :=
  WidthCompatMappings.widthCompatMappings.any (fun entry => decide (entry.1 = cp))

/-- Every target codepoint of `widthCompatMappings` is itself absent
    from the source column — the table is a one-step substitution
    that produces a fixed point. Closed by `native_decide` over the
    pinned 226-entry table. -/
theorem widthCompatTargets_not_in_source :
    WidthCompatMappings.widthCompatMappings.all
      (fun entry => entry.2.all (fun cp => !isWidthCompatSource cp)) = true := by
  native_decide

/-- A codepoint that is not a width-compat source has no
    `lookupWidthMapping?` result. -/
theorem lookupWidthMapping_none_of_non_source (cp : Nat)
    (h : isWidthCompatSource cp = false) :
    lookupWidthMapping? cp = none := by
  unfold lookupWidthMapping?
  apply Array.findSome?_eq_none_iff.mpr
  intro entry hMem
  obtain ⟨src, tgt⟩ := entry
  have hNotEq : src ≠ cp := by
    intro hEq
    have hAny : WidthCompatMappings.widthCompatMappings.any
                  (fun e => decide (e.1 = cp)) = true := by
      rw [Array.any_eq_true]
      rcases Array.getElem_of_mem hMem with ⟨i, hi, hElem⟩
      refine ⟨i, hi, by rw [hElem]; exact decide_eq_true hEq⟩
    unfold isWidthCompatSource at h
    rw [hAny] at h
    exact Bool.noConfusion h
  simp only [hNotEq, if_false]

/-- A codepoint that is not a width-compat source maps to its own
    singleton under `widthMapCodepoint`. -/
theorem widthMapCodepoint_id_of_non_source (cp : Nat)
    (h : isWidthCompatSource cp = false) :
    widthMapCodepoint cp = #[cp] := by
  unfold widthMapCodepoint
  rw [lookupWidthMapping_none_of_non_source cp h]

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

/-- `widthMap` is the identity on any sequence whose codepoints are
    all non-sources. -/
theorem widthMap_id_of_all_non_source (cps : Array Nat)
    (h : ∀ cp ∈ cps, isWidthCompatSource cp = false) :
    widthMap cps = cps := by
  unfold widthMap
  apply arr_foldl_map_id_of_all_identity cps widthMapCodepoint
  intro cp hMem
  exact widthMapCodepoint_id_of_non_source cp (h cp hMem)

/-- Converse of `lookupWidthMapping_none_of_non_source`: a codepoint
    with no `lookupWidthMapping?` result is not a source. -/
theorem non_source_of_lookupWidthMapping_none (cp : Nat)
    (h : lookupWidthMapping? cp = none) :
    isWidthCompatSource cp = false := by
  unfold lookupWidthMapping? at h
  unfold isWidthCompatSource
  rw [Array.findSome?_eq_none_iff] at h
  rw [Array.any_eq_false]
  intro i hi hDec
  have hSrcEq : WidthCompatMappings.widthCompatMappings[i].1 = cp := of_decide_eq_true hDec
  have hEntry := h WidthCompatMappings.widthCompatMappings[i] (Array.getElem_mem hi)
  obtain ⟨src, tgt⟩ := WidthCompatMappings.widthCompatMappings[i]
  simp at hSrcEq
  subst hSrcEq
  simp at hEntry

/-- Membership decomposition: a codepoint in `widthMap cps` comes
    from `widthMapCodepoint x` for some `x ∈ cps`. -/
theorem mem_widthMap_iff (cps : Array Nat) (cp : Nat)
    (hMem : cp ∈ widthMap cps) :
    ∃ x ∈ cps, cp ∈ widthMapCodepoint x := by
  unfold widthMap at hMem
  rw [← Array.foldl_toList] at hMem
  have key : ∀ (l : List Nat) (init : Array Nat),
      cp ∈ l.foldl (fun acc x => acc ++ widthMapCodepoint x) init →
      cp ∈ init ∨ ∃ x ∈ l, cp ∈ widthMapCodepoint x := by
    intro l
    induction l with
    | nil => intro init hM; left; simpa using hM
    | cons hd tl ih =>
      intro init hM
      simp [List.foldl_cons] at hM
      rcases ih (init ++ widthMapCodepoint hd) hM with hInit | ⟨x, hxM, hxF⟩
      · rcases Array.mem_append.mp hInit with h1 | h2
        · left; exact h1
        · right; exact ⟨hd, by simp, h2⟩
      · right; exact ⟨x, by simp [hxM], hxF⟩
  rcases key cps.toList #[] hMem with hEmpty | ⟨x, hxM, hxF⟩
  · simp at hEmpty
  · exact ⟨x, by simpa using hxM, hxF⟩

/-- Specialized version of `Array.findSome?_eq_some_iff` for the
    width-mapping table: recover the source codepoint of a
    successful lookup. -/
theorem widthCompat_exists_entry_of_lookup
    (x : Nat) (tgt : Array Nat)
    (h : lookupWidthMapping? x = some tgt) :
    ∃ (src : Nat), (src, tgt) ∈ WidthCompatMappings.widthCompatMappings
                    ∧ src = x := by
  unfold lookupWidthMapping? at h
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

/-- Every codepoint in the output of `widthMap` is a non-source:
    - sources in the input are replaced by targets (all non-sources by
      `widthCompatTargets_not_in_source`);
    - non-sources in the input are preserved as themselves.
-/
theorem widthMap_output_all_non_source (cps : Array Nat) :
    ∀ cp ∈ widthMap cps, isWidthCompatSource cp = false := by
  intro cp hMem
  obtain ⟨x, hxInCps, hxF⟩ := mem_widthMap_iff cps cp hMem
  clear hxInCps
  unfold widthMapCodepoint at hxF
  -- Split on whether `x` has a lookup or not.
  cases hLook : lookupWidthMapping? x with
  | none =>
    -- widthMapCodepoint x reduces to #[x]; cp ∈ #[x] forces cp = x, which is a non-source.
    rw [hLook] at hxF
    simp at hxF
    have hCpEqX : cp = x := hxF
    rw [hCpEqX]
    exact non_source_of_lookupWidthMapping_none x hLook
  | some tgt =>
    -- widthMapCodepoint x reduces to tgt; cp ∈ tgt; tgt-codepoints are all non-sources.
    rw [hLook] at hxF
    obtain ⟨src, hEntryMem, hSrcEqX⟩ :=
      widthCompat_exists_entry_of_lookup x tgt hLook
    clear hSrcEqX
    -- The table-level fact: every target codepoint is a non-source.
    have hTable := widthCompatTargets_not_in_source
    rw [Array.all_eq_true] at hTable
    rcases Array.getElem_of_mem hEntryMem with ⟨i, hi, hElem⟩
    have hEntryAll := hTable i hi
    rw [hElem] at hEntryAll
    rw [Array.all_eq_true] at hEntryAll
    rcases Array.getElem_of_mem hxF with ⟨j, hj, hElemCp⟩
    have hCp := hEntryAll j hj
    rw [hElemCp] at hCp
    simpa using hCp

/-- **`widthMap` is idempotent.** For every codepoint sequence,
    applying the RFC 8265 §5.2.3 width mapping twice produces the
    same result as applying it once. The proof chains:

    - `widthMap cps` produces codepoints all absent from the source
      column of `widthCompatMappings` (by
      `widthMap_output_all_non_source`, itself resting on
      `widthCompatTargets_not_in_source`);
    - `widthMap` is the identity on such a sequence (by
      `widthMap_id_of_all_non_source`).
-/
theorem widthMap_idempotent (cps : Array Nat) :
    widthMap (widthMap cps) = widthMap cps :=
  widthMap_id_of_all_non_source (widthMap cps) (widthMap_output_all_non_source cps)

/-- Double width-map on fullwidth A equals single width-map. -/
theorem widthMap_idempotent_fullwidth_A :
    widthMap (widthMap #[0xFF21]) = widthMap #[0xFF21] := by native_decide

/-- Double width-map on halfwidth katakana equals single width-map. -/
theorem widthMap_idempotent_halfwidth_katakana_a :
    widthMap (widthMap #[0xFF71]) = widthMap #[0xFF71] := by native_decide

/-- Double width-map on ASCII equals single width-map (trivially). -/
theorem widthMap_idempotent_ascii :
    widthMap (widthMap #[0x0041, 0x0042]) = widthMap #[0x0041, 0x0042] := by native_decide

end Unicode.Precis.WidthMapping
