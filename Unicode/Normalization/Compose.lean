/-
  Unicode.Normalization.Compose

  Canonical composition per UAX #15 §1.3 / D117. Walks a reordered
  sequence left-to-right, maintaining the "active starter" and its
  buffered trailing non-starters. For each new non-starter C:

    * If C is not blocked from the starter (no buffered non-starter
      has CCC ≥ CCC(C)), and the pair `(starter, C)` primary-composes
      to some `P` that is NOT in Full_Composition_Exclusion, then
      the starter is replaced by `P` and `C` is consumed.
    * Otherwise `C` joins the buffer.

  "Primary composite" lookup is the reverse of the canonical-
  decomposition table: find the codepoint whose decomposition is
  exactly `#[starter, C]`. Hangul L+V / LV+T pairs short-circuit via
  the algorithmic path in `Hangul.composePair?`.
-/

import Unicode.Normalization.Lookup
import Unicode.Normalization.Hangul
import Unicode.Precis.WidthMapping

namespace Unicode.Normalization.Compose

open Unicode.Normalization
open Unicode.Generated

/-- Primary-composite lookup: return `P` when `(d, c)` is the canonical
    decomposition of exactly one non-excluded codepoint `P`, else
    `none`. Hangul L+V and LV+T pairs handled algorithmically; all
    other pairs go through a linear scan of the UnicodeData table,
    skipping codepoints flagged Full_Composition_Exclusion. -/
def primaryComposite? (d c : Nat) : Option Nat :=
  match Hangul.composePair? d c with
  | some p => some p
  | none =>
    UnicodeData.rows.findSome? (fun r =>
      if r.canonicalDecomposition = #[d, c]
         ∧ ¬ Lookup.isFullCompositionExclusion r.codepoint then
        some r.codepoint
      else
        none)

/-- Fold state for the composition pass.

    * `emitted`  — the sequence finalized behind the current active
                   starter (finished runs).
    * `starter`  — the active starter codepoint, possibly the result
                   of one or more primary-composite absorptions.
    * `buffer`   — non-starters seen after `starter` that did not
                   compose with it, in REVERSE scan order.
    * `maxCCC`   — maximum CCC among buffered non-starters, used to
                   detect blocking per UAX #15. -/
structure ComposeState where
  emitted : Array Nat
  starter : Option Nat
  buffer  : List Nat
  maxCCC  : Nat
  deriving Inhabited

def initialState : ComposeState :=
  { emitted := #[], starter := none, buffer := [], maxCCC := 0 }

/-- Emit the accumulated starter + buffer as a suffix appended to
    `emitted`, producing the final output array. -/
def flushCompose (s : ComposeState) : Array Nat :=
  let bufferArr := s.buffer.reverse.toArray
  match s.starter with
  | some st => s.emitted ++ #[st] ++ bufferArr
  | none    => s.emitted ++ bufferArr

/-- Step: process one codepoint.

    Handles both starter-with-non-starter composition (the common case)
    and starter-with-starter composition (Hangul L+V → LV, LV+T → LVT).
    UAX #15 D115/D117: when the current codepoint `cp` is itself a
    starter (CCC = 0), it is blocked from the active starter iff any
    non-starter is buffered between them (equivalently, `buffer` is
    non-empty). -/
def stepCompose (s : ComposeState) (cp : Nat) : ComposeState :=
  let ccc := Lookup.canonicalCombiningClass cp
  match s.starter with
  | none =>
    if ccc = 0 then
      -- First starter of the sequence; no flush needed.
      { s with starter := some cp }
    else
      -- Leading non-starter with no active starter to absorb into.
      { s with emitted := s.emitted ++ #[cp] }
  | some st =>
    if ccc = 0 then
      -- New starter. Compose with active starter only if no buffered
      -- non-starters stand between them.
      if s.buffer.isEmpty then
        match primaryComposite? st cp with
        | some p => { s with starter := some p }
        | none =>
          { emitted := s.emitted ++ #[st]
            starter := some cp
            buffer  := []
            maxCCC  := 0 }
      else
        { emitted := s.emitted ++ #[st] ++ s.buffer.reverse.toArray
          starter := some cp
          buffer  := []
          maxCCC  := 0 }
    else
      -- Non-starter. Blocked iff any buffered non-starter has CCC ≥
      -- this codepoint's CCC.
      if ccc ≤ s.maxCCC then
        { s with buffer := cp :: s.buffer, maxCCC := Nat.max s.maxCCC ccc }
      else
        match primaryComposite? st cp with
        | some p => { s with starter := some p }
        | none   => { s with buffer := cp :: s.buffer, maxCCC := Nat.max s.maxCCC ccc }

/-- Canonical composition of a codepoint sequence per UAX #15 §1.3. -/
def compose (cps : Array Nat) : Array Nat :=
  flushCompose (cps.foldl stepCompose initialState)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Primary-composite sanity: `A` + combining grave composes to `À`. -/
theorem primary_A_grave :
    primaryComposite? 0x0041 0x0300 = some 0x00C0 := by native_decide

/-- Primary-composite sanity: `A` + combining ring above composes to `Å`. -/
theorem primary_A_ring :
    primaryComposite? 0x0041 0x030A = some 0x00C5 := by native_decide

/-- Hangul primary composition: L + V composes to LV syllable. -/
theorem primary_hangul_LV :
    primaryComposite? 0x1100 0x1161 = some 0xAC00 := by native_decide

/-- Empty sequence composes to empty. -/
theorem compose_empty : compose #[] = #[] := by native_decide

/-- Pure ASCII composes unchanged. -/
theorem compose_ascii : compose #[0x0048, 0x0069] = #[0x0048, 0x0069] := by native_decide

/-- `A` + combining grave composes to `À`. -/
theorem compose_A_grave :
    compose #[0x0041, 0x0300] = #[0x00C0] := by native_decide

/-- Decomposed Angstrom `(A, combining ring)` composes to `Å`
    (0x00C5) — NOT back to the ANGSTROM SIGN (0x212B), which is a
    Full_Composition_Exclusion. -/
theorem compose_angstrom_to_A_ring :
    compose #[0x0041, 0x030A] = #[0x00C5] := by native_decide

/-- Hangul jamo L + V composes to LV syllable. -/
theorem compose_hangul_LV :
    compose #[0x1100, 0x1161] = #[0xAC00] := by native_decide

/-- Hangul jamo L + V + T composes to LVT syllable in two steps. -/
theorem compose_hangul_LVT :
    compose #[0x1100, 0x1161, 0x11A8] = #[0xAC01] := by native_decide

/-- Blocking: when a non-composable non-starter stands between the
    starter and a would-be composable partner, the partner is blocked
    from composing with the starter. Here combining cedilla (CCC=202)
    sits between `A` and combining grave (CCC=230). Grave IS NOT
    blocked here because cedilla has LOWER CCC, so grave can still
    compose past it. Result: `À` (A+grave composed) + cedilla. -/
theorem compose_not_blocked_lower_ccc_between :
    compose #[0x0041, 0x0327, 0x0300] = #[0x00C0, 0x0327] := by native_decide

/-- Blocking requires a non-starter to be IN the buffer between starter
    and candidate. SPACE (0x0020) has no primary composites, so the
    combining grave following it goes into the buffer rather than
    being absorbed. A subsequent combining acute (CCC=230, equal to
    grave's CCC) is then blocked (CCC ≤ buffered maxCCC). Result:
    the input sequence passes through unchanged. -/
theorem compose_blocked_equal_ccc :
    compose #[0x0020, 0x0300, 0x0301] = #[0x0020, 0x0300, 0x0301] := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- WIDTH-COMPAT NON-INTERFERENCE
--
-- Canonical composition preserves non-width-compat-source input codepoints.
-- Two routes produce output codepoints: direct passthrough of input cps
-- (preserved by hypothesis) and primary-composite lookup. For the latter,
-- the composed codepoint is either
--   * a Hangul syllable in 0xAC00..0xD7A4 (bounded by the Hangul composition
--     arithmetic); the entire inclusive range is enumerated non-width-compat-
--     source by `native_decide`, or
--   * the codepoint of a UnicodeData row whose canonical decomposition equals
--     `#[d, c]`; rows with any canonical decomposition are non-width-compat-
--     source by `native_decide` on the pinned UnicodeData table (Unicode
--     invariant: a codepoint has either a canonical decomposition or a
--     compatibility decomposition, not both).
--
-- Both `native_decide` table facts combine with a structural state-invariant
-- induction on `stepCompose` to yield `compose_preserves_non_widthCompatSource`.
-- ═══════════════════════════════════════════════════════════════════════════════

section WidthCompatPreservation

open Unicode.Precis.WidthMapping (isWidthCompatSource)

/-- Every codepoint in the inclusive Hangul syllable range
    `[0xAC00, 0xD7A4]` is a non-width-compat-source. The upper inclusive
    bound covers the off-by-one edge that `Hangul.composePair?` may
    produce when the T-jamo offset saturates its maximum (`TCount = 28`).
    Closed by `native_decide` over 11173 cases. -/
theorem hangulFull_range_non_widthCompatSource :
    (List.range 11173).all
      (fun i => !isWidthCompatSource (0xAC00 + i)) = true := by
  native_decide

/-- Any UnicodeData row whose codepoint has a non-empty canonical
    decomposition is itself a non-width-compat-source. Unicode field
    constraint: a codepoint has at most one `Decomposition_Mapping`
    entry, so a canonical decomp and a `<wide>`/`<narrow>` compat decomp
    are mutually exclusive. Closed by `native_decide` over the pinned
    UnicodeData table. -/
theorem rows_with_canonical_decomp_non_widthCompatSource :
    UnicodeData.rows.all
      (fun row =>
        row.canonicalDecomposition.isEmpty
          || !isWidthCompatSource row.codepoint) = true := by
  native_decide

/-- `Hangul.composePair?` output, when `some`, lies in the inclusive
    range `[0xAC00, 0xD7A4]`. The LV branch produces
    `SBase + (lIndex * VCount + vIndex) * TCount` with
    `lIndex * VCount + vIndex < LCount * VCount = NCount`, hence strictly
    less than `SBase + SCount`. The LVT branch produces
    `first + (second - TBase)` with `first ∈ [SBase, SBase + SCount)`
    and `second ∈ (TBase, TBase + TCount]`, hence the sum is at most
    `SBase + SCount = 0xD7A4`. -/
theorem composePair_output_range
    (a b p : Nat) (h : Hangul.composePair? a b = some p) :
    0xAC00 ≤ p ∧ p ≤ 0xD7A4 := by
  unfold Hangul.composePair? at h
  split at h
  · next hLV =>
    obtain ⟨hL, hV⟩ := hLV
    simp only [Hangul.isLJamo, Hangul.LBase, Hangul.LCount] at hL
    simp only [Hangul.isVJamo, Hangul.VBase, Hangul.VCount] at hV
    have hLR := of_decide_eq_true hL
    have hVR := of_decide_eq_true hV
    simp only [Option.some.injEq] at h
    subst h
    simp only [Hangul.SBase, Hangul.VCount, Hangul.TCount, Hangul.LBase, Hangul.VBase]
    refine ⟨by omega, ?upperBound⟩
    omega
  · split at h
    · next hLVT =>
      obtain ⟨hS, hT⟩ := hLVT
      simp only [Hangul.isHangulSyllable, Hangul.SBase, Hangul.SCount,
                 Hangul.LCount, Hangul.NCount, Hangul.VCount, Hangul.TCount] at hS
      simp only [Hangul.isTJamo, Hangul.TBase, Hangul.TCount] at hT
      have hSR := of_decide_eq_true hS
      have hTR := of_decide_eq_true hT
      change (if (a - Hangul.SBase) % Hangul.TCount = 0
                then some (a + (b - Hangul.TBase)) else none) = some p at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [Hangul.TBase, Hangul.SBase, Hangul.TCount] at *
        refine ⟨by omega, by omega⟩
      · simp at h
    · simp at h

/-- `Hangul.composePair?` output, when `some`, is a non-width-compat-source. -/
theorem composePair_output_non_widthCompatSource
    (a b p : Nat) (h : Hangul.composePair? a b = some p) :
    isWidthCompatSource p = false := by
  obtain ⟨hLo, hHi⟩ := composePair_output_range a b p h
  have hiLt : p - 0xAC00 < 11173 := by omega
  have hCpEq : 0xAC00 + (p - 0xAC00) = p := by omega
  have hTable := hangulFull_range_non_widthCompatSource
  rw [List.all_eq_true] at hTable
  have hI : p - 0xAC00 ∈ List.range 11173 := List.mem_range.mpr hiLt
  have hAt := hTable (p - 0xAC00) hI
  rw [hCpEq] at hAt
  simpa using hAt

/-- Primary-composite output is always a non-width-compat-source. Case
    on `Hangul.composePair?`: the Hangul branch is discharged by
    `composePair_output_non_widthCompatSource`; the UnicodeData branch
    finds a row with matching canonical decomposition, and such rows
    have non-width-compat-source codepoints by
    `rows_with_canonical_decomp_non_widthCompatSource`. -/
theorem primaryComposite_non_widthCompatSource
    (d c p : Nat) (h : primaryComposite? d c = some p) :
    isWidthCompatSource p = false := by
  unfold primaryComposite? at h
  split at h
  · next q hq =>
    simp only [Option.some.injEq] at h
    subst h
    exact composePair_output_non_widthCompatSource d c q hq
  · have hTable := rows_with_canonical_decomp_non_widthCompatSource
    rw [Array.all_eq_true] at hTable
    obtain ⟨row, hRowMem, hFEq⟩ := Array.exists_of_findSome?_eq_some h
    rcases Array.getElem_of_mem hRowMem with ⟨i, hi, hElem⟩
    have hRowAll := hTable i hi
    rw [hElem] at hRowAll
    split at hFEq
    · next hCond =>
      obtain ⟨hDec, hNotExcl⟩ := hCond
      clear hNotExcl
      simp only [Option.some.injEq] at hFEq
      rw [hFEq] at hRowAll
      rw [hDec] at hRowAll
      simp at hRowAll
      exact hRowAll
    · simp at hFEq

/-- State invariant for `compose`: all codepoints reachable through
    emitted/starter/buffer satisfy the predicate `P`. -/
def AllSatisfiesP (P : Nat → Bool) (s : ComposeState) : Prop :=
  (∀ x ∈ s.emitted, P x = true)
    ∧ (∀ x, s.starter = some x → P x = true)
    ∧ (∀ x ∈ s.buffer, P x = true)

theorem initial_state_AllSatisfiesP (P : Nat → Bool) :
    AllSatisfiesP P initialState := by
  refine ⟨?emitInv, ?starterInv, ?bufInv⟩
  · intro x hx; simp [initialState] at hx
  · intro x hx; simp [initialState] at hx
  · intro x hx; simp [initialState] at hx

/-- Specialized step preservation for the non-width-compat-source
    predicate. The primary-composite branches supply their preservation
    witness through `primaryComposite_non_widthCompatSource`. -/
theorem stepCompose_preserves_non_widthCompatSource
    (s : ComposeState) (cp : Nat) (hCp : isWidthCompatSource cp = false)
    (hInv : AllSatisfiesP (fun x => !isWidthCompatSource x) s) :
    AllSatisfiesP (fun x => !isWidthCompatSource x) (stepCompose s cp) := by
  obtain ⟨hE, hStar, hBuf⟩ := hInv
  have hCpP : (fun x => !isWidthCompatSource x) cp = true := by simp [hCp]
  unfold stepCompose
  cases hS : s.starter with
  | none =>
    by_cases hCCC : Lookup.canonicalCombiningClass cp = 0
    · simp only [hCCC, if_true]
      refine ⟨hE, ?starterInvA, hBuf⟩
      intro x hx
      rw [← Option.some.inj hx]
      exact hCpP
    · simp only [hCCC, if_false]
      refine ⟨?emitInvB, ?starterInvB, hBuf⟩
      · intro x hx
        rcases Array.mem_append.mp hx with h1 | h2
        · exact hE x h1
        · simp at h2; rw [h2]; exact hCpP
      · intro x hx
        simp at hx
  | some st =>
    by_cases hCCC : Lookup.canonicalCombiningClass cp = 0
    · simp only [hCCC, if_true]
      by_cases hBufEm : s.buffer.isEmpty = true
      · simp only [hBufEm, if_true]
        cases hPrim : primaryComposite? st cp with
        | some p =>
          refine ⟨hE, ?starterInvC, hBuf⟩
          intro x hx
          rw [← Option.some.inj hx]
          have hP : isWidthCompatSource p = false :=
            primaryComposite_non_widthCompatSource st cp p hPrim
          simp [hP]
        | none =>
          refine ⟨?emitInvD, ?starterInvD, ?bufInvD⟩
          · intro x hx
            rcases Array.mem_append.mp hx with h1 | h2
            · exact hE x h1
            · simp at h2; rw [h2]; exact hStar st hS
          · intro x hx
            rw [← Option.some.inj hx]; exact hCpP
          · intro x hx; simp at hx
      · simp only [hBufEm]
        refine ⟨?emitInvE, ?starterInvE, ?bufInvE⟩
        · intro x hx
          rcases Array.mem_append.mp hx with h1 | h2
          · rcases Array.mem_append.mp h1 with h1a | h1b
            · exact hE x h1a
            · simp at h1b; rw [h1b]; exact hStar st hS
          · rw [List.mem_toArray, List.mem_reverse] at h2
            exact hBuf x h2
        · intro x hx
          rw [← Option.some.inj hx]; exact hCpP
        · intro x hx; simp at hx
    · simp only [hCCC, if_false]
      by_cases hBlock : Lookup.canonicalCombiningClass cp ≤ s.maxCCC
      · simp only [hBlock, if_true]
        refine ⟨hE, ?starterInvF, ?bufInvF⟩
        · intro x hx
          rw [← Option.some.inj hx]
          exact hStar st hS
        · intro x hx
          rcases List.mem_cons.mp hx with h1 | h2
          · rw [h1]; exact hCpP
          · exact hBuf x h2
      · simp only [hBlock, if_false]
        cases hPrim : primaryComposite? st cp with
        | some p =>
          refine ⟨hE, ?starterInvG, hBuf⟩
          intro x hx
          rw [← Option.some.inj hx]
          have hP : isWidthCompatSource p = false :=
            primaryComposite_non_widthCompatSource st cp p hPrim
          simp [hP]
        | none =>
          refine ⟨hE, ?starterInvH, ?bufInvH⟩
          · intro x hx
            rw [← Option.some.inj hx]
            exact hStar st hS
          · intro x hx
            rcases List.mem_cons.mp hx with h1 | h2
            · rw [h1]; exact hCpP
            · exact hBuf x h2

/-- `flushCompose` preserves the predicate: every output codepoint
    comes from `emitted`, `starter`, or the (reversed) buffer. -/
theorem flushCompose_preserves_non_widthCompatSource
    (s : ComposeState)
    (hInv : AllSatisfiesP (fun x => !isWidthCompatSource x) s) :
    ∀ j ∈ flushCompose s, isWidthCompatSource j = false := by
  obtain ⟨hE, hStar, hBuf⟩ := hInv
  intro j hj
  unfold flushCompose at hj
  split at hj
  · next st hSt =>
    rcases Array.mem_append.mp hj with h1 | h2
    · rcases Array.mem_append.mp h1 with h1a | h1b
      · have := hE j h1a; simpa using this
      · simp at h1b
        rw [h1b]
        have := hStar st hSt
        simpa using this
    · rw [List.mem_toArray, List.mem_reverse] at h2
      have := hBuf j h2
      simpa using this
  · next hSt =>
    rcases Array.mem_append.mp hj with h1 | h2
    · have := hE j h1; simpa using this
    · rw [List.mem_toArray, List.mem_reverse] at h2
      have := hBuf j h2
      simpa using this

/-- **Sequence-level preservation.** If every input codepoint is a
    non-width-compat-source, every output codepoint of `compose` is
    also a non-width-compat-source. -/
theorem compose_preserves_non_widthCompatSource
    (cps : Array Nat) (h : ∀ cp ∈ cps, isWidthCompatSource cp = false) :
    ∀ j ∈ compose cps, isWidthCompatSource j = false := by
  unfold compose
  have hFold : AllSatisfiesP (fun x => !isWidthCompatSource x)
                  (cps.foldl stepCompose initialState) := by
    rw [← Array.foldl_toList]
    have key : ∀ (l : List Nat) (s : ComposeState),
        (∀ x ∈ l, isWidthCompatSource x = false) →
        AllSatisfiesP (fun x => !isWidthCompatSource x) s →
        AllSatisfiesP (fun x => !isWidthCompatSource x) (l.foldl stepCompose s) := by
      intro l
      induction l with
      | nil => intro s hL hS; simpa using hS
      | cons hd tl ih =>
        intro s hL hS
        simp only [List.foldl_cons]
        apply ih (stepCompose s hd) (fun y hy => hL y (by simp [hy]))
        exact stepCompose_preserves_non_widthCompatSource s hd
          (hL hd (by simp)) hS
    exact key cps.toList initialState
      (fun x hx => h x (by simpa using hx))
      (initial_state_AllSatisfiesP (fun x => !isWidthCompatSource x))
  exact flushCompose_preserves_non_widthCompatSource
    (cps.foldl stepCompose initialState) hFold

end WidthCompatPreservation

end Unicode.Normalization.Compose
