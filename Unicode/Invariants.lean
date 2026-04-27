/-
  Unicode.Invariants

  Refinement-type invariants for Unicode normalization pipeline stages.

  Canon precedent: `Continuity.Gateway.Request` uses `Temperature`, `Port`,
  `Penalty` as refinement types with structural validity proofs. This module
  carries that idiom to the Unicode pipeline — each normalization stage
  consumes and produces `Array Nat` tagged with a structural invariant, so
  composition threads the invariants through the type system rather than
  through hand-proven preservation lemmas at every step.

  ## Structural rather than circular

  Each invariant is defined STRUCTURALLY (not as "function f is identity on
  this input"), so that:
    * `reorder` producing `HasSortedRuns` is a proof obligation on
      `reorder`'s implementation, not a recursive claim.
    * Idempotence of `widthMap`, `caseFold`, etc. follows from
      "structural invariant ⇒ function is identity on the input" — a
      fact about the function shape, not a chicken-and-egg.

  ## Scope

  NFC's structural invariant (`IsNFC`) has three pieces: sorted runs, full
  canonical decomposition, no unblocked primary-composable adjacent pair.
  This module defines the first two plus the leaf invariants; the third
  closes as part of the `decompose_compose_inversion` work (pillar 2 of
  NFC idempotence).
-/

import Unicode.Normalization.Hangul
import Unicode.Normalization.Lookup
import Unicode.Normalization.Reorder
import Unicode.Precis.WidthMapping
import Unicode.Precis.CaseMapping
import Unicode.Precis.Categories

namespace Unicode.Invariants

open Unicode.Normalization

-- ═══════════════════════════════════════════════════════════════════════════════
-- LEAF INVARIANTS (structural, pointwise)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Every codepoint is absent from the `<wide>`/`<narrow>` compat source
    column of UCD. Equivalent to `widthMap cps = cps`. -/
def IsWidthMapped (cps : Array Nat) : Prop :=
  ∀ cp ∈ cps, Precis.WidthMapping.isWidthCompatSource cp = false

/-- Every codepoint has no default full case-fold (status C or F entry).
    Equivalent to `caseFold cps = cps`. -/
def IsCaseFolded (cps : Array Nat) : Prop :=
  ∀ cp ∈ cps, Precis.CaseMapping.isCaseFoldSource cp = false

/-- Every codepoint has no canonical decomposition AND is not a precomposed
    Hangul syllable. Equivalent to "applying `fullCanonicalDecompose` to
    any element returns the singleton `#[cp]`". -/
def IsFullyDecomposed (cps : Array Nat) : Prop :=
  ∀ cp ∈ cps,
    Lookup.canonicalDecomposition cp = #[] ∧ Hangul.isHangulSyllable cp = false

/-- Every codepoint is admissible under the PRECIS IdentifierClass
    (UTS #39 Identifier_Status = Allowed and no disallowed PRECIS category). -/
def IsAllAdmissible (cps : Array Nat) : Prop :=
  ∀ cp ∈ cps, Precis.Categories.isPrecisAdmissible cp = true

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRUCTURAL INVARIANTS (fold/sort shape)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Canonical combining class ordering on non-starter runs (UAX #15 §1.3). -/
def IsHSR (cps : Array Nat) : Prop := Reorder.HasSortedRuns cps.toList

-- ═══════════════════════════════════════════════════════════════════════════════
-- REFINED ARRAY TYPES
--
-- `{ cps : Array Nat // P cps }` gives the pipeline stages typed outputs
-- the same way `Port` / `Temperature` / `Bounded α box n` work in
-- `Continuity.Gateway` and `Continuity.Codec.Guards`.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Width-mapped codepoint sequence: no `<wide>`/`<narrow>` sources. -/
abbrev WidthMappedArray : Type := { cps : Array Nat // IsWidthMapped cps }

/-- Case-folded codepoint sequence: no case-fold sources remain. -/
abbrev CaseFoldedArray : Type := { cps : Array Nat // IsCaseFolded cps }

/-- Fully decomposed codepoint sequence: no canonical decomposition, no
    Hangul syllables. The natural input type for `compose`. -/
abbrev FullyDecomposedArray : Type := { cps : Array Nat // IsFullyDecomposed cps }

/-- Admissible codepoint sequence: every codepoint is PRECIS-admissible. -/
abbrev AdmissibleArray : Type := { cps : Array Nat // IsAllAdmissible cps }

/-- CCC-sorted-runs codepoint sequence: structural output of `reorder`. -/
abbrev HSRArray : Type := { cps : Array Nat // IsHSR cps }

-- ═══════════════════════════════════════════════════════════════════════════════
-- BASIC INTERACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The empty array satisfies every leaf invariant vacuously. -/
theorem IsWidthMapped_empty : IsWidthMapped #[] := by
  intro cp hMem; simp at hMem

theorem IsCaseFolded_empty : IsCaseFolded #[] := by
  intro cp hMem; simp at hMem

theorem IsFullyDecomposed_empty : IsFullyDecomposed #[] := by
  intro cp hMem; simp at hMem

theorem IsAllAdmissible_empty : IsAllAdmissible #[] := by
  intro cp hMem; simp at hMem

theorem IsHSR_empty : IsHSR #[] := by
  unfold IsHSR
  simp

end Unicode.Invariants
