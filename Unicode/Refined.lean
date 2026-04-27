/-
  Unicode.Refined

  Refinement-typed pipeline wrappers. Each Unicode normalization stage
  returns `{ out : Array Nat // P out }` where `P` is the structural
  invariant established by that stage. Composition threads the invariants
  automatically: `(reorder cps).val` on input to `compose` carries the
  `IsHSR` witness in its type.

  Canon precedent: `Continuity.Codec.Guards.Bounded` wraps a `Box α` with
  a `size_ok` proof; `Continuity.Gateway.Request.Temperature` wraps a
  `Float` with range validity. This module does the analogous wrapping
  for Unicode normalization.
-/

import Unicode.Invariants
import Unicode.Normalization.Reorder
import Unicode.Normalization.Decompose
import Unicode.Normalization.Decomposability
import Unicode.Normalization.NFC
import Unicode.Precis.WidthMapping
import Unicode.Precis.CaseMapping
import Unicode.Precis.BidiRule
import Unicode.Precis.Preparation

namespace Unicode.Refined

open Unicode.Invariants
open Unicode.Normalization

-- ═══════════════════════════════════════════════════════════════════════════════
-- LIFTED STAGES
--
-- Each underlying function already has a preservation theorem that
-- witnesses the structural invariant. We package the function + witness
-- together as the refinement-typed constructor.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `widthMap` lifted to a `WidthMappedArray`-producing function.
    Witness: `Precis.WidthMapping.widthMap_output_all_non_source`. -/
def widthMap (cps : Array Nat) : WidthMappedArray :=
  ⟨Precis.WidthMapping.widthMap cps,
   Precis.WidthMapping.widthMap_output_all_non_source cps⟩

/-- `caseFold` lifted to a `CaseFoldedArray`-producing function.
    Witness: `Precis.CaseMapping.caseFold_output_all_non_source`. -/
def caseFold (cps : Array Nat) : CaseFoldedArray :=
  ⟨Precis.CaseMapping.caseFold cps,
   Precis.CaseMapping.caseFold_output_all_non_source cps⟩

/-- `reorder` lifted to an `HSRArray`-producing function.
    Witness: `Normalization.Reorder.reorder_output_HasSortedRuns`. -/
def reorder (cps : Array Nat) : HSRArray :=
  ⟨Reorder.reorder cps, Reorder.reorder_output_HasSortedRuns cps⟩

/-- `decomposeSequence` lifted to a `FullyDecomposedArray`-producing function.
    Witness: `Normalization.Decomposability.decomposeSequence_fullyDecomposed`. -/
def decomposeSequence (cps : Array Nat) : FullyDecomposedArray :=
  ⟨Decompose.decomposeSequence cps,
   Decomposability.decomposeSequence_fullyDecomposed cps⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRUCTURAL IDEMPOTENCE
--
-- With the invariant encoded in the type, the idempotence theorems
-- reduce to: "when input carries the invariant, the function is the
-- identity". The structural facts (`widthMap_id_of_all_non_source`,
-- `caseFold_id_of_all_non_source`, `reorder_id_on_HasSortedRuns`)
-- restate cleanly against the refined type.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `widthMap` is the identity on a `WidthMappedArray`. -/
theorem widthMap_id_on_WidthMapped (x : WidthMappedArray) :
    Precis.WidthMapping.widthMap x.val = x.val :=
  Precis.WidthMapping.widthMap_id_of_all_non_source x.val x.property

/-- `caseFold` is the identity on a `CaseFoldedArray`. -/
theorem caseFold_id_on_CaseFolded (x : CaseFoldedArray) :
    Precis.CaseMapping.caseFold x.val = x.val :=
  Precis.CaseMapping.caseFold_id_of_all_non_source x.val x.property

/-- `reorder` is the identity on an `HSRArray`. -/
theorem reorder_id_on_HSR (x : HSRArray) :
    Reorder.reorder x.val = x.val :=
  Reorder.reorder_id_on_HasSortedRuns x.val x.property

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPOSITION-LEVEL IDEMPOTENCE
--
-- Applying a lifted stage to its own output yields identity at the
-- value level, because the refinement type witness establishes the
-- identity precondition. These are the "idempotent" laws expressed
-- through the refinement-type plumbing.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Refinement-typed `widthMap` is idempotent on the value projection. -/
theorem widthMap_idempotent (cps : Array Nat) :
    (widthMap (widthMap cps).val).val = (widthMap cps).val :=
  widthMap_id_on_WidthMapped (widthMap cps)

/-- Refinement-typed `caseFold` is idempotent on the value projection. -/
theorem caseFold_idempotent (cps : Array Nat) :
    (caseFold (caseFold cps).val).val = (caseFold cps).val :=
  caseFold_id_on_CaseFolded (caseFold cps)

/-- Refinement-typed `reorder` is idempotent on the value projection. -/
theorem reorder_idempotent (cps : Array Nat) :
    (reorder (reorder cps).val).val = (reorder cps).val :=
  reorder_id_on_HSR (reorder cps)

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPOUND REFINEMENTS
--
-- When a downstream stage requires multiple invariants simultaneously
-- (typical for the PRECIS pipeline), a compound refinement type captures
-- both in a single type. `caseFold` applied to a `WidthMappedArray`
-- returns a value with BOTH `IsWidthMapped` and `IsCaseFolded` — the
-- former preserved through `caseFold_output_non_widthCompatSource`,
-- the latter established by `caseFold_output_all_non_source`.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Sequence that has survived both width-mapping and case-folding:
    no `<wide>`/`<narrow>` sources AND no case-fold sources. -/
abbrev WidthCaseFoldedArray : Type :=
  { cps : Array Nat // IsWidthMapped cps ∧ IsCaseFolded cps }

/-- `caseFold` applied to a width-mapped input produces a
    width-and-case-folded result. Both invariants are witnessed in the
    output type: `IsWidthMapped` by `caseFold_output_non_widthCompatSource`,
    `IsCaseFolded` by `caseFold_output_all_non_source`. -/
def caseFoldOnWidthMapped (input : WidthMappedArray) : WidthCaseFoldedArray :=
  ⟨Precis.CaseMapping.caseFold input.val,
   ⟨Precis.CaseMapping.caseFold_output_non_widthCompatSource
     input.val input.property,
    Precis.CaseMapping.caseFold_output_all_non_source input.val⟩⟩

/-- The `widthMap` + `caseFold` composite — the first two stages of
    RFC 8265 mapping, typed to carry both preservation witnesses. -/
def widthCaseFoldMap (cps : Array Nat) : WidthCaseFoldedArray :=
  caseFoldOnWidthMapped (widthMap cps)

/-- The composite map is idempotent on the value projection: applying
    the refined composite to its own value projection yields the same
    value projection. Follows from `widthMap_id_of_all_non_source` and
    `caseFold_id_of_all_non_source` on the respective invariants. -/
theorem widthCaseFoldMap_idempotent (cps : Array Nat) :
    (widthCaseFoldMap (widthCaseFoldMap cps).val).val = (widthCaseFoldMap cps).val := by
  let x := widthCaseFoldMap cps
  have hW : IsWidthMapped x.val := x.property.1
  have hC : IsCaseFolded x.val := x.property.2
  show Precis.CaseMapping.caseFold (Precis.WidthMapping.widthMap x.val) = x.val
  rw [Precis.WidthMapping.widthMap_id_of_all_non_source x.val hW]
  exact Precis.CaseMapping.caseFold_id_of_all_non_source x.val hC

/-- The full RFC 8265 `precisMap` (`toNFC ∘ caseFold ∘ widthMap`) lifted
    to return a `WidthMappedArray`. NFC preserves non-width-compat-source
    codepoints (established unconditionally in `Precis.Preparation.nfcPreservesNonWidthCompatSource`),
    so the `IsWidthMapped` witness survives the entire pipeline.

    Note: `IsCaseFolded` is NOT preserved through NFC (the U+01F0 family —
    see `CaseFoldNfcRoundtripFixed`), so the refinement can only carry
    the width-mapped witness. -/
def precisMap (cps : Array Nat) : WidthMappedArray :=
  ⟨Precis.Preparation.precisMap cps, by
    unfold Precis.Preparation.precisMap
    have hW : IsWidthMapped (Precis.WidthMapping.widthMap cps) :=
      Precis.WidthMapping.widthMap_output_all_non_source cps
    have hC : IsWidthMapped
                (Precis.CaseMapping.caseFold (Precis.WidthMapping.widthMap cps)) :=
      Precis.CaseMapping.caseFold_output_non_widthCompatSource
        (Precis.WidthMapping.widthMap cps) hW
    exact Normalization.NFC.toNFC_preserves_non_widthCompatSource
      (Precis.CaseMapping.caseFold (Precis.WidthMapping.widthMap cps)) hC⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- PRECIS PREPARATION
--
-- `precisPreparation` returns `Option (Array Nat)` with `none` signaling
-- rejection. The refined version returns `Option AdmissibleArray` — when
-- the result is `some out`, the `IsAllAdmissible` witness is available
-- in the type.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `precisPreparation` lifted to an `Option AdmissibleArray`. The
    `allAdmissible` gate in the underlying implementation provides the
    `IsAllAdmissible` witness; the BidiRule gate is also enforced so
    this function returns `some` exactly when the unrefined
    `Precis.Preparation.precisPreparation` does. -/
def precisPreparation (cps : Array Nat) : Option AdmissibleArray :=
  let mapped := Precis.Preparation.precisMap cps
  if h : mapped.all Precis.Categories.isPrecisAdmissible = true ∧
         Precis.BidiRule.satisfiesBidiRule mapped = true then
    some ⟨mapped, by
      intro cp hMem
      have hAll := h.1
      rw [Array.all_eq_true] at hAll
      rcases Array.getElem_of_mem hMem with ⟨i, hi, hElem⟩
      have := hAll i hi
      rw [hElem] at this
      exact this⟩
  else
    none

/-- Value projection of the refined `precisPreparation` matches the
    underlying unrefined one. -/
theorem precisPreparation_val_eq (cps : Array Nat) :
    (precisPreparation cps).map Subtype.val = Precis.Preparation.precisPreparation cps := by
  unfold precisPreparation Precis.Preparation.precisPreparation
    Precis.Preparation.isGatePass Precis.Preparation.allAdmissible
  cases hadm : (Precis.Preparation.precisMap cps).all
                Precis.Categories.isPrecisAdmissible
  · cases hbidi : Precis.BidiRule.satisfiesBidiRule
                    (Precis.Preparation.precisMap cps)
    · simp [hadm, hbidi]
    · simp [hadm, hbidi]
  · cases hbidi : Precis.BidiRule.satisfiesBidiRule
                    (Precis.Preparation.precisMap cps)
    · simp [hadm, hbidi]
    · simp [hadm, hbidi]

end Unicode.Refined
