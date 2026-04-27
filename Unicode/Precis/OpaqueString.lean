/-
  Unicode.Precis.OpaqueString

  RFC 8265 §4 OpaqueString profile for password / secret inputs.
  RFC-complete on the mapping pipeline (non-ASCII Zs remap → NFC) and
  the admissibility gate (FreeformClass via General_Category from M3,
  plus RFC 5893 Bidi Rule from M4).

  Mapping stages (RFC 8265 §4.2):

    * §4.2.1 Width Mapping: none.
    * §4.2.2 Additional Mapping: non-ASCII Zs → U+0020
      (`ZsPreservation.remapZsToAscii`).
    * §4.2.3 Case Mapping: none.
    * §4.2.4 Normalization: NFC.
    * §4.2.5 Directionality: none at the mapping stage; RFC 8265
      §5.5 mandates the RFC 5893 Bidi Rule at the admissibility gate,
      which this profile enforces via `BidiRule.satisfiesBidiRule`.

  Admissibility: FreeformClass per RFC 8264 §4.3, via
  `Categories.isFreeformClassAdmissibleGC` (General_Category lookup).
  Admits letters, marks, numbers, punctuation, symbols, and Zs
  separators; rejects Cc / Cf / Cs / Co / Cn and Zl / Zp.

  Idempotence is unconditional. The structural backbone — `toNFC`
  preserves the "no non-ASCII Zs" invariant — is proven in
  `Unicode.Precis.ZsPreservation` as a separate module to keep the
  heavy UCD-table `native_decide` compilation costs out of this
  module's build graph.
-/

import Unicode.Normalization.ComposeInversion
import Unicode.Precis.ZsPreservation
import Unicode.Precis.BidiRule
import Unicode.Precis.Categories

namespace Unicode.Precis.OpaqueString

open Unicode.Normalization
open Unicode.Normalization.NFC (toNFC)
open Unicode.Precis.ZsPreservation
  (isNonAsciiZs remapZsToAscii
   remapZsToAscii_output_no_nonAsciiZs
   remapZsToAscii_id_of_no_nonAsciiZs
   toNFC_preserves_no_nonAsciiZs)
open Unicode.Precis.BidiRule (satisfiesBidiRule)

-- ═══════════════════════════════════════════════════════════════════════════════
-- ADMISSIBILITY + BIDI GATE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- OpaqueString admissibility per RFC 8264 §4.3 FreeformClass: admits
    letters, marks, numbers, punctuation, symbols, and Zs space
    separators. Rejects Cc / Cf / Cs / Co / Cn and Zl / Zp. Uses the
    `DerivedGeneralCategory` pin from M3. -/
def isOpaqueStringAdmissible (cp : Nat) : Bool :=
  Unicode.Precis.Categories.isFreeformClassAdmissibleGC cp

def allOpaqueAdmissible (cps : Array Nat) : Bool :=
  cps.all isOpaqueStringAdmissible

/-- Combined gate for OpaqueString: FreeformClass admissibility AND
    RFC 5893 §2 Bidi Rule (mandated by RFC 8265 §5.5). -/
def isOpaqueGatePass (cps : Array Nat) : Bool :=
  allOpaqueAdmissible cps && satisfiesBidiRule cps

-- ═══════════════════════════════════════════════════════════════════════════════
-- THE PROFILE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- OpaqueString mapping: non-ASCII-space remap to U+0020, then NFC. -/
def precisMapOpaque (cps : Array Nat) : Array Nat :=
  toNFC (remapZsToAscii cps)

/-- OpaqueString preparation: apply the mapping stages, then reject if
    the result fails `isOpaqueGatePass`. -/
def precisPreparationOpaque (cps : Array Nat) : Option (Array Nat) :=
  let mapped := precisMapOpaque cps
  if isOpaqueGatePass mapped then some mapped else none

-- ═══════════════════════════════════════════════════════════════════════════════
-- UNCONDITIONAL IDEMPOTENCE
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **OpaqueString mapping idempotence.**

    Proof chain:
      Let `y := toNFC (remapZsToAscii cps)`.
      `remapZsToAscii cps` has no non-ASCII Zs
      (`remapZsToAscii_output_no_nonAsciiZs`). By
      `toNFC_preserves_no_nonAsciiZs`, `y` has no non-ASCII Zs either.
      So `remapZsToAscii y = y` (`remapZsToAscii_id_of_no_nonAsciiZs`).
      Then `toNFC (remapZsToAscii y) = toNFC y = y` by
      `toNFC_idempotent`. -/
theorem precisMapOpaque_idempotent (cps : Array Nat) :
    precisMapOpaque (precisMapOpaque cps) = precisMapOpaque cps := by
  unfold precisMapOpaque
  have hRemap_no_zs : ∀ cp ∈ remapZsToAscii cps, isNonAsciiZs cp = false :=
    remapZsToAscii_output_no_nonAsciiZs cps
  have hY_no_zs : ∀ cp ∈ toNFC (remapZsToAscii cps), isNonAsciiZs cp = false :=
    toNFC_preserves_no_nonAsciiZs (remapZsToAscii cps) hRemap_no_zs
  have hRemapY : remapZsToAscii (toNFC (remapZsToAscii cps))
                   = toNFC (remapZsToAscii cps) :=
    remapZsToAscii_id_of_no_nonAsciiZs (toNFC (remapZsToAscii cps)) hY_no_zs
  rw [hRemapY]
  exact ComposeInversion.toNFC_idempotent (remapZsToAscii cps)

/-- **OpaqueString preparation idempotence.** -/
theorem precis_idempotent_opaque
    (cps out : Array Nat) (h : precisPreparationOpaque cps = some out) :
    precisPreparationOpaque out = some out := by
  have hPMIdem : precisMapOpaque (precisMapOpaque cps) = precisMapOpaque cps :=
    precisMapOpaque_idempotent cps
  show (if isOpaqueGatePass (precisMapOpaque out) then some (precisMapOpaque out)
        else none) = some out
  have hCps : (if isOpaqueGatePass (precisMapOpaque cps) then some (precisMapOpaque cps)
               else none) = some out := h
  by_cases hAdm : isOpaqueGatePass (precisMapOpaque cps) = true
  · rw [if_pos hAdm] at hCps
    have hOut : out = precisMapOpaque cps := (Option.some.inj hCps).symm
    rw [hOut, hPMIdem, if_pos hAdm]
  · rw [if_neg hAdm] at hCps
    exact absurd hCps (by simp)

-- ═══════════════════════════════════════════════════════════════════════════════
-- OUTPUT INVARIANTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- OpaqueString preparation output is in NFC form. -/
theorem precis_output_in_NFC_opaque
    (cps out : Array Nat) (h : precisPreparationOpaque cps = some out) :
    toNFC out = out := by
  by_cases hAdm : isOpaqueGatePass (precisMapOpaque cps) = true
  · have hOut : out = precisMapOpaque cps := by
      have hRaw : (if isOpaqueGatePass (precisMapOpaque cps)
                    then some (precisMapOpaque cps) else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    unfold precisMapOpaque
    exact ComposeInversion.toNFC_idempotent (remapZsToAscii cps)
  · have hNone : (if isOpaqueGatePass (precisMapOpaque cps)
                   then some (precisMapOpaque cps) else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

/-- OpaqueString preparation output contains no non-ASCII Zs (remap +
    NFC strip them; `toNFC` preserves the invariant). -/
theorem precis_output_no_nonAsciiZs_opaque
    (cps out : Array Nat) (h : precisPreparationOpaque cps = some out) :
    ∀ cp ∈ out, isNonAsciiZs cp = false := by
  by_cases hAdm : isOpaqueGatePass (precisMapOpaque cps) = true
  · have hOut : out = precisMapOpaque cps := by
      have hRaw : (if isOpaqueGatePass (precisMapOpaque cps)
                    then some (precisMapOpaque cps) else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    unfold precisMapOpaque
    exact toNFC_preserves_no_nonAsciiZs
      (remapZsToAscii cps) (remapZsToAscii_output_no_nonAsciiZs cps)
  · have hNone : (if isOpaqueGatePass (precisMapOpaque cps)
                   then some (precisMapOpaque cps) else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

/-- OpaqueString preparation output is admissible under
    `isOpaqueStringAdmissible`. -/
theorem precis_output_admissible_opaque
    (cps out : Array Nat) (h : precisPreparationOpaque cps = some out) :
    ∀ cp ∈ out, isOpaqueStringAdmissible cp = true := by
  by_cases hAdm : isOpaqueGatePass (precisMapOpaque cps) = true
  · have hOut : out = precisMapOpaque cps := by
      have hRaw : (if isOpaqueGatePass (precisMapOpaque cps)
                    then some (precisMapOpaque cps) else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    intro cp hcp
    have hAllAdm : allOpaqueAdmissible (precisMapOpaque cps) = true := by
      unfold isOpaqueGatePass at hAdm
      simp only [Bool.and_eq_true] at hAdm
      exact hAdm.1
    unfold allOpaqueAdmissible at hAllAdm
    rw [Array.all_eq_true] at hAllAdm
    rcases Array.getElem_of_mem hcp with ⟨i, hi, hElem⟩
    have := hAllAdm i hi
    rw [hElem] at this
    exact this
  · have hNone : (if isOpaqueGatePass (precisMapOpaque cps)
                   then some (precisMapOpaque cps) else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

/-- OpaqueString preparation output satisfies the Bidi Rule. -/
theorem precis_output_bidi_rule_opaque
    (cps out : Array Nat) (h : precisPreparationOpaque cps = some out) :
    satisfiesBidiRule out = true := by
  by_cases hAdm : isOpaqueGatePass (precisMapOpaque cps) = true
  · have hOut : out = precisMapOpaque cps := by
      have hRaw : (if isOpaqueGatePass (precisMapOpaque cps)
                    then some (precisMapOpaque cps) else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    unfold isOpaqueGatePass at hAdm
    simp only [Bool.and_eq_true] at hAdm
    exact hAdm.2
  · have hNone : (if isOpaqueGatePass (precisMapOpaque cps)
                   then some (precisMapOpaque cps) else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

end Unicode.Precis.OpaqueString
