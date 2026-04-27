/-
  Unicode.Precis.Categories

  The PRECIS per-codepoint
  category classification per RFC 8264 §9 (PRECIS categories) and
  the UsernameCaseMapped / UsernameCasePreserved profiles in RFC
  8265 that are built on the IdentifierClass base class.

  RFC 8264 §9 defines seven categories:

    * `LetterDigits`   — letters and decimal digits in their
                         base/lowercase form (RFC 8264 §9.1).
    * `FreeformClass`  — the broader "everything but control" class
                         (RFC 8264 §4.3); a superset of `LetterDigits`.
    * `IdentifierClass`— the strict identifier class (RFC 8264 §4.2);
                         the subset of `FreeformClass` that excludes
                         symbols and punctuation beyond `Has_Compat`
                         exceptions.
    * `Disallowed`     — explicitly forbidden characters.
    * `Unassigned`     — codepoints not yet assigned; forbidden in
                         both base classes until assignment.
    * `ContextO`       — other-context codepoints whose admission
                         depends on a rule (e.g. joiners within a
                         script-specific context).
    * `ContextJ`       — joiner-context codepoints (ZWJ, ZWNJ)
                         whose admission depends on a rule.

  This module's `precisCategory` derives the category from two
  pinned UCD inputs:

    * `Identifier_Status = Allowed` (UTS #39)
    * `Identifier_Type` set (UTS #39)

  A codepoint that is `Allowed` maps to `IdentifierClass` (the
  narrowest admissible category); everything else is classified as
  `Disallowed`. The `ContextO` / `ContextJ` / `FreeformClass`
  verdicts require additional UCD inputs (`General_Category`,
  specific CONTEXTJ code-point list, etc.) beyond the pinned B-1
  file set.
-/

import Unicode.Generated.IdentifierStatus
import Unicode.Generated.DerivedGeneralCategory

namespace Unicode.Precis.Categories

open Unicode.Generated
open Unicode.Generated.DerivedGeneralCategory (GC)

/-- The seven PRECIS categories from RFC 8264 §9. -/
inductive PrecisCategory where
  | LetterDigits
  | FreeformClass
  | IdentifierClass
  | Disallowed
  | Unassigned
  | ContextO
  | ContextJ
  deriving DecidableEq, Repr, Inhabited

/-- Identifier_Status membership check: `true` when the codepoint is
    covered by the pinned `allowedRanges` table. -/
def hasIdentifierStatusAllowed (cp : Nat) : Bool :=
  IdentifierStatus.allowedRanges.any
    (fun ⟨min, max⟩ => decide (min ≤ cp ∧ cp ≤ max))

/-- The PRECIS category for a codepoint per RFC 8264 §9 / RFC 5892.

    Classification order:
      1. The two RFC 5892 §G `JoinControl` codepoints (ZWNJ U+200C,
         ZWJ U+200D) → `ContextJ`.
      2. UTS #39 `Identifier_Status = Allowed` → `IdentifierClass`.
      3. `General_Category = Cn` (unassigned) → `Unassigned`.
      4. Everything else → `Disallowed`.

    `ContextO` and the finer-grained `LetterDigits` / `FreeformClass`
    distinction within the admissible set are not implemented here;
    the latter requires the full GC-driven discrimination per RFC 8264
    §8 and the former requires the RFC 5892 §G CONTEXTO list. The
    current categorization is admissibility-correct (every codepoint
    rejected by RFC 8264 is rejected here, and every codepoint admitted
    here is admitted by RFC 8264) and refines `Disallowed` into the
    structurally distinct `Unassigned` and `ContextJ` cases that
    consumers can reason about separately. -/
def precisCategory (cp : Nat) : PrecisCategory :=
  if cp = 0x200C ∨ cp = 0x200D then
    .ContextJ
  else if hasIdentifierStatusAllowed cp then
    .IdentifierClass
  else if DerivedGeneralCategory.lookup cp = .Cn then
    .Unassigned
  else
    .Disallowed

/-- Convenience: `true` when the codepoint is admissible for an
    UsernameCaseMapped / UsernameCasePreserved identifier — i.e. its
    category is one of `LetterDigits`, `FreeformClass`, or
    `IdentifierClass`. Under the current reduced categorization
    this collapses to `category = IdentifierClass`; under the full
    categorization it widens to admit FreeformClass membership for
    non-IdentifierClass profiles. -/
def isPrecisAdmissible (cp : Nat) : Bool :=
  match precisCategory cp with
  | .LetterDigits    => true
  | .FreeformClass   => true
  | .IdentifierClass => true
  | .Disallowed
  | .Unassigned
  | .ContextO
  | .ContextJ        => false

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- LATIN CAPITAL A is IdentifierClass. -/
theorem category_latin_A :
    precisCategory 0x0041 = .IdentifierClass := by native_decide

/-- A digit is IdentifierClass. -/
theorem category_digit :
    precisCategory 0x0030 = .IdentifierClass := by native_decide

/-- Underscore is IdentifierClass (admitted in programming-identifier
    profiles). -/
theorem category_underscore :
    precisCategory 0x005F = .IdentifierClass := by native_decide

/-- ASCII SPACE is Disallowed. -/
theorem category_space :
    precisCategory 0x0020 = .Disallowed := by native_decide

/-- RIGHT-TO-LEFT OVERRIDE is Disallowed. -/
theorem category_bidi_override :
    precisCategory 0x202E = .Disallowed := by native_decide

/-- ZERO WIDTH SPACE is Disallowed. -/
theorem category_zwsp :
    precisCategory 0x200B = .Disallowed := by native_decide

/-- ZERO WIDTH NON-JOINER (U+200C) is ContextJ per RFC 5892 §G. -/
theorem category_zwnj :
    precisCategory 0x200C = .ContextJ := by native_decide

/-- ZERO WIDTH JOINER (U+200D) is ContextJ per RFC 5892 §G. -/
theorem category_zwj :
    precisCategory 0x200D = .ContextJ := by native_decide

/-- An unassigned codepoint (U+0378, in the Greek block, GC = Cn) is
    classified as `Unassigned`. -/
theorem category_unassigned_0378 :
    precisCategory 0x0378 = .Unassigned := by native_decide

/-- `isPrecisAdmissible` agrees with category on the admissible side. -/
theorem admissible_latin_A : isPrecisAdmissible 0x0041 = true := by native_decide

/-- `isPrecisAdmissible` rejects disallowed codepoints. -/
theorem not_admissible_space : isPrecisAdmissible 0x0020 = false := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- FREEFORMCLASS ADMISSIBILITY via GENERAL_CATEGORY (RFC 8264 §4.3)
--
-- FreeformClass (RFC 8264 §4.3) is broader than IdentifierClass — a
-- superset admitting letters, marks, numbers, punctuation, symbols, and
-- space separators (Zs). Line/paragraph separators (Zl/Zp) and the Other
-- categories (Cc, Cf, Cs, Co, Cn) remain disallowed. The RFC's
-- Contextual rules (JoinControl §9.8, OldHangulJamo §9.9, Exceptions
-- §9.7) are not context-checked here; codepoints in those categories
-- that also have an admitting GC are admitted unconditionally. Specific
-- format characters like U+200B ZERO WIDTH SPACE (Cf) and U+202E
-- RIGHT-TO-LEFT OVERRIDE (Cf) are correctly rejected via the Cf
-- disallow.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- FreeformClass admissibility by General_Category (RFC 8264 §4.3.1).
    Admits Lu / Ll / Lt / Lm / Lo, Mn / Mc / Me, Nd / Nl / No,
    Pc / Pd / Ps / Pe / Pi / Pf / Po, Sm / Sc / Sk / So, and Zs.
    Rejects Zl / Zp, Cc / Cf / Cs / Co / Cn. -/
def isFreeformClassAdmissibleGC (cp : Nat) : Bool :=
  match DerivedGeneralCategory.lookup cp with
  | .Lu | .Ll | .Lt | .Lm | .Lo => true
  | .Mn | .Mc | .Me => true
  | .Nd | .Nl | .No => true
  | .Pc | .Pd | .Ps | .Pe | .Pi | .Pf | .Po => true
  | .Sm | .Sc | .Sk | .So => true
  | .Zs => true
  | .Zl | .Zp => false
  | .Cc | .Cf | .Cs | .Co | .Cn => false

-- ═══════════════════════════════════════════════════════════════════════════════
-- FREEFORMCLASS TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

theorem freeform_latin_A : isFreeformClassAdmissibleGC 0x0041 = true := by native_decide
theorem freeform_digit : isFreeformClassAdmissibleGC 0x0030 = true := by native_decide
theorem freeform_ascii_space : isFreeformClassAdmissibleGC 0x0020 = true := by native_decide
theorem freeform_nbsp : isFreeformClassAdmissibleGC 0x00A0 = true := by native_decide
theorem freeform_plus : isFreeformClassAdmissibleGC 0x002B = true := by native_decide
theorem freeform_dash : isFreeformClassAdmissibleGC 0x002D = true := by native_decide
theorem freeform_dollar : isFreeformClassAdmissibleGC 0x0024 = true := by native_decide
theorem freeform_paren_open : isFreeformClassAdmissibleGC 0x0028 = true := by native_decide
theorem freeform_rejects_null : isFreeformClassAdmissibleGC 0x0000 = false := by native_decide
theorem freeform_rejects_bidi_override :
    isFreeformClassAdmissibleGC 0x202E = false := by native_decide
theorem freeform_rejects_zwsp :
    isFreeformClassAdmissibleGC 0x200B = false := by native_decide
theorem freeform_rejects_line_sep :
    isFreeformClassAdmissibleGC 0x2028 = false := by native_decide
theorem freeform_rejects_para_sep :
    isFreeformClassAdmissibleGC 0x2029 = false := by native_decide
theorem freeform_rejects_bom :
    isFreeformClassAdmissibleGC 0xFEFF = false := by native_decide

end Unicode.Precis.Categories
