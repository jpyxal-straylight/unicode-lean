/-
  Unicode.Precis.IdentifierClass

  The `isAllowedInIdentifierClass`
  predicate per RFC 8264 (PRECIS Framework) and RFC 8265
  (IdentifierClass / UsernameCase* profiles).

  A codepoint is admissible in the IdentifierClass iff its UTS #39
  `Identifier_Status` is `Allowed`. The PRECIS Framework reaches the
  same verdict via categorization rules applied to UCD properties
  (LetterDigits, Unassigned, Disallowed, ContextO, ContextJ, etc.),
  but the equivalent and authoritative shortcut at this layer is the
  pinned IdentifierStatus data — a codepoint Allowed for identifier
  use has passed Unicode's categorization into PVALID / FREE_VAL by
  construction.

  This module is narrowly focused on the MEMBERSHIP question. Width
  mapping, case folding, and the NFC pipeline that together implement
  the full PRECIS Preparation algorithm are carried by the sibling
  modules under `Unicode.Precis.*`.
-/

import Unicode.Generated.IdentifierStatus

namespace Unicode.Precis.IdentifierClass

open Unicode.Generated

/-- `Identifier_Status` lookup: `true` when the codepoint is covered by
    the `allowedRanges` array, falling back to `.Restricted` otherwise
    (the `defaultStatus` declared in the source file's `@missing`). -/
def identifierStatus (cp : Nat) : IdentifierStatus.IdentifierStatus :=
  if IdentifierStatus.allowedRanges.any (fun ⟨min, max⟩ => decide (min ≤ cp ∧ cp ≤ max))
  then .Allowed
  else IdentifierStatus.defaultStatus

/-- PRECIS IdentifierClass membership: a codepoint is allowed in an
    IDN-safe identifier iff its UTS #39 `Identifier_Status` is
    `Allowed`. -/
def isAllowedInIdentifierClass (cp : Nat) : Bool :=
  decide (identifierStatus cp = .Allowed)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- Each anchors the table binding on a known codepoint. Disallowed
-- vectors cover the three threat-surface categories most relevant to
-- the text codec work — plain ASCII SPACE (disallowed in identifiers),
-- a bidi override (Trojan Source), and a zero-width control.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `A` is in an allowed identifier range. -/
theorem allowed_latin_A : isAllowedInIdentifierClass 0x0041 = true := by native_decide

/-- `_` is allowed (common programming-identifier character). -/
theorem allowed_underscore : isAllowedInIdentifierClass 0x005F := by native_decide

/-- A digit is allowed (permitted inside identifiers; leading-digit
    rules are a separate concern at the identifier-codec layer). -/
theorem allowed_digit : isAllowedInIdentifierClass 0x0030 = true := by native_decide

/-- SPACE is NOT allowed in identifiers — explicit in the source's
    `@missing: Restricted` default, no Allowed range covers it. -/
theorem disallowed_space : isAllowedInIdentifierClass 0x0020 = false := by native_decide

/-- RIGHT-TO-LEFT OVERRIDE (bidi override, Trojan Source vector) is
    NOT allowed. -/
theorem disallowed_bidi_override : isAllowedInIdentifierClass 0x202E = false := by native_decide

/-- ZERO WIDTH SPACE is NOT allowed. -/
theorem disallowed_zero_width_space : isAllowedInIdentifierClass 0x200B = false := by native_decide

/-- TAG LATIN CAPITAL LETTER A (Glassworm/ASCII-smuggler class) is NOT
    allowed. -/
theorem disallowed_tag_char : isAllowedInIdentifierClass 0xE0041 = false := by native_decide

end Unicode.Precis.IdentifierClass
