/-
  Unicode.Precis.BidiRule

  RFC 5893 §2 Bidi Rule: six conditions that a single label in an
  internationalized domain name must satisfy when the label contains
  right-to-left characters. Referenced by RFC 8264 §5.5 / RFC 8265 §5.5
  as a mandatory enforcement step in the PRECIS Preparation pipeline.

  The six conditions (RFC 5893 §2):

    1. The first character must be a character with Bidi property
       L, R, or AL. If R or AL → RTL label; if L → LTR label.
    2. In an RTL label, only characters with the Bidi properties
       R, AL, AN, EN, ES, CS, ET, ON, BN, or NSM are allowed.
    3. In an RTL label, the end of the label must be a character with
       Bidi property R, AL, EN, or AN, followed by zero or more
       characters with Bidi property NSM.
    4. In an RTL label, if an EN is present, no AN may be present,
       and vice versa.
    5. In an LTR label, only characters with the Bidi properties
       L, EN, ES, CS, ET, ON, BN, or NSM are allowed.
    6. In an LTR label, the end of the label must be a character with
       Bidi property L or EN, followed by zero or more characters
       with Bidi property NSM.

  This module implements the rule as a pure Boolean predicate on an
  `Array Nat`; `Bidi_Class` values come from the pinned
  `Unicode.Generated.DerivedBidiClass` table. Because the rule is a
  predicate rather than a transformation, enforcing it in
  `precisPreparation*` preserves idempotence trivially: a string that
  passes the rule once continues to pass on re-application; a string
  that fails is rejected at the first application with no later state
  to reconsider.
-/

import Unicode.Generated.DerivedBidiClass

namespace Unicode.Precis.BidiRule

open Unicode.Generated.DerivedBidiClass (BidiClass)

/-- Look up a codepoint's `Bidi_Class` using the pinned
    `DerivedBidiClass` tables. Consults `explicitRanges` first; falls
    through to `defaultRanges` which cover every codepoint per UAX #9's
    default-range convention. `BidiClass.L` is a final fallback that
    should be unreachable given a well-formed UCD pin. -/
def lookupBidiClass (cp : Nat) : BidiClass :=
  match Unicode.Generated.DerivedBidiClass.explicitRanges.findSome?
          (fun ⟨min, max, c⟩ => if min ≤ cp ∧ cp ≤ max then some c else none) with
  | some c => c
  | none =>
    match Unicode.Generated.DerivedBidiClass.defaultRanges.findSome?
            (fun ⟨min, max, c⟩ => if min ≤ cp ∧ cp ≤ max then some c else none) with
    | some c => c
    | none   => BidiClass.L

-- ═══════════════════════════════════════════════════════════════════════════════
-- ALLOWED-CLASS PREDICATES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `true` iff `bc` has RTL reading direction: R, AL, or AN. These are
    the Bidi classes whose presence in a label triggers the RFC 5893
    Bidi Rule check. -/
def isRtlBidiClass (bc : BidiClass) : Bool :=
  match bc with
  | .R | .AL | .AN => true
  | .L  | .EN | .ES | .ET | .CS | .NSM | .BN | .B  | .S   | .WS
  | .ON | .LRE | .LRO | .RLE | .RLO | .PDF | .LRI | .RLI | .FSI | .PDI => false

/-- Bidi classes permitted in an LTR label per RFC 5893 §2 rule 5:
    L, EN, ES, CS, ET, ON, BN, NSM. -/
def allowedInLtrLabel (bc : BidiClass) : Bool :=
  match bc with
  | .L | .EN | .ES | .CS | .ET | .ON | .BN | .NSM => true
  | .R  | .AL | .AN | .B   | .S   | .WS  | .LRE | .LRO | .RLE | .RLO
  | .PDF | .LRI | .RLI | .FSI | .PDI => false

/-- Bidi classes permitted in an RTL label per RFC 5893 §2 rule 2:
    R, AL, AN, EN, ES, CS, ET, ON, BN, NSM. -/
def allowedInRtlLabel (bc : BidiClass) : Bool :=
  match bc with
  | .R | .AL | .AN | .EN | .ES | .CS | .ET | .ON | .BN | .NSM => true
  | .L  | .B | .S | .WS | .LRE | .LRO | .RLE | .RLO
  | .PDF | .LRI | .RLI | .FSI | .PDI => false

/-- Bidi classes permitted as the terminal non-NSM character in an LTR
    label per RFC 5893 §2 rule 6: L or EN. -/
def validLtrEndClass (bc : BidiClass) : Bool :=
  match bc with
  | .L | .EN => true
  | .R  | .AL | .AN | .ES | .CS | .ET | .ON | .BN | .NSM | .B
  | .S  | .WS | .LRE | .LRO | .RLE | .RLO | .PDF | .LRI | .RLI | .FSI | .PDI => false

/-- Bidi classes permitted as the terminal non-NSM character in an RTL
    label per RFC 5893 §2 rule 3: R, AL, EN, or AN. -/
def validRtlEndClass (bc : BidiClass) : Bool :=
  match bc with
  | .R | .AL | .EN | .AN => true
  | .L  | .ES | .CS | .ET | .ON | .BN | .NSM | .B
  | .S  | .WS | .LRE | .LRO | .RLE | .RLO | .PDF | .LRI | .RLI | .FSI | .PDI => false

/-- `true` iff `bc` has the NSM (Non-Spacing Mark) Bidi class. -/
def isNsmBidiClass (bc : BidiClass) : Bool :=
  match bc with
  | .NSM => true
  | .L  | .R | .AL | .EN | .ES | .ET | .AN | .CS | .BN
  | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
  | .LRI | .RLI | .FSI | .PDI => false

/-- `true` iff `bc` is EN (European Number). -/
def isEnBidiClass (bc : BidiClass) : Bool :=
  match bc with
  | .EN => true
  | .L  | .R | .AL | .ES | .ET | .AN | .CS | .NSM | .BN
  | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
  | .LRI | .RLI | .FSI | .PDI => false

/-- `true` iff `bc` is AN (Arabic Number). -/
def isAnBidiClass (bc : BidiClass) : Bool :=
  match bc with
  | .AN => true
  | .L  | .R | .AL | .EN | .ES | .ET | .CS | .NSM | .BN
  | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
  | .LRI | .RLI | .FSI | .PDI => false

/-- `true` iff `bc` is L (Left-to-Right). -/
def isLBidiClass (bc : BidiClass) : Bool :=
  match bc with
  | .L => true
  | .R  | .AL | .EN | .ES | .ET | .AN | .CS | .NSM | .BN
  | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
  | .LRI | .RLI | .FSI | .PDI => false

/-- `true` iff `bc` is R or AL (right-to-left strong direction). -/
def isRAlBidiClass (bc : BidiClass) : Bool :=
  match bc with
  | .R | .AL => true
  | .L  | .EN | .ES | .ET | .AN | .CS | .NSM | .BN
  | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
  | .LRI | .RLI | .FSI | .PDI => false

/-- `true` iff `bc` ∈ {L, R, AL}, per RFC 5893 §2 rule 1's allowed
    first-character classes. -/
def isFirstCharBidiClass (bc : BidiClass) : Bool :=
  match bc with
  | .L | .R | .AL => true
  | .EN | .ES | .ET | .AN | .CS | .NSM | .BN
  | .B | .S | .WS | .ON | .LRE | .LRO | .RLE | .RLO | .PDF
  | .LRI | .RLI | .FSI | .PDI => false

-- ═══════════════════════════════════════════════════════════════════════════════
-- LABEL CLASSIFICATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `true` iff the first character's Bidi class is L, R, or AL
    (RFC 5893 §2 rule 1). -/
def firstCharValid (cps : Array Nat) : Bool :=
  match cps[0]? with
  | some cp => isFirstCharBidiClass (lookupBidiClass cp)
  | none    => true  -- empty label: rule 1 vacuously satisfied.

/-- `true` iff the label is RTL (first char has class R or AL). LTR
    otherwise. An empty label is treated as LTR — the subsequent rules
    vacuously apply. -/
def isRtlLabel (cps : Array Nat) : Bool :=
  match cps[0]? with
  | some cp => isRAlBidiClass (lookupBidiClass cp)
  | none    => false

-- ═══════════════════════════════════════════════════════════════════════════════
-- TAIL-NSM STRIPPING
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Drop trailing NSM codepoints. RFC 5893 §2 rules 3 and 6 specify the
    end-of-label condition on the last non-NSM character, so NSM suffix
    must be stripped before applying those rules. Implemented as a
    fuel-bounded reverse-walk for structural termination under
    `Array`'s eager-evaluation semantics. -/
def dropTrailingNSMFuel : Nat → Array Nat → Array Nat
  | 0, cps => cps
  | fuel + 1, cps =>
    if hEmpty : cps.size = 0 then cps
    else
      let lastIdx := cps.size - 1
      have hLt : lastIdx < cps.size := by
        rcases Nat.eq_or_lt_of_le (Nat.zero_le cps.size) with hEq | hGt
        · exact absurd hEq.symm hEmpty
        · omega
      let last := cps[lastIdx]
      if isNsmBidiClass (lookupBidiClass last) then
        dropTrailingNSMFuel fuel cps.pop
      else
        cps

/-- Drop trailing NSM codepoints with a fuel bound equal to the array
    size (guaranteed termination). -/
def dropTrailingNSM (cps : Array Nat) : Array Nat :=
  dropTrailingNSMFuel cps.size cps

-- ═══════════════════════════════════════════════════════════════════════════════
-- THE SIX RULES
-- ═══════════════════════════════════════════════════════════════════════════════

/-- RFC 5893 §2 rule 4: in an RTL label, EN and AN do not coexist. -/
def noMixedEnAnInRtl (cps : Array Nat) : Bool :=
  let hasEn := cps.any (fun cp => isEnBidiClass (lookupBidiClass cp))
  let hasAn := cps.any (fun cp => isAnBidiClass (lookupBidiClass cp))
  !(hasEn && hasAn)

/-- RFC 5893 §2 rule 3: in an RTL label, the end (after stripping NSM)
    is R, AL, EN, or AN. -/
def rtlEndValid (cps : Array Nat) : Bool :=
  let stripped := dropTrailingNSM cps
  match stripped[stripped.size - 1]? with
  | some cp => validRtlEndClass (lookupBidiClass cp)
  | none    => true  -- all-NSM stripped to empty; vacuous

/-- RFC 5893 §2 rule 6: in an LTR label, the end (after stripping NSM)
    is L or EN. -/
def ltrEndValid (cps : Array Nat) : Bool :=
  let stripped := dropTrailingNSM cps
  match stripped[stripped.size - 1]? with
  | some cp => validLtrEndClass (lookupBidiClass cp)
  | none    => true

-- ═══════════════════════════════════════════════════════════════════════════════
-- THE BIDI RULE — all six conditions
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `true` iff `cps` contains at least one codepoint with Bidi class
    R, AL, or AN. RFC 5893 §1.4 defines such a label as a "Bidi label";
    the Bidi Rule applies only to Bidi labels. Per RFC 5893 and RFC
    8265 §5.5, a label that contains no RTL characters passes
    unconditionally. -/
def isBidiLabel (cps : Array Nat) : Bool :=
  cps.any (fun cp => isRtlBidiClass (lookupBidiClass cp))

/-- **RFC 5893 §2 Bidi Rule.** Returns `true` iff either:
      * `cps` is NOT a Bidi label (no R/AL/AN characters), OR
      * `cps` is a Bidi label that satisfies all six conditions.

    Per RFC 8265 §5.5: "A Bidi Rule string MUST be either a label that
    contains no RTL characters or a label that conforms to the Bidi
    Rule." This distinguishes Bidi labels (where rules 1–6 apply) from
    pure-LTR labels like `_alice01`, which pass unconditionally.

    Dispatching for Bidi labels:
      * Rule 1 (first char ∈ {L, R, AL}) must hold.
      * If first char is R or AL → RTL label; check rules 2, 3, 4.
      * If first char is L → LTR label; check rules 5, 6. -/
def satisfiesBidiRule (cps : Array Nat) : Bool :=
  if !isBidiLabel cps then true
  else if !firstCharValid cps then false
  else if isRtlLabel cps then
    cps.all (fun cp => allowedInRtlLabel (lookupBidiClass cp)) &&
    noMixedEnAnInRtl cps &&
    rtlEndValid cps
  else
    cps.all (fun cp => allowedInLtrLabel (lookupBidiClass cp)) &&
    ltrEndValid cps

-- ═══════════════════════════════════════════════════════════════════════════════
-- IDEMPOTENCE (trivial)
--
-- `satisfiesBidiRule` is a PREDICATE, not a transformation. Applying a
-- predicate check twice to the same input yields the same verdict both
-- times. When used as a gate in `precisPreparation*`, the idempotence of
-- the full pipeline is preserved: the mapping stages produce an output,
-- the Bidi rule is checked on the output, and the check is deterministic.
-- No additional idempotence proof is needed beyond the pipeline's
-- existing guarantees.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The check is pure: applying it twice gives the same answer. -/
theorem satisfiesBidiRule_deterministic (cps : Array Nat) :
    satisfiesBidiRule cps = satisfiesBidiRule cps := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty label is vacuously valid. -/
theorem bidi_empty : satisfiesBidiRule #[] = true := by native_decide

/-- Pure-ASCII LTR label passes. -/
theorem bidi_alice : satisfiesBidiRule #[0x61, 0x6C, 0x69, 0x63, 0x65] = true := by
  native_decide

/-- Mixed-case ASCII passes (all L class). -/
theorem bidi_Alice : satisfiesBidiRule #[0x41, 0x6C, 0x69, 0x63, 0x65] = true := by
  native_decide

/-- ASCII with digit passes (L followed by EN). Ends with EN which is
    valid for an LTR label. -/
theorem bidi_alice1 :
    satisfiesBidiRule #[0x61, 0x6C, 0x69, 0x63, 0x65, 0x31] = true := by native_decide

/-- Label starting with a digit + LTR chars, no RTL characters: NOT a
    Bidi label per RFC 5893 §1.4, so passes unconditionally. -/
theorem bidi_digit_start :
    satisfiesBidiRule #[0x30, 0x61, 0x6C, 0x69, 0x63, 0x65] = true := by
  native_decide

/-- RTL label starting with a digit (EN) FAILS rule 1 — first char must
    be L, R, or AL. (Example: Arabic digit + Arabic letter.) -/
theorem bidi_rtl_digit_start :
    satisfiesBidiRule #[0x0660, 0x0627] = false := by native_decide

/-- Pure Arabic identifier (RTL label). `ا` U+0627, Arabic letter alef.
    Starts and ends with AL. -/
theorem bidi_arabic :
    satisfiesBidiRule #[0x0627, 0x0644, 0x0639, 0x0631, 0x0628] = true := by
  native_decide

/-- Pure Hebrew identifier (RTL label), starts and ends with R. -/
theorem bidi_hebrew :
    satisfiesBidiRule #[0x05D0, 0x05D1, 0x05D2] = true := by native_decide

/-- Rejects: Latin start + Arabic middle + Latin end. The Arabic
    codepoint (AL) is not allowed in an LTR label. -/
theorem bidi_reject_mixed :
    satisfiesBidiRule #[0x61, 0x0627, 0x62] = false := by native_decide

end Unicode.Precis.BidiRule
