/-
  Unicode.Precis.Preparation

  The PRECIS Preparation algorithm per
  RFC 8264 §5 and RFC 8265 §5 for the UsernameCaseMapped and
  UsernameCasePreserved profiles built on top of the IdentifierClass.

  The pipeline applies the four RFC 8264/8265 rules in order:

    1. Width Mapping      (`Precis.WidthMapping.widthMap`)
    2. Additional Mapping (identity — no profile-specific mapping
                           required for UsernameCaseMapped)
    3. Case Mapping       (`Precis.CaseMapping.caseFold`)
    4. Normalization      (NFC, via `Unicode.Normalization.NFC.toNFC`)

  followed by the admissibility gate (`Precis.Categories.
  isPrecisAdmissible` applied pointwise — identical to the
  IdentifierClass membership predicate under the current
  categorization).

  The reject-on-disallowed check is applied LAST per RFC 8264 §5.2.4:
  the admissibility verdict is taken over the prepared form so that
  a codepoint mapped into IdentifierClass by width-mapping or
  case-folding still admits even when its source codepoint was
  categorized differently.

  # Idempotence

  `precis_idempotent` closes RFC 8264/8265 §7 idempotence
  unconditionally for the UsernameCaseMapped profile. The closure
  path passes through `Unicode.CaseFoldRoundtrip.caseFoldNfcRoundtripFixed_holds`,
  which discharges the round-trip fixed point via a restricted
  sequence lift rather than the universal `CaseFoldNfdCommutesSeq`
  that was originally proposed here — the universal is false (U+0345
  counter-example; see `CaseFoldRoundtrip` header for details).

  Stage-level idempotences for `widthMap` and `caseFold` are proven
  in `Precis.WidthMapping.widthMap_idempotent` and
  `Precis.CaseMapping.caseFold_idempotent`; the NFC step is
  `Unicode.Normalization.ComposeInversion.toNFC_idempotent`. Concrete
  test-vector idempotence is also established here via `native_decide`.
-/

import Unicode.Normalization.NFC
import Unicode.Normalization.NFD
import Unicode.Normalization.ComposeInversion
import Unicode.CaseFoldRoundtrip
import Unicode.Precis.BidiRule
import Unicode.Precis.IdentifierClass
import Unicode.Precis.WidthMapping
import Unicode.Precis.CaseMapping
import Unicode.Precis.Categories

namespace Unicode.Precis.Preparation

open Unicode.Normalization.NFC (toNFC)
open Unicode.Precis.IdentifierClass (isAllowedInIdentifierClass)
open Unicode.Precis.WidthMapping (widthMap)
open Unicode.Precis.CaseMapping (caseFold)
open Unicode.Precis.Categories (isPrecisAdmissible)
open Unicode.Precis.BidiRule (satisfiesBidiRule)

/-- The RFC 8264/8265 mapping stages: width-map, then case-fold,
    then NFC. Admissibility is NOT checked here; it is applied to
    the output by `precisPreparation` below. Exposed as its own
    function so stage-level theorems can name it. -/
def precisMap (cps : Array Nat) : Array Nat :=
  toNFC (caseFold (widthMap cps))

/-- Per-codepoint admissibility check against the post-mapping
    sequence. -/
def allAdmissible (cps : Array Nat) : Bool :=
  cps.all isPrecisAdmissible

/-- Combined gate for UsernameCaseMapped / UsernameCasePreserved:
    IdentifierClass admissibility (RFC 8264 §5.6) AND RFC 5893 §2
    Bidi Rule (mandated by RFC 8265 §5.5). -/
def isGatePass (cps : Array Nat) : Bool :=
  allAdmissible cps && satisfiesBidiRule cps

/-- The full PRECIS Preparation: apply the mapping stages, then
    reject if the result fails `isGatePass`.

    Returns `some prepared` on success and `none` on rejection. -/
def precisPreparation (cps : Array Nat) : Option (Array Nat) :=
  let mapped := precisMap cps
  if isGatePass mapped then some mapped else none

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS — ADMISSIBLE (PASS)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty input passes preparation (no codepoints to classify). -/
theorem prep_empty : precisPreparation #[] = some #[] := by native_decide

/-- Pure-lowercase ASCII identifier is unchanged. -/
theorem prep_alice :
    precisPreparation #[0x61, 0x6C, 0x69, 0x63, 0x65]
      = some #[0x61, 0x6C, 0x69, 0x63, 0x65] := by native_decide

/-- Pure-uppercase ASCII identifier folds to lowercase. -/
theorem prep_uppercase_ALICE :
    precisPreparation #[0x41, 0x4C, 0x49, 0x43, 0x45]
      = some #[0x61, 0x6C, 0x69, 0x63, 0x65] := by native_decide

/-- Fullwidth ASCII identifier is width-mapped to ASCII then
    case-folded. `Ａｌｉｃｅ` (U+FF21 U+FF4C U+FF49 U+FF43 U+FF45)
    prepares to `alice`. -/
theorem prep_fullwidth_Alice :
    precisPreparation #[0xFF21, 0xFF4C, 0xFF49, 0xFF43, 0xFF45]
      = some #[0x61, 0x6C, 0x69, 0x63, 0x65] := by native_decide

/-- SHARP S prepares to `ss` via the case-folding step. -/
theorem prep_sharp_s :
    precisPreparation #[0x00DF] = some #[0x0073, 0x0073] := by native_decide

/-- Underscore and digit both admit. -/
theorem prep_underscore_digits :
    precisPreparation #[0x005F, 0x0030, 0x0031]
      = some #[0x005F, 0x0030, 0x0031] := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS — REJECTED
-- ═══════════════════════════════════════════════════════════════════════════════

/-- ASCII SPACE is rejected (not admissible in IdentifierClass). -/
theorem prep_rejects_space :
    precisPreparation #[0x0020] = none := by native_decide

/-- RIGHT-TO-LEFT OVERRIDE is rejected (Trojan Source vector). -/
theorem prep_rejects_bidi_override :
    precisPreparation #[0x202E] = none := by native_decide

/-- ZERO WIDTH SPACE is rejected (invisible content). -/
theorem prep_rejects_zwsp :
    precisPreparation #[0x200B] = none := by native_decide

/-- An otherwise-valid identifier containing a disallowed codepoint
    is rejected — the category check fails on the disallowed byte
    even though the surrounding ASCII would admit. -/
theorem prep_rejects_mixed :
    precisPreparation #[0x61, 0x202E, 0x62] = none := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- IDEMPOTENCE — CONCRETE VECTORS
-- Double-application of `precisPreparation` on each admissible
-- vector above returns the same result. The closed-form
-- `precis_idempotent : ∀ cps, precisPreparation cps = some out →
-- precisPreparation out = some out` follows structurally from
-- `toNFC_idempotent` and is stated below as a conditional theorem
-- that closes automatically when `toNFC_idempotent` lands.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty input is idempotent under preparation. -/
theorem prep_idempotent_empty :
    precisPreparation #[] >>= precisPreparation = some #[] := by native_decide

/-- Already-lowercase ASCII is idempotent under preparation. -/
theorem prep_idempotent_alice :
    (precisPreparation #[0x61, 0x6C, 0x69, 0x63, 0x65]).bind precisPreparation
      = some #[0x61, 0x6C, 0x69, 0x63, 0x65] := by native_decide

/-- Applying preparation to the already-folded `alice` output
    equals `some alice`. -/
theorem prep_idempotent_alice_from_fullwidth :
    (precisPreparation #[0xFF21, 0xFF4C, 0xFF49, 0xFF43, 0xFF45]).bind precisPreparation
      = some #[0x61, 0x6C, 0x69, 0x63, 0x65] := by native_decide

/-- Sharp-s's output `ss` is a fixed point of preparation. -/
theorem prep_idempotent_sharp_s :
    (precisPreparation #[0x00DF]).bind precisPreparation
      = some #[0x0073, 0x0073] := by native_decide

/-- Capital ALICE folds to alice; re-applying preparation leaves it
    unchanged. -/
theorem prep_idempotent_uppercase_ALICE :
    (precisPreparation #[0x41, 0x4C, 0x49, 0x43, 0x45]).bind precisPreparation
      = some #[0x61, 0x6C, 0x69, 0x63, 0x65] := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONDITIONAL UNIVERSAL IDEMPOTENCE
--
-- The four hypotheses below are the load-bearing pieces. Three are
-- NFC-level claims that close once `toNFC_idempotent` and the
-- stage-non-interference lemmas for NFC land in
-- `Unicode.Normalization.NFC`; the fourth is unconditionally proven
-- by `WidthMapping.widthMap_idempotent` and
-- `CaseMapping.caseFold_idempotent` and does not appear as a
-- hypothesis.
--
-- When the three NFC hypotheses are discharged at the call site,
-- `precisMap_idempotent_given` becomes unconditional, and the
-- derived `precis_idempotent_given` closes the headline RFC
-- 8264/8265 idempotence theorem.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- NFC is idempotent: applying canonical normalization twice equals
    applying it once. -/
def NfcIdempotent : Prop := ∀ cs, toNFC (toNFC cs) = toNFC cs

/-- NFC does not introduce width-compat sources. Since NFC applies
    only canonical (not compatibility) decomposition, and `<wide>` /
    `<narrow>` are compatibility-only decomposition tags, NFC's
    output inventory is a subset of the input plus canonical-
    decomposition targets — neither category contains a width-compat
    source when the input does not. Closable as a table-level check
    over `UnicodeData.rows` plus a structural Decompose/Reorder/Compose
    lift. -/
def NfcPreservesNonWidthCompatSource : Prop :=
  ∀ cs, (∀ cp ∈ cs, WidthMapping.isWidthCompatSource cp = false) →
        ∀ cp ∈ toNFC cs, WidthMapping.isWidthCompatSource cp = false

/-- `caseFold ∘ toNFC` is idempotent on the output of `caseFold ∘ widthMap`.

    The analogous per-stage claim — "`toNFC` preserves non-case-fold-source"
    — is **false** in UCD 17.0: there are 51 UnicodeData rows where a
    lowercase base plus a combining mark composes to a precomposed form
    which is itself a case-fold source (the U+01F0 family: `ǰ` folds
    with status F to `j + COMBINING CARON`, and primary-composing
    `j + combining caron` yields `ǰ`). These codepoints make each
    individual stage non-idempotent in isolation, yet the pipeline is
    idempotent because `caseFold` and `toNFC` form a round-trip on
    them: `caseFold ǰ = j + caron`, then `toNFC (j + caron) = ǰ`.

    The correct invariant for RFC 8264/8265 PRECIS idempotence is the
    round-trip fixed point below: running `caseFold ∘ toNFC` twice
    equals running it once. When discharged at the call site, this
    combined with `NfcIdempotent` closes PRECIS idempotence on any
    input whose width-compat sources have already been eliminated. -/
def CaseFoldNfcRoundtripFixed : Prop :=
  ∀ cs, toNFC (caseFold (toNFC (caseFold cs))) = toNFC (caseFold cs)

/-- **Conditional universal idempotence of `precisMap`.**

    Given the three hypotheses — NFC idempotence, NFC preserving
    non-width-compat-sources, and the caseFold ∘ toNFC round-trip
    fixed point — `precisMap` is idempotent on every codepoint
    sequence.

    The proof chains:

      Let `y := precisMap cps = toNFC (caseFold (widthMap cps))`.
      Applying `precisMap` again gives `toNFC (caseFold (widthMap y))`.

      1. `y` has no width-compat sources, so `widthMap y = y`:
         - `widthMap cps` has none (from `widthMap_output_all_non_source`);
         - `caseFold` on a non-width-source input preserves the
           property (from `caseFold_output_non_widthCompatSource`);
         - `toNFC` preserves the property (by `hNfcWidth`).
         So `widthMap y = y` (by `widthMap_id_of_all_non_source`).

      2. The round-trip does NOT require `caseFold y = y`. Instead
         `hRoundtrip` gives `toNFC (caseFold y) = toNFC (caseFold
         (toNFC (caseFold (widthMap cps)))) = toNFC (caseFold
         (widthMap cps)) = y`.

    The step-by-step derivation:

        precisMap y = toNFC (caseFold (widthMap y))
                    = toNFC (caseFold y)                [widthMap y = y]
                    = toNFC (caseFold (toNFC (caseFold (widthMap cps))))
                    = toNFC (caseFold (widthMap cps))   [hRoundtrip]
                    = y                                 [definition of y]
-/
theorem precisMap_idempotent_given
    (hNfcWidth : NfcPreservesNonWidthCompatSource)
    (hRoundtrip : CaseFoldNfcRoundtripFixed)
    (cps : Array Nat) :
    precisMap (precisMap cps) = precisMap cps := by
  unfold precisMap
  -- Establish: `caseFold (widthMap cps)` has no width-sources.
  have hCwNoWidth : ∀ cp ∈ caseFold (widthMap cps),
      WidthMapping.isWidthCompatSource cp = false :=
    CaseMapping.caseFold_output_non_widthCompatSource (widthMap cps)
      (WidthMapping.widthMap_output_all_non_source cps)
  -- Lift through NFC: `y = toNFC (...)` has no width-sources.
  have hYNoWidth : ∀ cp ∈ toNFC (caseFold (widthMap cps)),
      WidthMapping.isWidthCompatSource cp = false :=
    hNfcWidth (caseFold (widthMap cps)) hCwNoWidth
  -- Step 1: widthMap y = y.
  have hWy : widthMap (toNFC (caseFold (widthMap cps)))
              = toNFC (caseFold (widthMap cps)) :=
    WidthMapping.widthMap_id_of_all_non_source
      (toNFC (caseFold (widthMap cps))) hYNoWidth
  rw [hWy]
  -- Step 2: caseFold + toNFC round-trips back to y.
  exact hRoundtrip (widthMap cps)

/-- **Conditional universal idempotence of `precisPreparation`.**

    If `precisPreparation cps = some out`, then applying preparation
    to `out` again yields `some out`. Derived from
    `precisMap_idempotent_given` plus the admissibility gate being
    deterministic. -/
theorem precis_idempotent_given
    (hNfcWidth : NfcPreservesNonWidthCompatSource)
    (hRoundtrip : CaseFoldNfcRoundtripFixed)
    (cps : Array Nat) (out : Array Nat)
    (h : precisPreparation cps = some out) :
    precisPreparation out = some out := by
  have hPMIdem : precisMap (precisMap cps) = precisMap cps :=
    precisMap_idempotent_given hNfcWidth hRoundtrip cps
  show (if isGatePass (precisMap out) then some (precisMap out) else none)
       = some out
  have hCps : (if isGatePass (precisMap cps) then some (precisMap cps) else none)
              = some out := h
  by_cases hAdm : isGatePass (precisMap cps) = true
  · rw [if_pos hAdm] at hCps
    have hOut : out = precisMap cps := (Option.some.inj hCps).symm
    rw [hOut]
    rw [hPMIdem]
    rw [if_pos hAdm]
  · rw [if_neg hAdm] at hCps
    exact absurd hCps (by simp)

/-- **Unconditional discharge** of the NFC width-compat preservation
    hypothesis. Every codepoint in `toNFC cs` is a non-width-compat-source
    whenever every codepoint in `cs` is a non-width-compat-source. Lifted
    through the Decompose → Reorder → Compose pipeline from the three
    stage-wise preservation theorems in `Unicode.Normalization.NFC`. -/
theorem nfcPreservesNonWidthCompatSource : NfcPreservesNonWidthCompatSource :=
  Unicode.Normalization.NFC.toNFC_preserves_non_widthCompatSource

/-- **One-hypothesis PRECIS idempotence.** With the width-compat preservation
    discharged unconditionally, `precis_idempotent` reduces to a single open
    hypothesis: `CaseFoldNfcRoundtripFixed`, the `caseFold ∘ toNFC` round-trip
    fixed point governing the U+01F0 family of lowercase-precomposed-with-
    combining-mark characters that are themselves case-fold sources. -/
theorem precis_idempotent_given_roundtrip
    (hRoundtrip : CaseFoldNfcRoundtripFixed)
    (cps out : Array Nat) (h : precisPreparation cps = some out) :
    precisPreparation out = some out :=
  precis_idempotent_given nfcPreservesNonWidthCompatSource hRoundtrip cps out h

/-- **One-hypothesis PRECIS map idempotence.** The `precisMap` stage (the
    map-only portion of `precisPreparation`, without the admissibility gate)
    is idempotent given only the caseFold ∘ toNFC round-trip fixed point. -/
theorem precisMap_idempotent_given_roundtrip
    (hRoundtrip : CaseFoldNfcRoundtripFixed)
    (cps : Array Nat) :
    precisMap (precisMap cps) = precisMap cps :=
  precisMap_idempotent_given nfcPreservesNonWidthCompatSource hRoundtrip cps

-- ═══════════════════════════════════════════════════════════════════════════════
-- UNCONDITIONAL PRECIS IDEMPOTENCE
--
-- `CaseFoldNfdCommutesSeq` as a UNIVERSAL over arbitrary arrays is FALSE
-- (witnessed by the input `[0x0041, 0x0345, 0x0301]` — U+0345 folds to
-- U+03B9, promoting a non-starter to a starter and shifting the
-- partition boundary that `reorder` uses to delimit CCC-sorted runs).
-- The PRECIS chain only invokes the sequence lift at two x-values, both
-- images of `caseFold` and therefore free of the U+0345 pathology.
--
-- The restricted sequence lift `toNFD_caseFold_pointwise_lift` in
-- `Unicode.CaseFoldRoundtrip` handles those two invocations directly,
-- yielding `caseFoldNfcRoundtripFixed_holds` unconditionally. The
-- `CaseFoldNfdCommutesSeq` hypothesis is therefore bypassed (not
-- discharged — it is false); the round-trip chain closes through the
-- weaker-but-sufficient restricted lift.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Unconditional PRECIS Preparation idempotence.** For every
    codepoint sequence `cps`, if `precisPreparation cps` succeeds with
    output `out`, then applying `precisPreparation` to `out` again
    returns `some out`. Closes RFC 8264/8265 §7's idempotence
    requirement for the UsernameCaseMapped profile. -/
theorem precis_idempotent
    (cps out : Array Nat) (h : precisPreparation cps = some out) :
    precisPreparation out = some out :=
  precis_idempotent_given_roundtrip
    (Unicode.CaseFoldRoundtrip.caseFoldNfcRoundtripFixed_holds) cps out h

/-- **Unconditional PRECIS map idempotence.** Companion to
    `precis_idempotent` but for the map-only stage, without the
    admissibility gate. -/
theorem precisMap_idempotent (cps : Array Nat) :
    precisMap (precisMap cps) = precisMap cps :=
  precisMap_idempotent_given_roundtrip
    (Unicode.CaseFoldRoundtrip.caseFoldNfcRoundtripFixed_holds) cps

-- ═══════════════════════════════════════════════════════════════════════════════
-- USERNAMECASEPRESERVED PROFILE (RFC 8265 §3.4)
--
-- Identical to UsernameCaseMapped except the case-folding step is
-- omitted — case is preserved. The absence of `caseFold` means the
-- U+0345 pathology that forces the restricted sequence lift in
-- UsernameCaseMapped does not arise. Idempotence is structural:
-- `widthMap` idempotence on width-compat-free input, combined with
-- `toNFC` idempotence. The admissibility gate is shared (both profiles
-- use IdentifierClass).
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Mapping stages for UsernameCasePreserved: width-map then NFC. No
    case folding. -/
def precisMapPreserved (cps : Array Nat) : Array Nat :=
  toNFC (WidthMapping.widthMap cps)

/-- Full UsernameCasePreserved preparation: `precisMapPreserved` then
    gate (admissibility + Bidi Rule). -/
def precisPreparationPreserved (cps : Array Nat) : Option (Array Nat) :=
  let mapped := precisMapPreserved cps
  if isGatePass mapped then some mapped else none

/-- **Unconditional UsernameCasePreserved map idempotence.**

    Proof chain: let `y := precisMapPreserved cps = toNFC (widthMap cps)`.
    By `WidthMapping.widthMap_output_all_non_source`, `widthMap cps` has
    no width-compat sources. By `Unicode.Normalization.NFC.
    toNFC_preserves_non_widthCompatSource`, `y` has none. By
    `WidthMapping.widthMap_id_of_all_non_source`, `widthMap y = y`. So

      precisMapPreserved y = toNFC (widthMap y)
                           = toNFC y
                           = toNFC (toNFC (widthMap cps))
                           = toNFC (widthMap cps)   [toNFC idempotent]
                           = y. -/
theorem precisMapPreserved_idempotent (cps : Array Nat) :
    precisMapPreserved (precisMapPreserved cps) = precisMapPreserved cps := by
  unfold precisMapPreserved
  have hWcNoWidth : ∀ cp ∈ WidthMapping.widthMap cps,
      WidthMapping.isWidthCompatSource cp = false :=
    WidthMapping.widthMap_output_all_non_source cps
  have hYNoWidth : ∀ cp ∈ toNFC (WidthMapping.widthMap cps),
      WidthMapping.isWidthCompatSource cp = false :=
    Unicode.Normalization.NFC.toNFC_preserves_non_widthCompatSource
      (WidthMapping.widthMap cps) hWcNoWidth
  have hWy : WidthMapping.widthMap (toNFC (WidthMapping.widthMap cps))
               = toNFC (WidthMapping.widthMap cps) :=
    WidthMapping.widthMap_id_of_all_non_source
      (toNFC (WidthMapping.widthMap cps)) hYNoWidth
  rw [hWy]
  exact Unicode.Normalization.ComposeInversion.toNFC_idempotent
    (WidthMapping.widthMap cps)

/-- **Unconditional UsernameCasePreserved preparation idempotence.**
    If `precisPreparationPreserved cps = some out`, then applying
    preparation to `out` again yields `some out`. Direct analog of
    `precis_idempotent` for the case-preserving profile. -/
theorem precis_idempotent_preserved
    (cps out : Array Nat) (h : precisPreparationPreserved cps = some out) :
    precisPreparationPreserved out = some out := by
  have hPMIdem : precisMapPreserved (precisMapPreserved cps) = precisMapPreserved cps :=
    precisMapPreserved_idempotent cps
  show (if isGatePass (precisMapPreserved out) then some (precisMapPreserved out)
        else none) = some out
  have hCps : (if isGatePass (precisMapPreserved cps) then some (precisMapPreserved cps)
               else none) = some out := h
  by_cases hAdm : isGatePass (precisMapPreserved cps) = true
  · rw [if_pos hAdm] at hCps
    have hOut : out = precisMapPreserved cps := (Option.some.inj hCps).symm
    rw [hOut]
    rw [hPMIdem]
    rw [if_pos hAdm]
  · rw [if_neg hAdm] at hCps
    exact absurd hCps (by simp)

-- ═══════════════════════════════════════════════════════════════════════════════
-- USERNAMECASEPRESERVED TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty input passes preparation. -/
theorem prepPreserved_empty : precisPreparationPreserved #[] = some #[] := by
  native_decide

/-- Pure-lowercase ASCII is unchanged — case preserved, no mapping. -/
theorem prepPreserved_alice :
    precisPreparationPreserved #[0x61, 0x6C, 0x69, 0x63, 0x65]
      = some #[0x61, 0x6C, 0x69, 0x63, 0x65] := by native_decide

/-- Pure-uppercase ASCII is preserved (unlike UsernameCaseMapped which
    folds to lowercase). -/
theorem prepPreserved_uppercase_ALICE :
    precisPreparationPreserved #[0x41, 0x4C, 0x49, 0x43, 0x45]
      = some #[0x41, 0x4C, 0x49, 0x43, 0x45] := by native_decide

/-- Mixed-case identifier is preserved. -/
theorem prepPreserved_mixed_Alice :
    precisPreparationPreserved #[0x41, 0x6C, 0x69, 0x63, 0x65]
      = some #[0x41, 0x6C, 0x69, 0x63, 0x65] := by native_decide

/-- Fullwidth ASCII is width-mapped but not case-folded. `Ａｌｉｃｅ`
    prepares to `Alice`, preserving case. -/
theorem prepPreserved_fullwidth_Alice :
    precisPreparationPreserved #[0xFF21, 0xFF4C, 0xFF49, 0xFF43, 0xFF45]
      = some #[0x41, 0x6C, 0x69, 0x63, 0x65] := by native_decide

/-- Space is still disallowed under IdentifierClass. -/
theorem prepPreserved_rejects_space :
    precisPreparationPreserved #[0x0020] = none := by native_decide

/-- Bidi override is still disallowed (Trojan Source protection). -/
theorem prepPreserved_rejects_bidi_override :
    precisPreparationPreserved #[0x202E] = none := by native_decide

-- Note: the RFC-complete OpaqueString profile (for passwords / secrets,
-- RFC 8265 §4, with non-ASCII Zs → U+0020 remap and admittance of
-- U+0020) lives in `Unicode.Precis.OpaqueString`. It is a separate
-- namespace from the UsernameCase* profiles here because its
-- admissibility rules (IdentifierClass ∪ {U+0020}) and mapping stages
-- (no width map, Zs remap, no case map, NFC) differ.

-- ═══════════════════════════════════════════════════════════════════════════════
-- OUTPUT INVARIANTS
--
-- Semantic guarantees downstream consumers can rely on without re-checking.
-- For every profile: successful preparation output is in NFC form. For
-- profiles that include specific mapping stages, additional invariants
-- hold (e.g. caseFold-stability for UsernameCaseMapped, width-compat-source-
-- freedom for both username profiles).
-- ═══════════════════════════════════════════════════════════════════════════════

/-- PRECIS UsernameCaseMapped output is in NFC form. Follows from
    `toNFC_idempotent` applied to `precisMap` which ends with `toNFC`. -/
theorem precis_output_in_NFC_mapped
    (cps out : Array Nat) (h : precisPreparation cps = some out) :
    toNFC out = out := by
  by_cases hAdm : isGatePass (precisMap cps) = true
  · have hOut : out = precisMap cps := by
      show out = toNFC (caseFold (WidthMapping.widthMap cps))
      have hRaw : (if isGatePass (precisMap cps) then some (precisMap cps)
                   else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    unfold precisMap
    exact Unicode.Normalization.ComposeInversion.toNFC_idempotent _
  · have hNone : (if isGatePass (precisMap cps) then some (precisMap cps)
                  else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

/-- PRECIS UsernameCasePreserved output is in NFC form. -/
theorem precis_output_in_NFC_preserved
    (cps out : Array Nat) (h : precisPreparationPreserved cps = some out) :
    toNFC out = out := by
  by_cases hAdm : isGatePass (precisMapPreserved cps) = true
  · have hOut : out = precisMapPreserved cps := by
      have hRaw : (if isGatePass (precisMapPreserved cps) then some (precisMapPreserved cps)
                   else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    unfold precisMapPreserved
    exact Unicode.Normalization.ComposeInversion.toNFC_idempotent _
  · have hNone : (if isGatePass (precisMapPreserved cps) then some (precisMapPreserved cps)
                  else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

/-- PRECIS UsernameCaseMapped output contains no width-compat-source
    codepoints. Follows by composing
    `WidthMapping.widthMap_output_all_non_source`,
    `CaseMapping.caseFold_output_non_widthCompatSource`, and
    `Unicode.Normalization.NFC.toNFC_preserves_non_widthCompatSource`
    along the `widthMap → caseFold → toNFC` pipeline. -/
theorem precis_output_non_widthCompatSource_mapped
    (cps out : Array Nat) (h : precisPreparation cps = some out) :
    ∀ cp ∈ out, WidthMapping.isWidthCompatSource cp = false := by
  by_cases hAdm : isGatePass (precisMap cps) = true
  · have hOut : out = precisMap cps := by
      have hRaw : (if isGatePass (precisMap cps) then some (precisMap cps)
                   else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    intro cp hcp
    unfold precisMap at hcp
    have hW : ∀ c ∈ WidthMapping.widthMap cps,
                WidthMapping.isWidthCompatSource c = false :=
      WidthMapping.widthMap_output_all_non_source cps
    have hCW : ∀ c ∈ caseFold (WidthMapping.widthMap cps),
                 WidthMapping.isWidthCompatSource c = false :=
      CaseMapping.caseFold_output_non_widthCompatSource
        (WidthMapping.widthMap cps) hW
    exact Unicode.Normalization.NFC.toNFC_preserves_non_widthCompatSource
      (caseFold (WidthMapping.widthMap cps)) hCW cp hcp
  · have hNone : (if isGatePass (precisMap cps) then some (precisMap cps)
                  else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

/-- PRECIS UsernameCasePreserved output contains no width-compat-source
    codepoints. Same pipeline as `_mapped` minus `caseFold`. -/
theorem precis_output_non_widthCompatSource_preserved
    (cps out : Array Nat) (h : precisPreparationPreserved cps = some out) :
    ∀ cp ∈ out, WidthMapping.isWidthCompatSource cp = false := by
  by_cases hAdm : isGatePass (precisMapPreserved cps) = true
  · have hOut : out = precisMapPreserved cps := by
      have hRaw : (if isGatePass (precisMapPreserved cps) then some (precisMapPreserved cps)
                   else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    intro cp hcp
    unfold precisMapPreserved at hcp
    have hW : ∀ c ∈ WidthMapping.widthMap cps,
                WidthMapping.isWidthCompatSource c = false :=
      WidthMapping.widthMap_output_all_non_source cps
    exact Unicode.Normalization.NFC.toNFC_preserves_non_widthCompatSource
      (WidthMapping.widthMap cps) hW cp hcp
  · have hNone : (if isGatePass (precisMapPreserved cps) then some (precisMapPreserved cps)
                  else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

/-- UsernameCaseMapped preparation output is admissible by
    `isPrecisAdmissible`. Follows from `isGatePass` requiring
    admissibility as one of its two conjuncts. -/
theorem precis_output_admissible_mapped
    (cps out : Array Nat) (h : precisPreparation cps = some out) :
    ∀ cp ∈ out, isPrecisAdmissible cp = true := by
  by_cases hAdm : isGatePass (precisMap cps) = true
  · have hOut : out = precisMap cps := by
      have hRaw : (if isGatePass (precisMap cps) then some (precisMap cps)
                   else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    intro cp hcp
    have hAllAdm : allAdmissible (precisMap cps) = true := by
      unfold isGatePass at hAdm
      simp only [Bool.and_eq_true] at hAdm
      exact hAdm.1
    unfold allAdmissible at hAllAdm
    rw [Array.all_eq_true] at hAllAdm
    rcases Array.getElem_of_mem hcp with ⟨i, hi, hElem⟩
    have := hAllAdm i hi
    rw [hElem] at this
    exact this
  · have hNone : (if isGatePass (precisMap cps) then some (precisMap cps)
                  else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

/-- UsernameCasePreserved preparation output is admissible. -/
theorem precis_output_admissible_preserved
    (cps out : Array Nat) (h : precisPreparationPreserved cps = some out) :
    ∀ cp ∈ out, isPrecisAdmissible cp = true := by
  by_cases hAdm : isGatePass (precisMapPreserved cps) = true
  · have hOut : out = precisMapPreserved cps := by
      have hRaw : (if isGatePass (precisMapPreserved cps)
                    then some (precisMapPreserved cps) else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    intro cp hcp
    have hAllAdm : allAdmissible (precisMapPreserved cps) = true := by
      unfold isGatePass at hAdm
      simp only [Bool.and_eq_true] at hAdm
      exact hAdm.1
    unfold allAdmissible at hAllAdm
    rw [Array.all_eq_true] at hAllAdm
    rcases Array.getElem_of_mem hcp with ⟨i, hi, hElem⟩
    have := hAllAdm i hi
    rw [hElem] at this
    exact this
  · have hNone : (if isGatePass (precisMapPreserved cps)
                   then some (precisMapPreserved cps) else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

/-- UsernameCaseMapped preparation output satisfies the RFC 5893 Bidi
    Rule. Follows from `isGatePass` requiring the rule as one of its
    two conjuncts. -/
theorem precis_output_bidi_rule_mapped
    (cps out : Array Nat) (h : precisPreparation cps = some out) :
    satisfiesBidiRule out = true := by
  by_cases hAdm : isGatePass (precisMap cps) = true
  · have hOut : out = precisMap cps := by
      have hRaw : (if isGatePass (precisMap cps) then some (precisMap cps)
                   else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    unfold isGatePass at hAdm
    simp only [Bool.and_eq_true] at hAdm
    exact hAdm.2
  · have hNone : (if isGatePass (precisMap cps) then some (precisMap cps)
                  else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

/-- UsernameCasePreserved preparation output satisfies the Bidi Rule. -/
theorem precis_output_bidi_rule_preserved
    (cps out : Array Nat) (h : precisPreparationPreserved cps = some out) :
    satisfiesBidiRule out = true := by
  by_cases hAdm : isGatePass (precisMapPreserved cps) = true
  · have hOut : out = precisMapPreserved cps := by
      have hRaw : (if isGatePass (precisMapPreserved cps)
                    then some (precisMapPreserved cps) else none) = some out := h
      rw [if_pos hAdm] at hRaw
      exact (Option.some.inj hRaw).symm
    rw [hOut]
    unfold isGatePass at hAdm
    simp only [Bool.and_eq_true] at hAdm
    exact hAdm.2
  · have hNone : (if isGatePass (precisMapPreserved cps)
                   then some (precisMapPreserved cps) else none) = some out := h
    rw [if_neg hAdm] at hNone
    exact absurd hNone (by simp)

end Unicode.Precis.Preparation
