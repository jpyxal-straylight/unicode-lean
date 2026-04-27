/-
  Unicode.Normalization.NFC

  Top-level Normalization Form C glue. Chains the three UAX #15 stages
  on a codepoint sequence:

    toNFC = compose ∘ reorder ∘ decompose

  Also exposes two quick-check predicates keyed off
  `DerivedNormalizationProps.nfcQC`:

    * `isNFCQuickCheck` — returns `true` when every codepoint in the
      sequence has `NFC_QC = Y`; proves the sequence is already in
      NFC without running the full pipeline.
    * `isNFC`           — the definitive check: `toNFC cps = cps`.
      Used when the quick check is inconclusive (any codepoint with
      `NFC_QC = M`) or when a caller wants the full round-trip
      guarantee.

  This module operates on codepoint sequences (`Array Nat`). Byte-level
  UTF-8 wrapping lands separately once the UTF-8 encode helpers are
  confirmed against the existing `Codec.Utf8` module.
-/

import Unicode.Normalization.Decompose
import Unicode.Normalization.Reorder
import Unicode.Normalization.Compose
import Unicode.Generated.DerivedNormalizationProps
import Unicode.Precis.WidthMapping

namespace Unicode.Normalization.NFC

open Unicode.Normalization
open Unicode.Generated

/-- Apply the canonical decomposition and reorder stages only — NFD.
    Available here alongside `toNFC` because downstream security
    algorithms (UTS #39 Confusables skeleton) use NFD, not NFC, as
    their normalization step. -/
def toNFD (cps : Array Nat) : Array Nat :=
  Reorder.reorder (Decompose.decomposeSequence cps)

/-- Apply the full NFC pipeline to a codepoint sequence. -/
def toNFC (cps : Array Nat) : Array Nat :=
  Compose.compose (toNFD cps)

/-- Look up a codepoint's `NFC_QuickCheck` value. Falls back to the
    source file's `@missing` default (`Y`) when the codepoint is not
    covered by any explicit range. -/
def nfcQCValue (cp : Nat) : DerivedNormalizationProps.NFC_QC :=
  match DerivedNormalizationProps.nfcQC.findSome?
          (fun ⟨min, max, v⟩ => if min ≤ cp ∧ cp ≤ max then some v else none) with
  | some v => v
  | none   => DerivedNormalizationProps.defaultNfcQC

/-- Decidable Bool analog of `Reorder.HasSortedRuns`: `true` iff every
    adjacent pair `(x, y)` with `y` a non-starter (CCC > 0) satisfies
    `CCC x ≤ CCC y`. Starters act as run boundaries; no ordering
    constraint applies when the trailing element is a starter.

    Enumerates adjacent pairs via `l.zip l.tail` — the empty-and-
    singleton cases both produce an empty zip, yielding `true`
    vacuously without a pattern-match case split. -/
def hasSortedRunsBool (l : List Nat) : Bool :=
  (l.zip l.tail).all (fun pair =>
    decide (Lookup.canonicalCombiningClass pair.2 = 0) ||
    decide (Lookup.canonicalCombiningClass pair.1
              ≤ Lookup.canonicalCombiningClass pair.2))

/-- Unfolding equation for `hasSortedRunsBool` on a non-empty cons-cons
    list, exposing the head-pair check and the recursive tail call. -/
theorem hasSortedRunsBool_cons_cons (x y : Nat) (t : List Nat) :
    hasSortedRunsBool (x :: y :: t) =
      ((decide (Lookup.canonicalCombiningClass y = 0) ||
        decide (Lookup.canonicalCombiningClass x
                  ≤ Lookup.canonicalCombiningClass y))
       && hasSortedRunsBool (y :: t)) := by
  unfold hasSortedRunsBool
  simp [List.tail_cons, List.zip_cons_cons]

/-- `hasSortedRunsBool` decides `Reorder.HasSortedRuns`: the Bool
    version returns `true` exactly when the Prop version holds. -/
theorem hasSortedRunsBool_iff_HasSortedRuns (l : List Nat) :
    hasSortedRunsBool l = true ↔ Reorder.HasSortedRuns l := by
  induction l with
  | nil =>
    exact ⟨fun x => trivial, fun x => rfl⟩
  | cons x rest ih =>
    match rest with
    | [] =>
      exact ⟨fun x => trivial, fun x => rfl⟩
    | y :: t =>
      rw [hasSortedRunsBool_cons_cons, Bool.and_eq_true,
          Reorder.HasSortedRuns_cons_cons]
      rw [Bool.or_eq_true]
      constructor
      · intro ⟨hPair, hRest⟩
        refine ⟨?fwdImpl, ih.mp hRest⟩
        intro hYccc
        rcases hPair with hZ | hLe
        · have hYZero : Lookup.canonicalCombiningClass y = 0 := of_decide_eq_true hZ
          omega
        · exact of_decide_eq_true hLe
      · intro ⟨hCond, hRest⟩
        refine ⟨?revImpl, ih.mpr hRest⟩
        by_cases hYccc : Lookup.canonicalCombiningClass y = 0
        · left; exact decide_eq_true hYccc
        · right; exact decide_eq_true (hCond (Nat.pos_of_ne_zero hYccc))

/-- Quick check per UAX #15 §A.1 full algorithm: a sequence is
    guaranteed to be in NFC when (a) every codepoint has
    `NFC_QC = Y` AND (b) the CCC values are non-decreasing within
    non-starter runs. Returns `true` on a YES-verdict, `false`
    otherwise — inconclusive (`NFC_QC = M`) or CCC-out-of-order
    cases yield `false`; callers should fall back to `isNFC` for
    the definitive answer in those situations. -/
def isNFCQuickCheck (cps : Array Nat) : Bool :=
  cps.all (fun cp => decide (nfcQCValue cp = .Y)) &&
  hasSortedRunsBool cps.toList

/-- Definitive NFC check: a sequence is in NFC iff applying the NFC
    pipeline to it is a no-op. -/
def isNFC (cps : Array Nat) : Bool :=
  toNFC cps = cps

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Empty sequence. -/
theorem toNFC_empty : toNFC #[] = #[] := by native_decide
theorem isNFC_empty : isNFC #[] = true := by native_decide

/-- Pure ASCII is always in NFC. -/
theorem toNFC_ascii :
    toNFC #[0x0048, 0x0069] = #[0x0048, 0x0069] := by native_decide  -- "Hi"
theorem isNFC_ascii : isNFC #[0x0048, 0x0069] = true := by native_decide

/-- Decomposed form reduces to precomposed under NFC. -/
theorem toNFC_composes_A_grave :
    toNFC #[0x0041, 0x0300] = #[0x00C0] := by native_decide

/-- Precomposed form is already in NFC (decomposes then recomposes). -/
theorem toNFC_idempotent_on_A_grave :
    toNFC #[0x00C0] = #[0x00C0] := by native_decide
theorem isNFC_A_grave : isNFC #[0x00C0] = true := by native_decide

/-- ANGSTROM SIGN is NOT in NFC — its canonical decomposition recomposes
    to `LATIN CAPITAL A WITH RING ABOVE` (0x00C5), not back to ANGSTROM
    (0x212B is a Full_Composition_Exclusion). -/
theorem toNFC_angstrom_to_A_ring :
    toNFC #[0x212B] = #[0x00C5] := by native_decide

/-- Out-of-order combining marks get reordered during the NFC pipeline. -/
theorem toNFC_reorders_then_composes :
    -- A + grave (230) + cedilla (202) →
    --   decompose: A + grave + cedilla (no change, no decompositions)
    --   reorder:   A + cedilla + grave (cedilla CCC=202 < grave CCC=230)
    --   compose:   A + cedilla first — no A+cedilla precomposed form
    --              keep A as starter, buffer cedilla
    --              then grave (CCC=230 > 202 buffered) — can it compose?
    --              primaryComposite?(A, grave) = À; starter := À
    --   output: À + cedilla
    toNFC #[0x0041, 0x0300, 0x0327] = #[0x00C0, 0x0327] := by native_decide

/-- Hangul: decomposed jamo LV compose to the precomposed syllable. -/
theorem toNFC_hangul_compose :
    toNFC #[0x1100, 0x1161] = #[0xAC00] := by native_decide

/-- Hangul: precomposed syllable is already in NFC. Decomposes to jamo,
    reorders (no-op for starters), recomposes back. -/
theorem toNFC_hangul_idempotent :
    toNFC #[0xAC00] = #[0xAC00] := by native_decide
theorem isNFC_hangul : isNFC #[0xAC00] = true := by native_decide

/-- `isNFCQuickCheck` is conservative: pure ASCII and standalone
    precomposed `À` both have `NFC_QC = Y` and the quick check
    returns `true`. -/
theorem quickCheck_ascii : isNFCQuickCheck #[0x0048, 0x0069] = true := by native_decide

/-- `isNFCQuickCheck` returns `false` for `NFC_QC = N` input — a
    codepoint that definitely needs normalization. COMBINING GRAVE
    TONE MARK (U+0340) has `NFC_QC = N` per the pinned tables. -/
theorem quickCheck_nfc_N : isNFCQuickCheck #[0x0340] = false := by native_decide

/-- `nfcQCValue` default: `A` has `NFC_QC = Y` (not listed in the
    pinned table; falls back to the `defaultNfcQC`). -/
theorem nfcQC_default_ascii : nfcQCValue 0x0041 = .Y := by native_decide

/-- `nfcQCValue` explicit: U+0340 is listed with `NFC_QC = N`. -/
theorem nfcQC_explicit_N : nfcQCValue 0x0340 = .N := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════════
-- WIDTH-COMPAT NON-INTERFERENCE
--
-- Canonical Normalization Form C preserves the PRECIS non-width-compat-source
-- property. Composed from stage-wise preservation lemmas in Decompose, Reorder,
-- and Compose, each of which lifts its stage's table-level non-width-compat-source
-- fact (Hangul jamo / UnicodeData canonical decomposition targets / Hangul
-- syllable range) through its respective foldl.
--
-- Used by `Unicode.Precis.Preparation` to discharge
-- `NfcPreservesNonWidthCompatSource` unconditionally.
-- ═══════════════════════════════════════════════════════════════════════════════

section WidthCompatPreservation

open Unicode.Precis.WidthMapping (isWidthCompatSource)

/-- **NFD preserves non-width-compat-source.** The decompose+reorder stages
    together never introduce width-compat-source codepoints into the output. -/
theorem toNFD_preserves_non_widthCompatSource
    (cps : Array Nat) (h : ∀ cp ∈ cps, isWidthCompatSource cp = false) :
    ∀ j ∈ toNFD cps, isWidthCompatSource j = false := by
  unfold toNFD
  intro j hj
  have hDecAll : ∀ cp ∈ Decompose.decomposeSequence cps,
                   (fun x => !isWidthCompatSource x) cp = true := by
    intro cp hcp
    have := Decompose.decomposeSequence_preserves_non_widthCompatSource cps h cp hcp
    simpa using this
  have hR := Reorder.reorder_preserves_all (fun x => !isWidthCompatSource x)
               (Decompose.decomposeSequence cps) hDecAll j hj
  simpa using hR

/-- **NFC preserves non-width-compat-source.** Pipelines decompose → reorder →
    compose — each stage has its own preservation lemma, this theorem composes
    them. -/
theorem toNFC_preserves_non_widthCompatSource
    (cps : Array Nat) (h : ∀ cp ∈ cps, isWidthCompatSource cp = false) :
    ∀ j ∈ toNFC cps, isWidthCompatSource j = false := by
  unfold toNFC
  exact Compose.compose_preserves_non_widthCompatSource (toNFD cps)
    (toNFD_preserves_non_widthCompatSource cps h)

end WidthCompatPreservation

end Unicode.Normalization.NFC
