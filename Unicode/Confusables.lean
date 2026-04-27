/-
  Unicode.Confusables

  UTS #39 §4 confusable-skeleton computation and the
  derived `areConfusable` relation.

  The skeleton of a codepoint sequence is defined (UTS #39 Definition
  12) as:

    skeleton(X) = toNFD(substitute(toNFD(X)))

  where `substitute` replaces each codepoint that appears as a source
  in the confusables table with its target sequence, and codepoints
  not in the table are kept unchanged.

  Two sequences are "confusable" (visually mistakable to a reader
  under generic rendering) iff their skeletons are equal. This is the
  primary test downstream identifier codecs (B-4 PRECIS, C-2
  PrecisIdentifier) use to reject IDN-class homograph attacks before
  they reach the identifier layer.
-/

import Unicode.Normalization.NFC
import Unicode.Generated.Confusables

namespace Unicode.Confusables

open Unicode
open Unicode.Generated

/-- Look up a codepoint in the confusables source column. Returns
    `some target` when the codepoint maps to a skeleton sequence,
    `none` otherwise. -/
def lookupConfusable? (cp : Nat) : Option (Array Nat) :=
  Confusables.mappings.findSome? (fun ⟨src, tgt⟩ =>
    if src = cp then some tgt else none)

/-- Replace every codepoint in a sequence with its confusables-table
    target (if one exists); codepoints absent from the table are
    preserved. Applied between two NFD passes in `skeleton`. -/
def substitute (cps : Array Nat) : Array Nat :=
  cps.foldl (fun acc cp =>
    match lookupConfusable? cp with
    | some tgt => acc ++ tgt
    | none     => acc.push cp) #[]

/-- The confusables skeleton of a codepoint sequence per UTS #39 §4. -/
def skeleton (cps : Array Nat) : Array Nat :=
  Normalization.NFC.toNFD (substitute (Normalization.NFC.toNFD cps))

/-- Two sequences are confusable iff their skeletons are equal. -/
def areConfusable (a b : Array Nat) : Bool :=
  decide (skeleton a = skeleton b)

-- ═══════════════════════════════════════════════════════════════════════════════
-- STRUCTURAL PROPERTIES
-- Reflexivity and symmetry hold by the equality semantics of `decide`;
-- neither requires induction over the Generated table.
-- ═══════════════════════════════════════════════════════════════════════════════

theorem areConfusable_refl (cps : Array Nat) :
    areConfusable cps cps = true := by
  unfold areConfusable
  exact decide_eq_true rfl

theorem areConfusable_symm (a b : Array Nat) :
    areConfusable a b = areConfusable b a := by
  unfold areConfusable
  by_cases h : skeleton a = skeleton b
  · rw [decide_eq_true h, decide_eq_true h.symm]
  · have h' : ¬ skeleton b = skeleton a := fun e => h e.symm
    rw [decide_eq_false h, decide_eq_false h']

/-- **`areConfusable` is transitive.** Follows from equality-semantics
    of `decide`: confusability reduces to skeleton equality, and
    equality is transitive. Combined with reflexivity and symmetry,
    this establishes `areConfusable` as an equivalence relation on
    codepoint arrays. -/
theorem areConfusable_trans (a b c : Array Nat)
    (hab : areConfusable a b = true) (hbc : areConfusable b c = true) :
    areConfusable a c = true := by
  unfold areConfusable at hab hbc ⊢
  have hSab : skeleton a = skeleton b := of_decide_eq_true hab
  have hSbc : skeleton b = skeleton c := of_decide_eq_true hbc
  exact decide_eq_true (hSab.trans hSbc)

-- ═══════════════════════════════════════════════════════════════════════════════
-- SKELETON IS NOT IDEMPOTENT
--
-- UTS #39 §5.1: "Skeleton is not idempotent, because the confusables
-- data is not always transitively closed."
--
-- A universal `skeleton (skeleton x) = skeleton x` would be FALSE as a
-- theorem. The non-idempotence does NOT weaken the equivalence-relation
-- structure of `areConfusable` — reflexivity, symmetry, and
-- `areConfusable_trans` above establish that regardless of whether
-- `skeleton` is a fixed-point map on its image.
--
-- For callers that need an idempotent skeleton (e.g. caching the
-- canonical representative of a confusability class), the UTS #39
-- recommendation is to iterate `skeleton` until a fixed point is
-- reached. Since the confusables data is acyclic, the iteration
-- terminates; bounding the iteration count is a separate analysis.
-- ═══════════════════════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Every string is confusable with itself. -/
theorem areConfusable_self_ascii :
    areConfusable #[0x0068, 0x0069] #[0x0068, 0x0069] = true := by native_decide

/-- COMBINING GREEK KORONIS (0x0343) and COMBINING COMMA ABOVE RIGHT
    (0x0315) are both listed in the confusables table mapping to
    COMBINING COMMA ABOVE (0x0313). Their skeletons are therefore
    equal. -/
theorem areConfusable_0343_0315 :
    areConfusable #[0x0343] #[0x0315] = true := by native_decide

/-- COMBINING TRIPLE DOT (0x1AB4) and COMBINING THREE DOTS ABOVE
    (0x20DB) both map to ARABIC SMALL HIGH THREE DOTS (0x06DB). -/
theorem areConfusable_1AB4_20DB :
    areConfusable #[0x1AB4] #[0x20DB] = true := by native_decide

/-- Two distinct ASCII letters are NOT confusable. -/
theorem areConfusable_distinct_ascii :
    areConfusable #[0x0041] #[0x0042] = false := by native_decide

/-- The skeleton of a simple ASCII identifier is the identifier
    itself, NFD-normalized (and ASCII has no non-trivial NFD). -/
theorem skeleton_ascii :
    skeleton #[0x0068, 0x0069] = #[0x0068, 0x0069] := by native_decide

/-- The skeleton maps HEBREW ACCENT DEHI (0x05AD) to HEBREW ACCENT
    TIPEHA (0x0596) per the confusables table. -/
theorem skeleton_hebrew_dehi :
    skeleton #[0x05AD] = #[0x0596] := by native_decide

end Unicode.Confusables
