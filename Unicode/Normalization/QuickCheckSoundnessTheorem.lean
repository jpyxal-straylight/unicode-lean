/-
  Unicode.Normalization.QuickCheckSoundnessTheorem

  The master soundness theorem for `isNFCQuickCheck` (UAX #15 §A.1):

      ∀ cps, isNFCQuickCheck cps = true → toNFC cps = cps.

  Architecture: structural snoc induction. The base case
  (`empty_sound`) and the prefix-preservation step
  (`isNFCQuickCheck_dropLast`) sit in their respective companion
  modules; the inductive step is closed by
  `QuickCheckSoundnessSnocClosure.nfc_snoc_qcY`, a two-shape
  dispatcher (starter / non-starter) over `cp`'s CCC class:

    * Starter (CCC = 0): consolidated via
      `ComposeBlockAdditive.compose_qcY_starter_block_additive` and
      `singleton_sound`. Covers atomic, Hangul, size-2-starter, and
      recursively-chained-size-2-starter shapes uniformly.
    * Non-starter (CCC > 0): closed by
      `QuickCheckSoundnessSnocClosure.nfc_snoc_qcY_nonstarter_structural`
      via `ComposeNonstarterSlide.compose_slide_qcY`,
      `ComposeBufferStructure.compose_buffer_ccc_bound`, and
      `ComposeBufferStructure.chain_fires_via_buffer_bound`.
-/

import Unicode.Normalization.NFC
import Unicode.Normalization.Reorder
import Unicode.Normalization.QuickCheckSoundness
import Unicode.Normalization.QuickCheckSoundnessSnoc
import Unicode.Normalization.QuickCheckSoundnessMaster
import Unicode.Normalization.QuickCheckSoundnessSnocClosure

namespace Unicode.Normalization.QuickCheckSoundnessTheorem

open Unicode.Normalization
open Unicode.Normalization.NFC
  (toNFC isNFCQuickCheck nfcQCValue)

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1 PER-CODEPOINT QC EXTRACTOR
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Every codepoint of an `isNFCQuickCheck`-passing sequence has
    `nfcQCValue = .Y`. Direct projection of the per-element conjunct
    of `isNFCQuickCheck`. -/
theorem qcY_of_mem
    {cps : Array Nat} (h : isNFCQuickCheck cps = true)
    {cp : Nat} (hMem : cp ∈ cps) :
    nfcQCValue cp = .Y :=
  QuickCheckSoundnessMaster.qcY_of_mem cps h cp hMem

-- ═══════════════════════════════════════════════════════════════════════════════
-- §2 SINGLETON SOUNDNESS LIFT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Singleton soundness for any QC=Y codepoint. -/
theorem singleton_sound
    (cp : Nat) (hQC : nfcQCValue cp = .Y) :
    toNFC #[cp] = #[cp] :=
  QuickCheckSoundnessMaster.singleton_sound cp hQC

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3 MEMBERSHIP HELPERS FOR SNOC INDUCTION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The trailing element of `xs ++ #[cp]` is a member. -/
theorem mem_snoc_self (xs : Array Nat) (cp : Nat) :
    cp ∈ xs ++ #[cp] := by
  apply Array.mem_append.mpr
  right
  simp

/-- Membership in the prefix lifts to membership in the snoc-extended
    array. -/
theorem mem_snoc_of_mem_prefix
    {xs : Array Nat} {cp : Nat} (x : Nat) (hMem : x ∈ xs) :
    x ∈ xs ++ #[cp] := by
  apply Array.mem_append.mpr
  left
  exact hMem

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4 MASTER SOUNDNESS THEOREM (UNCONDITIONAL)
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Master soundness theorem.** Every `isNFCQuickCheck`-passing
    sequence is in NFC form. Closed unconditionally: the snoc-induction
    base bottoms out via `empty_sound`; the inductive step delegates
    to `QuickCheckSoundnessSnocClosure.nfc_snoc_qcY`, the two-shape
    dispatcher built atop `compose_qcY_starter_block_additive` (starter)
    and `nfc_snoc_atomic_nonstarter` (non-starter). -/
theorem quickCheck_sound
    (cps : Array Nat) (hQC : isNFCQuickCheck cps = true) :
    toNFC cps = cps := by
  suffices hList : ∀ (l : List Nat),
      isNFCQuickCheck l.toArray = true → toNFC l.toArray = l.toArray by
    have hRes := hList cps.toList
    have hToArr : cps.toList.toArray = cps := cps.toArray_toList
    rw [hToArr] at hRes
    exact hRes hQC
  intro l
  refine Reorder.list_snoc_induction
    (motive := fun l =>
      isNFCQuickCheck l.toArray = true → toNFC l.toArray = l.toArray)
    ?baseCase ?stepCase l
  · intro hQCNil
    clear hQCNil
    exact QuickCheckSoundness.empty_sound
  · intro xs cp ih hSnocQC
    have hAppend : (xs ++ [cp]).toArray = xs.toArray ++ #[cp] :=
      (List.append_toArray xs [cp]).symm
    rw [hAppend] at hSnocQC ⊢
    have hPrefixQC : isNFCQuickCheck xs.toArray = true :=
      QuickCheckSoundnessSnoc.isNFCQuickCheck_dropLast
        xs.toArray cp hSnocQC
    have hPrefixNFC : toNFC xs.toArray = xs.toArray := ih hPrefixQC
    have hCpQC : nfcQCValue cp = .Y :=
      qcY_of_mem hSnocQC (mem_snoc_self xs.toArray cp)
    exact QuickCheckSoundnessSnocClosure.nfc_snoc_qcY
      xs.toArray cp hCpQC hPrefixNFC hSnocQC

end Unicode.Normalization.QuickCheckSoundnessTheorem
