/-
  Unicode.Normalization.QuickCheckHangulFacts

  Hangul / jamo CCC = 0 facts in support of `isNFCQuickCheck` soundness
  (UAX #15 §A.1).

  Three `native_decide` tables live here:

    * `vJamo_ccc_zero`         — 21 V-jamo codepoints have CCC = 0.
    * `tJamo_ccc_zero`         — 27 T-jamo codepoints have CCC = 0
                                 (indexed from `TBase + 1`; `TBase + 0`
                                 is the "no T" sentinel).
    * `hangulSyllable_ccc_zero` — every one of the 11172 precomposed
                                  Hangul syllables has CCC = 0.

  The three tables together discharge "Hangul composition never fires
  with a nonstarter trailing element" — the lemma the Fact 3 per-codepoint
  lift in `QuickCheckSoundness` depends on.

  Placed in its own module so the heavy compilation (especially the
  11172-element Hangul-syllable scan) isolates cleanly under
  `LEAN_NUM_THREADS=1`. Parallel to `QuickCheckFacts`'s split.
-/

import Unicode.Normalization.Hangul
import Unicode.Normalization.Lookup

namespace Unicode.Normalization.QuickCheckHangulFacts

open Unicode.Normalization

/-- Every V-jamo (vowel jamo, range `0x1161..0x1175`) has CCC = 0.
    Narrow `native_decide` over 21 codepoints. -/
theorem vJamo_ccc_zero :
    (List.range Hangul.VCount).all
      (fun i => Lookup.canonicalCombiningClass (Hangul.VBase + i) = 0) = true := by
  native_decide

/-- Every T-jamo (trailing jamo, range `0x11A8..0x11C2`) has CCC = 0.
    Narrow `native_decide` over 27 codepoints. Indexes from `TBase + 1`
    because `TBase + 0` is the "no T" sentinel in `decomposeSyllable?`. -/
theorem tJamo_ccc_zero :
    (List.range (Hangul.TCount - 1)).all
      (fun i => Lookup.canonicalCombiningClass (Hangul.TBase + 1 + i) = 0) = true := by
  native_decide

/-- Every precomposed Hangul syllable (range `0xAC00..0xD7A3`) has
    CCC = 0. Table-scale `native_decide` over 11172 codepoints. -/
theorem hangulSyllable_ccc_zero :
    (List.range Hangul.SCount).all
      (fun i => Lookup.canonicalCombiningClass (Hangul.SBase + i) = 0) = true := by
  native_decide

end Unicode.Normalization.QuickCheckHangulFacts
