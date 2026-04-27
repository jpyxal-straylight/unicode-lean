/-
  Unicode.Normalization.Hangul

  Algorithmic Hangul syllable decomposition and composition per UAX #15
  §4.2. The 11172 precomposed Hangul syllables in `0xAC00 .. 0xD7A3`
  decompose to sequences of jamo (leading consonant L, vowel V, and
  optional trailing consonant T) by arithmetic on codepoint offsets,
  rather than via the UnicodeData table. Keeping this logic isolated
  keeps the general-purpose decomposition path in `Decompose.lean`
  small.
-/

namespace Unicode.Normalization.Hangul

/-- Base codepoint of precomposed Hangul syllables (HANGUL SYLLABLE GA). -/
def SBase : Nat := 0xAC00

/-- Base codepoint of leading consonants (L jamo; HANGUL CHOSEONG KIYEOK). -/
def LBase : Nat := 0x1100

/-- Base codepoint of vowels (V jamo; HANGUL JUNGSEONG A). -/
def VBase : Nat := 0x1161

/-- Base codepoint of trailing consonants (T jamo), offset by one so
    that `TBase + 0` is the "no trailing consonant" sentinel rather
    than an actual jamo. Real trailing jamo start at `TBase + 1`
    (HANGUL JONGSEONG KIYEOK). -/
def TBase : Nat := 0x11A7

def LCount : Nat := 19
def VCount : Nat := 21
def TCount : Nat := 28
def NCount : Nat := VCount * TCount         -- 588
def SCount : Nat := LCount * NCount         -- 11172

/-- True iff `cp` is a precomposed Hangul syllable in `0xAC00..0xD7A3`. -/
def isHangulSyllable (cp : Nat) : Bool :=
  decide (SBase ≤ cp ∧ cp < SBase + SCount)

/-- True iff `cp` is a leading jamo in `0x1100..0x1112`. -/
def isLJamo (cp : Nat) : Bool :=
  decide (LBase ≤ cp ∧ cp < LBase + LCount)

/-- True iff `cp` is a vowel jamo in `0x1161..0x1175`. -/
def isVJamo (cp : Nat) : Bool :=
  decide (VBase ≤ cp ∧ cp < VBase + VCount)

/-- True iff `cp` is a trailing jamo in `0x11A8..0x11C2` — the 27
    non-filler Jongseong codepoints that can appear as the T slot of
    a canonical LVT syllable decomposition. The `TBase` offset places
    cp=`TBase` (0x11A7) outside this range intentionally; real
    trailing jamo begin one above `TBase`. The upper bound is strict
    (`cp < TBase + TCount` rather than `≤`) because `decomposeSyllable?`
    computes `tIndex := sIndex % TCount` ∈ [0, 27), so the T slot it
    emits is in `[TBase+1, TBase+27] = [0x11A8, 0x11C2]`. Accepting
    `cp = 0x11C3 = TBase + TCount` would break the composePair? /
    decomposeSyllable? round-trip at exactly that edge — see
    sidecars/.tmp/hangul-anomaly-check.lean for the concrete witness. -/
def isTJamo (cp : Nat) : Bool :=
  decide (TBase < cp ∧ cp < TBase + TCount)

/-- Canonical decomposition of a Hangul syllable. Produces a two-element
    sequence `#[L, V]` when the syllable has no trailing consonant and
    a three-element sequence `#[L, V, T]` otherwise. Returns `none` when
    `cp` is not a precomposed Hangul syllable. -/
def decomposeSyllable? (cp : Nat) : Option (Array Nat) :=
  if isHangulSyllable cp then
    let sIndex := cp - SBase
    let l      := LBase + sIndex / NCount
    let v      := VBase + (sIndex % NCount) / TCount
    let tIndex := sIndex % TCount
    if tIndex = 0 then
      some #[l, v]
    else
      some #[l, v, TBase + tIndex]
  else
    none

/-- Canonical composition of a Hangul jamo sequence. Attempts to pair
    `(l, v)` into an `LV` syllable, or `(lv, t)` where `lv` is itself
    a Hangul syllable into an `LVT` syllable. Returns `none` when the
    pair is not composable.

    Per UAX #15 §4.2 this is the ONLY codepoint pair combination
    allowed for Hangul composition — individual jamo do not compose
    via the `UnicodeData` primary-composite table. -/
def composePair? (first second : Nat) : Option Nat :=
  if isLJamo first ∧ isVJamo second then
    let lIndex := first - LBase
    let vIndex := second - VBase
    some (SBase + (lIndex * VCount + vIndex) * TCount)
  else if isHangulSyllable first ∧ isTJamo second then
    let sIndex := first - SBase
    if sIndex % TCount = 0 then
      some (first + (second - TBase))
    else
      none
  else
    none

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- HANGUL SYLLABLE GA (U+AC00) is `L + V` with no trailing consonant:
    LBase + VBase. -/
theorem decompose_GA :
    decomposeSyllable? 0xAC00 = some #[0x1100, 0x1161] := by native_decide

/-- HANGUL SYLLABLE GAG (U+AC01) is `L + V + T`: KIYEOK + A + KIYEOK. -/
theorem decompose_GAG :
    decomposeSyllable? 0xAC01 = some #[0x1100, 0x1161, 0x11A8] := by native_decide

/-- HANGUL SYLLABLE HIH (U+D7A3 = last syllable) is `L + V + T`. -/
theorem decompose_last :
    decomposeSyllable? 0xD7A3 = some #[0x1112, 0x1175, 0x11C2] := by native_decide

/-- Non-syllable codepoints return `none`. -/
theorem decompose_latin_A : decomposeSyllable? 0x0041 = none := by native_decide

/-- Composing KIYEOK + A recovers HANGUL SYLLABLE GA. -/
theorem compose_GA : composePair? 0x1100 0x1161 = some 0xAC00 := by native_decide

/-- Composing HANGUL SYLLABLE GA + KIYEOK recovers HANGUL SYLLABLE GAG. -/
theorem compose_GAG : composePair? 0xAC00 0x11A8 = some 0xAC01 := by native_decide

/-- Non-Hangul pairs do not compose. -/
theorem compose_latin_pair : composePair? 0x0041 0x0300 = none := by native_decide

/-- `isHangulSyllable` boundary sanity. -/
theorem range_low  : isHangulSyllable 0xAC00 = true  := by native_decide
theorem range_high : isHangulSyllable 0xD7A3 = true  := by native_decide
theorem range_out  : isHangulSyllable 0xD7A4 = false := by native_decide

end Unicode.Normalization.Hangul
