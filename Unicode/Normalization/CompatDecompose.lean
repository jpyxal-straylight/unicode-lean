/-
  Unicode.Normalization.CompatDecompose

  Recursive compatibility decomposition per UAX #15 §1.3 (NFKD). For
  each codepoint, applies BOTH canonical and compatibility mappings
  recursively until a fixed point:

    * Hangul precomposed syllables decompose algorithmically to their
      L/V(/T) jamo.
    * If the codepoint has a canonical decomposition (UnicodeData
      column 5, no `<tag>` prefix), recurse on each target.
    * Else if the codepoint has a compatibility decomposition
      (UnicodeData column 5, with a `<tag>` prefix), recurse on each
      target.
    * Else the codepoint is its own decomposition.

  Parallel to `Unicode.Normalization.Decompose` but consults both
  decomposition tables. The `compatDecomposition` lookup goes
  through `Unicode.Generated.CompatDecomp`, which holds the rows whose
  source UnicodeData entry was tagged.

  Recursion is fuel-bounded for trivial termination. UAX #15 guarantees
  no decomposition cycles and bounded chain depth (in practice ≤ 4 for
  every Unicode release to date); the fuel constant leaves a wide margin.
-/

import Unicode.Normalization.Lookup
import Unicode.Normalization.Hangul
import Unicode.Generated.CompatDecomp

namespace Unicode.Normalization.CompatDecompose

open Unicode.Normalization
open Unicode.Generated

/-- Find the `CompatDecompRow` for a codepoint, if one is present in the
    pinned compat-decomp subset. Returns `none` for codepoints that have
    no compatibility decomposition (the vast majority). -/
def compatRow? (cp : Nat) : Option CompatDecomp.CompatDecompRow :=
  CompatDecomp.compatDecompRows.find? (fun r => r.codepoint = cp)

/-- Compatibility decomposition target sequence, or `#[]` when the
    codepoint has no compatibility decomposition. -/
def compatDecomposition (cp : Nat) : Array Nat :=
  match compatRow? cp with
  | some r => r.mapping
  | none   => #[]

/-- The decomposition tag (if any) of a codepoint with compatibility
    decomposition. Returns `none` for canonical or non-decomposing
    codepoints. -/
def compatTag? (cp : Nat) : Option CompatDecomp.CompatTag :=
  match compatRow? cp with
  | some r => some r.tag
  | none   => none

/-- Maximum recursion depth for compatibility decomposition. UAX #15
    bounds the longest decomposition chain at a small integer; 32
    leaves a comfortable safety margin over every published UCD. -/
def maxDepth : Nat := 32

/-- Fully decompose a single codepoint per UAX #15 NFKD, recursively
    applying canonical mappings first and compatibility mappings second,
    until a fixed point. Returns `#[cp]` when the codepoint has no
    decomposition.

    `fuel` bounds recursion depth; if exhausted the function returns the
    partial expansion, but this is unreachable under the `maxDepth`
    default on any real UCD release. -/
def fullCompatDecomposeFuel : Nat → Nat → Array Nat
  | 0,        cp => #[cp]
  | fuel + 1, cp =>
    match Hangul.decomposeSyllable? cp with
    | some jamo => jamo
    | none =>
      let canon := Lookup.canonicalDecomposition cp
      if canon.isEmpty then
        let compat := compatDecomposition cp
        if compat.isEmpty then
          #[cp]
        else
          compat.foldl
            (fun acc cp' => acc ++ fullCompatDecomposeFuel fuel cp') #[]
      else
        canon.foldl
          (fun acc cp' => acc ++ fullCompatDecomposeFuel fuel cp') #[]

/-- Fully compatibility-decompose a single codepoint. Thin wrapper that
    fixes `fuel = maxDepth`. -/
def fullCompatDecompose (cp : Nat) : Array Nat :=
  fullCompatDecomposeFuel maxDepth cp

/-- Fully compatibility-decompose a codepoint sequence. Applies
    `fullCompatDecompose` to each input codepoint and concatenates the
    results in order. -/
def compatDecomposeSequence (cps : Array Nat) : Array Nat :=
  cps.foldl (fun acc cp => acc ++ fullCompatDecompose cp) #[]

-- ═══════════════════════════════════════════════════════════════════════════════
-- TEST VECTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- `A` (no decomposition) round-trips as its own singleton. -/
theorem compat_decompose_latin_A :
    fullCompatDecompose 0x0041 = #[0x0041] := by native_decide

/-- LATIN CAPITAL LETTER A WITH GRAVE has a canonical decomposition;
    NFKD reaches it through the canonical branch. -/
theorem compat_decompose_A_grave :
    fullCompatDecompose 0x00C0 = #[0x0041, 0x0300] := by native_decide

/-- NO-BREAK SPACE U+00A0 has compatibility decomposition `<noBreak> 0020`. -/
theorem compat_decompose_nbsp :
    fullCompatDecompose 0x00A0 = #[0x0020] := by native_decide

/-- SUPERSCRIPT TWO U+00B2 has compatibility decomposition `<super> 0032`. -/
theorem compat_decompose_super_2 :
    fullCompatDecompose 0x00B2 = #[0x0032] := by native_decide

/-- DIAERESIS U+00A8 has compatibility decomposition `<compat> 0020 0308`. -/
theorem compat_decompose_diaeresis :
    fullCompatDecompose 0x00A8 = #[0x0020, 0x0308] := by native_decide

/-- MICRO SIGN U+00B5 has compatibility decomposition `<compat> 03BC`
    (Greek small letter mu); 0x03BC has no further decomposition. -/
theorem compat_decompose_micro :
    fullCompatDecompose 0x00B5 = #[0x03BC] := by native_decide

/-- HANGUL SYLLABLE GAG decomposes algorithmically to L + V + T. -/
theorem compat_decompose_GAG :
    fullCompatDecompose 0xAC01 = #[0x1100, 0x1161, 0x11A8] := by native_decide

/-- Sequence decomposition concatenates per-codepoint decompositions. -/
theorem compat_decompose_sequence_mixed :
    compatDecomposeSequence #[0x00A0, 0x00B2, 0x0041]
      = #[0x0020, 0x0032, 0x0041] := by native_decide

/-- Decomposition of an empty sequence is empty. -/
theorem compat_decompose_empty :
    compatDecomposeSequence #[] = #[] := by native_decide

end Unicode.Normalization.CompatDecompose
