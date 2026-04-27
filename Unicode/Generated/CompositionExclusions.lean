/-
  Unicode.Generated.CompositionExclusions

  Codepoints excluded from canonical composition (UCD 17.0.0),
  embedded as a String constant via `include_str` and parsed once at
  module load. Pattern follows `fgdorais/lean4-unicode-basic`.

  Semantics: the codepoints below are excluded from canonical composition
  during NFC/NFKC normalization (UAX #15 §1.2). They decompose to one or
  more codepoints canonically but do NOT recompose when the decomposed
  sequence is re-normalized.

  Source format per row: `<hex-codepoint>` (single column, comments
  stripped).
-/

namespace Unicode.Generated.CompositionExclusions

@[inline]
def trimS (s : String) : String := (String.trimAscii s).toString

def hexDigitVal (c : Char) : Nat :=
  let n := c.toNat
  if n ≥ 0x30 ∧ n ≤ 0x39 then n - 0x30
  else if n ≥ 0x61 ∧ n ≤ 0x66 then n - 0x61 + 10
  else if n ≥ 0x41 ∧ n ≤ 0x46 then n - 0x41 + 10
  else 0

def parseHex (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexDigitVal c) 0

/-- Parse one CompositionExclusions.txt row. Returns `none` for blank
    or comment-only lines. -/
def parseExclusionRow (rawLine : String) : Option Nat :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else some (parseHex line)

/-- Raw text of `CompositionExclusions.txt`, embedded at compile time. -/
def compositionExclusionsRaw : String :=
  include_str "../Ucd/CompositionExclusions.txt"

/-- Sorted array of codepoints excluded from canonical composition. -/
def codepoints : Array Nat :=
  ((compositionExclusionsRaw.splitOn "\n").filterMap parseExclusionRow).toArray

end Unicode.Generated.CompositionExclusions
