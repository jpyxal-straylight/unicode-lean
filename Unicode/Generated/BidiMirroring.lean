/-
  Unicode.Generated.BidiMirroring

  Bidi mirroring pairs from `lemma/lean/Unicode/Ucd/BidiMirroring.txt`
  (UCD 17.0.0), embedded as a String constant via `include_str` and
  parsed once at module load. Pattern follows
  `fgdorais/lean4-unicode-basic`.

  Semantics (UAX #9 §7.2, UAX #44 §5.7.5): the `Bidi_Mirroring_Glyph`
  property maps a Bidi_Mirrored=Yes codepoint to another codepoint
  whose glyph is its mirror image. Used by UAX #9 rule L4 to select
  the visual glyph in right-to-left context.

  Source format per row: `<source-hex>; <mirror-hex>`.
-/

namespace Unicode.Generated.BidiMirroring

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

/-- Parse one BidiMirroring.txt row. Returns `none` for blank/comment
    lines. -/
def parseMirrorRow (rawLine : String) : Option (Nat × Nat) :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | [srcField, mirField] => some (parseHex (trimS srcField), parseHex (trimS mirField))
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `BidiMirroring.txt`, embedded at compile time. -/
def bidiMirroringRaw : String := include_str "../Ucd/BidiMirroring.txt"

/-- Pairs `(codepoint, mirror)` from BidiMirroring.txt. -/
def bidiMirrorPairs : Array (Nat × Nat) :=
  ((bidiMirroringRaw.splitOn "\n").filterMap parseMirrorRow).toArray

end Unicode.Generated.BidiMirroring
