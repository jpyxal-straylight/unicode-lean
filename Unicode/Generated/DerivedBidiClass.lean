/-
  Unicode.Generated.DerivedBidiClass

  Bidi_Class ranges from `lemma/lean/Unicode/Ucd/DerivedBidiClass.txt`
  (UCD 17.0.0), embedded as a String constant via `include_str` and
  parsed once at module load. Pattern follows
  `fgdorais/lean4-unicode-basic`.

  Semantics: resolve a codepoint's Bidi_Class by first searching
  `explicitRanges`; if no range covers it, take the LAST entry in
  `defaultRanges` whose range covers it. `defaultRanges` is the
  transliteration of the file's `@missing` header declarations, in
  source order.

  The data section uses the short Bidi_Class names (`L`, `R`, `AL`, …);
  the `@missing` directives use the long names (`Left_To_Right`,
  `Right_To_Left`, `Arabic_Letter`, …). The parser recognises both.
-/

namespace Unicode.Generated.DerivedBidiClass

/-- The 23 Bidi_Class values defined by UAX #9. Short names per Table 4. -/
inductive BidiClass where
  | L | R | AL | EN | ES | ET | AN | CS | NSM | BN
  | B | S | WS | ON | LRE | LRO | RLE | RLO | PDF
  | LRI | RLI | FSI | PDI
  deriving DecidableEq, Repr, Inhabited

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

def parseRange (s : String) : Nat × Nat :=
  match String.splitOn s ".." with
  | [single]  => let n := parseHex single; (n, n)
  | [a, b]    => (parseHex a, parseHex b)
  | irregularRange => Function.const (List String) (0, 0) irregularRange

/-- Parse a Bidi_Class name. Accepts either the short form (`L`, `R`,
    `AL`, …) used in the data section or the long form
    (`Left_To_Right`, `Right_To_Left`, `Arabic_Letter`, …) used in
    `@missing:` directives. -/
def parseBidiClass? : String → Option BidiClass
  | "L"   | "Left_To_Right"            => some .L
  | "R"   | "Right_To_Left"            => some .R
  | "AL"  | "Arabic_Letter"            => some .AL
  | "EN"  | "European_Number"          => some .EN
  | "ES"  | "European_Separator"       => some .ES
  | "ET"  | "European_Terminator"      => some .ET
  | "AN"  | "Arabic_Number"            => some .AN
  | "CS"  | "Common_Separator"         => some .CS
  | "NSM" | "Nonspacing_Mark"          => some .NSM
  | "BN"  | "Boundary_Neutral"         => some .BN
  | "B"   | "Paragraph_Separator"      => some .B
  | "S"   | "Segment_Separator"        => some .S
  | "WS"  | "White_Space"              => some .WS
  | "ON"  | "Other_Neutral"            => some .ON
  | "LRE" | "Left_To_Right_Embedding"  => some .LRE
  | "LRO" | "Left_To_Right_Override"   => some .LRO
  | "RLE" | "Right_To_Left_Embedding"  => some .RLE
  | "RLO" | "Right_To_Left_Override"   => some .RLO
  | "PDF" | "Pop_Directional_Format"   => some .PDF
  | "LRI" | "Left_To_Right_Isolate"    => some .LRI
  | "RLI" | "Right_To_Left_Isolate"    => some .RLI
  | "FSI" | "First_Strong_Isolate"     => some .FSI
  | "PDI" | "Pop_Directional_Isolate"  => some .PDI
  | unknownBidiClassName => Function.const String none unknownBidiClassName

/-- Parse one DerivedBidiClass.txt explicit row. -/
def parseExplicitRow (rawLine : String) : Option (Nat × Nat × BidiClass) :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | [rngField, classField] =>
    let (lo, hi) := parseRange (trimS rngField)
    match parseBidiClass? (trimS classField) with
    | some cls => some (lo, hi, cls)
    | none     => none
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Parse one `@missing:` directive. -/
def parseMissingRow (rawLine : String) : Option (Nat × Nat × BidiClass) :=
  let line := trimS rawLine
  if !line.startsWith "# @missing:" then none else
  let body := trimS (line.drop "# @missing:".length).toString
  match String.splitOn body ";" with
  | [rngField, classField] =>
    let (lo, hi) := parseRange (trimS rngField)
    match parseBidiClass? (trimS classField) with
    | some cls => some (lo, hi, cls)
    | none     => none
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `DerivedBidiClass.txt`, embedded at compile time. -/
def derivedBidiClassRaw : String := include_str "../Ucd/DerivedBidiClass.txt"

/-! Per-range Bidi_Class assignments from the data section. -/
def explicitRanges : Array (Nat × Nat × BidiClass) :=
  ((derivedBidiClassRaw.splitOn "\n").filterMap parseExplicitRow).toArray

/-! `@missing` directives from the source header, in source order. The
    LAST entry whose range contains a codepoint wins (UAX #9 default
    rule). -/
def defaultRanges : Array (Nat × Nat × BidiClass) :=
  ((derivedBidiClassRaw.splitOn "\n").filterMap parseMissingRow).toArray

end Unicode.Generated.DerivedBidiClass
