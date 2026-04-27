/-
  Unicode.Generated.EastAsianWidth

  East_Asian_Width ranges from `lemma/lean/Unicode/Ucd/EastAsianWidth.txt`
  (UCD 17.0.0), embedded as a String constant via `include_str` and
  parsed once at module load. Pattern follows
  `fgdorais/lean4-unicode-basic`.

  Semantics (UAX #11): each explicit range assigns an East_Asian_Width
  property value to a closed codepoint interval. Codepoints not covered
  by `explicitRanges` fall back to the LAST `defaultRanges` entry whose
  range contains them, matching the `@missing` header in the source
  file.
-/

namespace Unicode.Generated.EastAsianWidth

/-- The six East_Asian_Width property values per UAX #11. -/
inductive EastAsianWidthClass where
  | A
  | F
  | H
  | N
  | Na
  | W
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

def parseEAW? : String → Option EastAsianWidthClass
  | "A"  => some .A
  | "F"  => some .F
  | "H"  => some .H
  | "N"  => some .N
  | "Na" => some .Na
  | "W"  => some .W
  | unknownEawClass => Function.const String none unknownEawClass

/-- Parse one EastAsianWidth.txt explicit row. Returns `none` for
    blank/comment lines or unrecognised width classes. -/
def parseExplicitRow
    (rawLine : String) : Option (Nat × Nat × EastAsianWidthClass) :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | [rngField, classField] =>
    let (lo, hi) := parseRange (trimS rngField)
    match parseEAW? (trimS classField) with
    | some cls => some (lo, hi, cls)
    | none     => none
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Parse one `@missing:` directive from a comment line. Format:
    `# @missing: <range>; <class>`. -/
def parseMissingRow
    (rawLine : String) : Option (Nat × Nat × EastAsianWidthClass) :=
  let line := trimS rawLine
  -- Expect lines like `# @missing: 0000..10FFFF; N`
  if !line.startsWith "# @missing:" then none else
  let body := trimS (line.drop "# @missing:".length).toString
  match String.splitOn body ";" with
  | [rngField, classField] =>
    let (lo, hi) := parseRange (trimS rngField)
    match parseEAW? (trimS classField) with
    | some cls => some (lo, hi, cls)
    | none     => none
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `EastAsianWidth.txt`, embedded at compile time. -/
def eastAsianWidthRaw : String := include_str "../Ucd/EastAsianWidth.txt"

/-! Per-range East_Asian_Width property assignments. -/
def explicitRanges : Array (Nat × Nat × EastAsianWidthClass) :=
  ((eastAsianWidthRaw.splitOn "\n").filterMap parseExplicitRow).toArray

/-! Default ranges from `@missing:` directives in the source header,
    in source order. The LAST entry whose range contains a codepoint
    wins. -/
def defaultRanges : Array (Nat × Nat × EastAsianWidthClass) :=
  ((eastAsianWidthRaw.splitOn "\n").filterMap parseMissingRow).toArray

end Unicode.Generated.EastAsianWidth
