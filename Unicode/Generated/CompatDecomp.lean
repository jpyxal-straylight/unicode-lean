/-
  Unicode.Generated.CompatDecomp

  Compatibility-decomposition rows extracted from `UnicodeData.txt`
  (UCD 17.0.0) at module load. Pattern follows
  `fgdorais/lean4-unicode-basic`.

  Semantics (UAX #44 §5.7.3, UAX #15 §1.2): UnicodeData column 5 carries
  the codepoint's Decomposition_Mapping. When the field begins with a
  bracketed `<tag>`, the decomposition is *compatibility* (not canonical)
  and the tag specifies the formatting context that distinguishes the
  source from its decomposition target. Compatibility decompositions
  apply only under NFKD / NFKC normalization; canonical decompositions
  (the `<tag>`-less rows) live in `Unicode.Generated.UnicodeData`.

  This module pins ONLY the compatibility decompositions.

  Counts: 3833 compat-decomp rows, 16 distinct tags.
-/

namespace Unicode.Generated.CompatDecomp

inductive CompatTag where
  | Circle
  | Compat
  | Final
  | Font
  | Fraction
  | Initial
  | Isolated
  | Medial
  | Narrow
  | NoBreak
  | Small
  | Square
  | Sub
  | Super
  | Vertical
  | Wide
  deriving DecidableEq, Repr, Inhabited

/-- One compatibility-decomposition row from UnicodeData.txt column 5. -/
structure CompatDecompRow where
  codepoint : Nat
  tag       : CompatTag
  mapping   : Array Nat
  deriving Repr, Inhabited

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

/-- Map a `<tag>` token (with the angle brackets, as it appears in
    UnicodeData.txt column 5) to its `CompatTag` constructor. Returns
    `none` for unrecognised tags or non-tag fields. -/
def parseCompatTag? : String → Option CompatTag
  | "<circle>"   => some .Circle
  | "<compat>"   => some .Compat
  | "<final>"    => some .Final
  | "<font>"     => some .Font
  | "<fraction>" => some .Fraction
  | "<initial>"  => some .Initial
  | "<isolated>" => some .Isolated
  | "<medial>"   => some .Medial
  | "<narrow>"   => some .Narrow
  | "<noBreak>"  => some .NoBreak
  | "<small>"    => some .Small
  | "<square>"   => some .Square
  | "<sub>"      => some .Sub
  | "<super>"    => some .Super
  | "<vertical>" => some .Vertical
  | "<wide>"     => some .Wide
  | unknownCompatTag => Function.const String none unknownCompatTag

/-- Parse one UnicodeData.txt row, returning a `CompatDecompRow` only
    when the row carries a compatibility decomposition (column 5
    begins with `<tag>`). All other rows return `none` and are
    dropped. -/
def parseCompatRow (rawLine : String) : Option CompatDecompRow := Id.run do
  let line := trimS rawLine
  if line.isEmpty then return none
  let fields := String.splitOn line ";"
  if fields.length < 6 then return none
  let cp := parseHex (trimS fields[0]!)
  let decompStr := trimS fields[5]!
  if decompStr.isEmpty then return none
  if !decompStr.startsWith "<" then return none  -- canonical, not compat
  let toks := (decompStr.splitOn " ").filterMap (fun t =>
    let t := trimS t
    if t.isEmpty then none else some t)
  match toks with
  | [] => none
  | tagTok :: cpToks =>
    match parseCompatTag? tagTok with
    | none => none
    | some tag =>
      let mapping := (cpToks.map parseHex).toArray
      some ⟨cp, tag, mapping⟩

/-- Raw text of `UnicodeData.txt`, embedded at compile time. Same
    source file as `Unicode.Generated.UnicodeData`; each module parses
    independently to extract its own NFC-relevant fields. -/
def unicodeDataRaw : String := include_str "../Ucd/UnicodeData.txt"

/-- All compatibility-decomposition rows from UnicodeData.txt. -/
def compatDecompRows : Array CompatDecompRow :=
  ((unicodeDataRaw.splitOn "\n").filterMap parseCompatRow).toArray

end Unicode.Generated.CompatDecomp
