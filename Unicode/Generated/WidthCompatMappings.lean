/-
  Unicode.Generated.WidthCompatMappings

  Width-compatibility decomposition mappings extracted from
  `lemma/lean/Unicode/Ucd/UnicodeData.txt` (UCD 17.0.0) at module load.
  Pattern follows `fgdorais/lean4-unicode-basic`.

  Semantics (RFC 8265 §5.2.3 Width Mapping): each entry `(source,
  target)` maps a fullwidth or halfwidth codepoint to its canonical
  width-equivalent sequence. PRECIS Preparation applies this mapping
  before case folding and NFC.

  Source: rows of UnicodeData.txt where column 5 begins with `<wide>`
  or `<narrow>`.
-/

namespace Unicode.Generated.WidthCompatMappings

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

/-- Parse one UnicodeData.txt row, returning a width-compatibility
    `(source, target)` mapping only when column 5 begins with `<wide>`
    or `<narrow>`. -/
def parseWidthRow (rawLine : String) : Option (Nat × Array Nat) := Id.run do
  let line := trimS rawLine
  if line.isEmpty then return none
  let fields := String.splitOn line ";"
  if fields.length < 6 then return none
  let cp := parseHex (trimS fields[0]!)
  let decompStr := trimS fields[5]!
  if !(decompStr.startsWith "<wide>" || decompStr.startsWith "<narrow>") then
    return none
  let toks := (decompStr.splitOn " ").filterMap (fun t =>
    let t := trimS t
    if t.isEmpty then none else some t)
  match toks with
  | tag :: cpToks =>
    let mapping := (cpToks.map parseHex).toArray
    if mapping.isEmpty then none else some (cp,
      Function.const String mapping tag)
  | irregularToks => Function.const (List String) none irregularToks

/-- Raw text of `UnicodeData.txt`, embedded at compile time. -/
def unicodeDataRaw : String := include_str "../Ucd/UnicodeData.txt"

/-- Width-compatibility mappings: each `(source, target)` pair from
    `<wide>`/`<narrow>` rows of UnicodeData.txt. -/
def widthCompatMappings : Array (Nat × Array Nat) :=
  ((unicodeDataRaw.splitOn "\n").filterMap parseWidthRow).toArray

end Unicode.Generated.WidthCompatMappings
