/-
  Unicode.Generated.BidiBrackets

  Bidi paired-bracket entries from `lemma/lean/Unicode/Ucd/BidiBrackets.txt`
  (UCD 17.0.0), embedded as a String constant via `include_str` and
  parsed once at module load. Pattern follows
  `fgdorais/lean4-unicode-basic`.

  Semantics (UAX #9 §3.1.3, UAX #44 §5.7.4): every paired-bracket
  codepoint carries two normative properties:

    * `Bidi_Paired_Bracket`        — the matching paired-bracket
                                     codepoint (e.g. `(` ↔ `)`).
    * `Bidi_Paired_Bracket_Type`   — `Open` (column `o` in source),
                                     `Close` (column `c`), or `None`
                                     (no entry).

  Used by UAX #9 rule N0 (paired-bracket pair processing).

  Counts: 128 paired-bracket entries (64 pairs counted twice — one
  Open + one Close row each).
-/

namespace Unicode.Generated.BidiBrackets

inductive BidiBracketType where
  | Open
  | Close
  deriving DecidableEq, Repr, Inhabited

/-- One paired-bracket entry. `pair` is the matching bracket; `bracketType`
    classifies this codepoint as Open or Close. -/
structure BidiBracketRow where
  codepoint   : Nat
  pair        : Nat
  bracketType : BidiBracketType
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

def parseBracketType? : String → Option BidiBracketType
  | "o" => some .Open
  | "c" => some .Close
  | unknownBracketKind => Function.const String none unknownBracketKind

/-- Parse one BidiBrackets.txt row. Returns `none` for blank/comment
    lines or rows without a recognised bracket-type column. -/
def parseBracketRow (rawLine : String) : Option BidiBracketRow :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | [cpField, pairField, typeField] =>
    match parseBracketType? (trimS typeField) with
    | none      => none
    | some btyp => some ⟨parseHex (trimS cpField), parseHex (trimS pairField), btyp⟩
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `BidiBrackets.txt`, embedded at compile time. -/
def bidiBracketsRaw : String := include_str "../Ucd/BidiBrackets.txt"

def bidiBracketRows : Array BidiBracketRow :=
  ((bidiBracketsRaw.splitOn "\n").filterMap parseBracketRow).toArray

end Unicode.Generated.BidiBrackets
