/-
  Unicode.Generated.CaseFolding

  Case-folding mappings from `lemma/lean/Unicode/Ucd/CaseFolding.txt`
  (UCD 17.0.0), embedded as a String constant via `include_str` and
  parsed once at module load. Pattern follows
  `fgdorais/lean4-unicode-basic`.

  Semantics (UCD §5.18): each entry `(source, target)` maps a single
  source codepoint to its default-case-folded target sequence. Only
  entries whose source-file status is `C` (common) or `F` (full) are
  kept. Status `S` (simple) entries are redundant with `C`/`F` and
  `T` entries are Turkic-locale-specific — both are dropped to match
  the default (non-locale) case-folding path specified by RFC 8265
  §5.2.4.

  Codepoints not listed fold to themselves: apply the identity when a
  lookup in `foldings` misses.
-/

namespace Unicode.Generated.CaseFolding

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

/-- Parse a space-separated list of hex codepoints. -/
def parseCodepoints (s : String) : Array Nat :=
  ((s.splitOn " ").filterMap (fun tok =>
    let t := trimS tok
    if t.isEmpty then none else some (parseHex t))).toArray

/-- Parse one CaseFolding.txt row. Returns `none` for blank/comment
    lines or rows whose status is not `C` or `F`. -/
def parseFoldingRow (rawLine : String) : Option (Nat × Array Nat) :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | cpField :: statusField :: targetField :: trailingFields =>
    let status := trimS statusField
    if status = "C" ∨ status = "F" then
      let cp := parseHex (trimS cpField)
      let target := parseCodepoints (trimS targetField)
      Function.const (List String)
        (if target.isEmpty then none else some (cp, target))
        trailingFields
    else
      Function.const (List String) none trailingFields
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `CaseFolding.txt`, embedded at compile time. -/
def caseFoldingRaw : String := include_str "../Ucd/CaseFolding.txt"

/-- Case-folding mappings for UCD status C and F. Each `(source,
    target)` has `source : Nat` as a single codepoint and `target :
    Array Nat` as the sequence of one or more fold-target
    codepoints. -/
def foldings : Array (Nat × Array Nat) :=
  ((caseFoldingRaw.splitOn "\n").filterMap parseFoldingRow).toArray

end Unicode.Generated.CaseFolding
