/-
  Unicode.Generated.Confusables

  Confusable-skeleton mappings from `lemma/lean/Unicode/Ucd/confusables.txt`
  (UTS #39 16.0.0), embedded as a String constant via `include_str`
  and parsed once at module load. Pattern follows
  `fgdorais/lean4-unicode-basic`.

  Semantics (UTS #39 §4): each entry `(source, skeleton)` maps a single
  source codepoint to its confusable-skeleton sequence of one or more
  target codepoints. The skeleton of a string is computed by NFD-
  normalizing, replacing each codepoint by its skeleton-sequence image
  (if present) or by itself (if absent), then NFD-normalizing again.
  Two strings are confusable iff their skeletons are equal.

  Source format per row:
    `<source-hex> ; <target-hex>(' ' <target-hex>)* ; <type> # comment`

  Counts: 6355 mappings.
-/

namespace Unicode.Generated.Confusables

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

/-- Parse one row of confusables.txt. Returns `none` for blank or
    comment lines. The third field (type, e.g. `MA`) is dropped;
    only the source/skeleton pair is kept. -/
def parseConfusableRow (rawLine : String) : Option (Nat × Array Nat) :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | srcField :: tgtField :: trailingFields =>
    let src := parseHex (trimS srcField)
    let tgt := parseCodepoints (trimS tgtField)
    Function.const (List String)
      (if tgt.isEmpty then none else some (src, tgt))
      trailingFields
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `confusables.txt`, embedded at compile time. -/
def confusablesRaw : String := include_str "../Ucd/confusables.txt"

/-! Confusable-skeleton mappings. Each entry `(source, skeleton)` has
    `source : Nat` as a single codepoint and `skeleton : Array Nat` as
    the sequence of one or more target codepoints. -/
def mappings : Array (Nat × Array Nat) :=
  ((confusablesRaw.splitOn "\n").filterMap parseConfusableRow).toArray

end Unicode.Generated.Confusables
