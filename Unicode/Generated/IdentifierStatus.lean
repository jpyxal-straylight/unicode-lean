/-
  Unicode.Generated.IdentifierStatus

  Identifier_Status ranges from `lemma/lean/Unicode/Ucd/IdentifierStatus.txt`
  (UTS #39 16.0.0), embedded as a String constant via `include_str`
  and parsed once at module load. Pattern follows
  `fgdorais/lean4-unicode-basic`.

  Semantics: the (min, max) ranges below enumerate the positive set of
  codepoints carrying `Identifier_Status = Allowed` per UTS #39. Every
  codepoint not covered falls back to `defaultStatus` (`Restricted`),
  matching the `@missing: 0000..10FFFF; Restricted` declaration in the
  source file header.
-/

namespace Unicode.Generated.IdentifierStatus

/-- The two possible `Identifier_Status` values per UTS #39. -/
inductive IdentifierStatus where
  | Allowed
  | Restricted
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

/-- Parse one IdentifierStatus.txt row. Source file lists only
    `Allowed` ranges (the `@missing` default is `Restricted`); rows
    not labelled `Allowed` are dropped. -/
def parseIdentifierStatusRow (rawLine : String) : Option (Nat × Nat) :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | [rngField, statusField] =>
    if trimS statusField = "Allowed" then some (parseRange (trimS rngField))
    else none
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `IdentifierStatus.txt`, embedded at compile time. -/
def identifierStatusRaw : String := include_str "../Ucd/IdentifierStatus.txt"

/-- Allowed-identifier ranges, each encoded as `(min, max)` inclusive. -/
def allowedRanges : Array (Nat × Nat) :=
  ((identifierStatusRaw.splitOn "\n").filterMap parseIdentifierStatusRow).toArray

/-- Default `Identifier_Status` for codepoints not in `allowedRanges`. -/
def defaultStatus : IdentifierStatus := .Restricted

end Unicode.Generated.IdentifierStatus
