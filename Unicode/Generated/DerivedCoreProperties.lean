/-
  Unicode.Generated.DerivedCoreProperties

  Identifier-relevant boolean properties from
  `lemma/lean/Unicode/Ucd/DerivedCoreProperties.txt` (UCD 17.0.0),
  embedded as a String constant via `include_str` and parsed once at
  module load. Pattern follows `fgdorais/lean4-unicode-basic`.

  Semantics: each array enumerates the (min, max) ranges for one
  boolean property derived from the UCD. A codepoint has the property
  iff it is covered by at least one range in the corresponding array.
  The source file's other (non-identifier-relevant) properties are
  deliberately not extracted here.
-/

namespace Unicode.Generated.DerivedCoreProperties

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

/-- Intermediate parsed row: range plus property name. We then filter
    by name into the per-property arrays below. -/
structure RawRow where
  lo   : Nat
  hi   : Nat
  prop : String
  deriving Inhabited

def parseRawRow (rawLine : String) : Option RawRow :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | rngField :: propField :: trailingFields =>
    let (lo, hi) := parseRange (trimS rngField)
    Function.const (List String) (some ⟨lo, hi, trimS propField⟩) trailingFields
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `DerivedCoreProperties.txt`, embedded at compile time. -/
def derivedCorePropertiesRaw : String :=
  include_str "../Ucd/DerivedCoreProperties.txt"

/-- All parsed rows, retained as the intermediate form for the
    per-property derived definitions below. -/
def parsedRows : Array RawRow :=
  ((derivedCorePropertiesRaw.splitOn "\n").filterMap parseRawRow).toArray

/-! ID_Start ranges (UAX #44 §5.7.5). -/
def idStart : Array (Nat × Nat) :=
  parsedRows.filterMap (fun r =>
    if r.prop = "ID_Start" then some (r.lo, r.hi) else none)

/-! ID_Continue ranges. -/
def idContinue : Array (Nat × Nat) :=
  parsedRows.filterMap (fun r =>
    if r.prop = "ID_Continue" then some (r.lo, r.hi) else none)

/-! XID_Start ranges. -/
def xidStart : Array (Nat × Nat) :=
  parsedRows.filterMap (fun r =>
    if r.prop = "XID_Start" then some (r.lo, r.hi) else none)

/-! XID_Continue ranges. -/
def xidContinue : Array (Nat × Nat) :=
  parsedRows.filterMap (fun r =>
    if r.prop = "XID_Continue" then some (r.lo, r.hi) else none)

/-! Default_Ignorable_Code_Point ranges. -/
def defaultIgnorable : Array (Nat × Nat) :=
  parsedRows.filterMap (fun r =>
    if r.prop = "Default_Ignorable_Code_Point" then some (r.lo, r.hi) else none)

end Unicode.Generated.DerivedCoreProperties
