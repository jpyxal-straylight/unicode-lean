/-
  Unicode.Generated.UnicodeData

  NFC-relevant subset of `UnicodeData.txt` (UCD 17.0.0), embedded as a
  String constant via `include_str` and parsed once at module load.
  Pattern follows `fgdorais/lean4-unicode-basic`.

  Semantics (UAX #44 §5.3): each row carries the three NFC-relevant
  fields for a single codepoint:

    * `codepoint`                  : the codepoint itself
    * `canonicalCombiningClass`    : UCD field 3 (for UAX #15 reorder)
    * `canonicalDecomposition`     : UCD field 5 — the canonical target
                                     sequence, OR `#[]` if the row has
                                     no decomposition or only a compat
                                     (`<tag>`-prefixed) decomposition

  Rows where `canonicalCombiningClass = 0` AND `canonicalDecomposition
  = #[]` are filtered out: they are NFC-inert and do not require a
  table entry. Callers resolving a codepoint not present in `rows`
  therefore use `(ccc = 0, decomposition = #[])`, matching the UCD's
  implicit default.
-/

namespace Unicode.Generated.UnicodeData

/-- One entry of the NFC-relevant subset of UnicodeData.txt. Fields
    correspond to UCD columns 0, 3, and 5 per UAX #44. -/
structure UnicodeDataRow where
  codepoint               : Nat
  canonicalCombiningClass : Nat
  canonicalDecomposition  : Array Nat
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

/-- Parse the canonical-decomposition field of a UnicodeData row.
    Returns `#[]` for empty fields and for compatibility decompositions
    (those starting with a `<tag>` prefix). Otherwise splits on space
    and parses each token as a hex codepoint. -/
def parseCanonicalDecomp (field : String) : Array Nat :=
  let s := trimS field
  if s.isEmpty then #[]
  else if s.startsWith "<" then #[]  -- compat, not canonical
  else
    ((s.splitOn " ").filterMap (fun tok =>
      let t := trimS tok
      if t.isEmpty then none else some (parseHex t))).toArray

/-- Parse one UnicodeData.txt row. Returns `none` for blank lines or
    NFC-inert rows (ccc = 0 AND no canonical decomposition). -/
def parseUnicodeDataRow (rawLine : String) : Option UnicodeDataRow :=
  let line := trimS rawLine
  if line.isEmpty then none else
  let fields := String.splitOn line ";"
  if fields.length < 6 then none else
  let cp := parseHex (trimS fields[0]!)
  let ccc := (trimS fields[3]!).toNat?.getD 0
  let decomp := parseCanonicalDecomp fields[5]!
  if ccc = 0 ∧ decomp.isEmpty then none
  else some ⟨cp, ccc, decomp⟩

/-- Raw text of `UnicodeData.txt`, embedded at compile time. -/
def unicodeDataRaw : String := include_str "../Ucd/UnicodeData.txt"

/-- NFC-relevant rows from UnicodeData.txt. Sorted by codepoint
    (the source file's natural order). -/
def rows : Array UnicodeDataRow :=
  ((unicodeDataRaw.splitOn "\n").filterMap parseUnicodeDataRow).toArray

end Unicode.Generated.UnicodeData
