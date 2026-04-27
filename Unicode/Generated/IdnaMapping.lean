/-
  Unicode.Generated.IdnaMapping

  IDNA mapping table from `lemma/lean/Unicode/Ucd/IdnaMappingTable.txt`
  (UTS #46 16.0.0 — IDNA Compatibility Processing), embedded as a
  String constant via `include_str` and parsed once at module load.
  Pattern follows `fgdorais/lean4-unicode-basic`.

  Semantics (UTS #46): each row maps a codepoint range to one of five
  IDNA processing dispositions, optionally with a mapping target
  sequence and an IDNA2008 status flag.

  Dispositions:
    * `Valid`       — admissible without modification.
    * `Mapped`      — replace with the `mapping` sequence.
    * `Ignored`     — drop from the processed string.
    * `Deviation`   — admitted in transitional processing, mapped in
                      non-transitional. The `mapping` sequence applies.
    * `Disallowed`  — reject the input string.

  IDNA2008 status (column 4 of the source):
    * `NV8` — Not valid in IDNA2008 (was valid in IDNA2003).
    * `XV8` — Excluded from valid in IDNA2008 by general exclusion.
    * `none` — IDNA2008 status matches IDNA2003 default for the row.

  Counts: 9185 ranges.
-/

namespace Unicode.Generated.IdnaMapping

inductive IdnaDisposition where
  | Valid
  | Mapped
  | Ignored
  | Deviation
  | Disallowed
  deriving DecidableEq, Repr, Inhabited

inductive IdnaIdna2008Status where
  | NV8
  | XV8
  deriving DecidableEq, Repr, Inhabited

/-- One row of the IDNA mapping table. `mapping` is empty when the row
    has no mapping target (e.g. for `Valid`, `Ignored`, `Disallowed`),
    and carries one or more codepoints for `Mapped` and the
    transitional case of `Deviation`. -/
structure IdnaRow where
  min          : Nat
  max          : Nat
  disposition  : IdnaDisposition
  mapping      : Array Nat
  idna2008     : Option IdnaIdna2008Status
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

def parseDisposition? : String → Option IdnaDisposition
  | "valid"      => some .Valid
  | "mapped"     => some .Mapped
  | "ignored"    => some .Ignored
  | "deviation"  => some .Deviation
  | "disallowed" => some .Disallowed
  | unknownDisposition => Function.const String none unknownDisposition

def parseIdna2008? : String → Option IdnaIdna2008Status
  | "NV8" => some .NV8
  | "XV8" => some .XV8
  | unknownIdna2008Status => Function.const String none unknownIdna2008Status

/-- Parse the codepoint-range field. Returns `(min, max)`; for a
    single-codepoint row, `min = max`. -/
def parseRange (s : String) : Nat × Nat :=
  match String.splitOn s ".." with
  | [single]  => let n := parseHex single; (n, n)
  | [a, b]    => (parseHex a, parseHex b)
  | irregularRange => Function.const (List String) (0, 0) irregularRange

/-- Parse a space-separated list of hex codepoints (the `mapping`
    column for Mapped / Deviation rows). -/
def parseCodepoints (s : String) : Array Nat :=
  ((s.splitOn " ").filterMap (fun tok =>
    let t := trimS tok
    if t.isEmpty then none else some (parseHex t))).toArray

/-- Parse one IdnaMappingTable.txt row. Returns `none` for blank or
    comment lines. -/
def parseIdnaRow (rawLine : String) : Option IdnaRow := Id.run do
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then return none
  let fields := String.splitOn line ";"
  if fields.length < 2 then return none
  let (lo, hi) := parseRange (trimS fields[0]!)
  match parseDisposition? (trimS fields[1]!) with
  | none => none
  | some disp =>
    let mapping :=
      if fields.length ≥ 3 then parseCodepoints (trimS fields[2]!)
      else #[]
    let idna2008 :=
      if fields.length ≥ 4 then parseIdna2008? (trimS fields[3]!)
      else none
    some ⟨lo, hi, disp, mapping, idna2008⟩

/-- Raw text of `IdnaMappingTable.txt`, embedded at compile time. -/
def idnaMappingRaw : String := include_str "../Ucd/IdnaMappingTable.txt"

/-- Range table mapping codepoint ranges to their IDNA disposition. -/
def idnaMappingRanges : Array IdnaRow :=
  ((idnaMappingRaw.splitOn "\n").filterMap parseIdnaRow).toArray

end Unicode.Generated.IdnaMapping
