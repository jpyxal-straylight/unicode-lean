/-
  Unicode.Generated.DerivedNormalizationProps

  NFC-relevant subset of `DerivedNormalizationProps.txt` (UCD 17.0.0),
  embedded as a String constant via `include_str` and parsed once at
  module load. Pattern follows `fgdorais/lean4-unicode-basic`.

  Semantics (UAX #15):

  * `nfcQC` enumerates every codepoint whose NFC_QuickCheck is `N` (No,
    cannot start an NFC form) or `M` (Maybe — needs further analysis).
    Every other codepoint is `Y` (Yes, is in NFC form unchanged) — the
    `defaultNfcQC` constant records this `@missing` default.

  * `fullCompositionExclusion` enumerates codepoints that decompose but
    do NOT recompose under canonical composition.

  * `nfkcQC`, `nfdQC`, `nfkdQC` are the analogous tables for NFKC, NFD,
    NFKD QuickCheck. NFD/NFKD only have `N` values (no `M`).
-/

namespace Unicode.Generated.DerivedNormalizationProps

inductive NFC_QC where
  | Y
  | N
  | M
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

/-- Parse the range field (`XXXX` or `XXXX..YYYY`). -/
def parseRange (s : String) : Nat × Nat :=
  match String.splitOn s ".." with
  | [single]  => let n := parseHex single; (n, n)
  | [a, b]    => (parseHex a, parseHex b)
  | irregularRange => Function.const (List String) (0, 0) irregularRange

/-- Parse the QC value field. NFC_QC / NFKC_QC use both `N` and `M`;
    NFD_QC / NFKD_QC use only `N`. -/
def parseQC? : String → Option NFC_QC
  | "N" => some .N
  | "M" => some .M
  | unknownQcLabel => Function.const String none unknownQcLabel

/-- Parsed structure: a row from `DerivedNormalizationProps.txt`. The
    third field is the property name; the fourth (optional) is the
    value, present for QC properties and FC_NFKC closures. -/
structure RawRow where
  lo    : Nat
  hi    : Nat
  prop  : String
  value : String
  deriving Inhabited

/-- Parse one `DerivedNormalizationProps.txt` row into the raw form.
    Returns `none` for blank/comment lines. -/
def parseRawRow (rawLine : String) : Option RawRow :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  let fields := String.splitOn line ";"
  match fields with
  | rngField :: propField :: rest =>
    let (lo, hi) := parseRange (trimS rngField)
    let prop := trimS propField
    let value := match rest with
      | []                    => ""
      | v :: trailingFields   => Function.const (List String) (trimS v) trailingFields
    some ⟨lo, hi, prop, value⟩
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `DerivedNormalizationProps.txt`, embedded at compile time. -/
def derivedNormalizationPropsRaw : String :=
  include_str "../Ucd/DerivedNormalizationProps.txt"

/-- All parsed rows from the source, retained intermediate form for the
    per-property derived definitions below. -/
def parsedRows : Array RawRow :=
  ((derivedNormalizationPropsRaw.splitOn "\n").filterMap parseRawRow).toArray

/-! NFC_QC explicit ranges from the data section. Codepoints not
    covered have `defaultNfcQC`. -/
def nfcQC : Array (Nat × Nat × NFC_QC) :=
  parsedRows.filterMap (fun r =>
    if r.prop = "NFC_QC" then
      (parseQC? r.value).map (fun v => (r.lo, r.hi, v))
    else none)

def defaultNfcQC : NFC_QC := .Y

/-! Full_Composition_Exclusion ranges. -/
def fullCompositionExclusion : Array (Nat × Nat) :=
  parsedRows.filterMap (fun r =>
    if r.prop = "Full_Composition_Exclusion" then some (r.lo, r.hi)
    else none)

/-! NFKC_QC explicit ranges. -/
def nfkcQC : Array (Nat × Nat × NFC_QC) :=
  parsedRows.filterMap (fun r =>
    if r.prop = "NFKC_QC" then
      (parseQC? r.value).map (fun v => (r.lo, r.hi, v))
    else none)

def defaultNfkcQC : NFC_QC := .Y

/-! NFD_QC explicit ranges (only `N` values; no `M` for NFD). -/
def nfdQC : Array (Nat × Nat × NFC_QC) :=
  parsedRows.filterMap (fun r =>
    if r.prop = "NFD_QC" then
      (parseQC? r.value).map (fun v => (r.lo, r.hi, v))
    else none)

def defaultNfdQC : NFC_QC := .Y

/-! NFKD_QC explicit ranges (only `N` values). -/
def nfkdQC : Array (Nat × Nat × NFC_QC) :=
  parsedRows.filterMap (fun r =>
    if r.prop = "NFKD_QC" then
      (parseQC? r.value).map (fun v => (r.lo, r.hi, v))
    else none)

def defaultNfkdQC : NFC_QC := .Y

end Unicode.Generated.DerivedNormalizationProps
