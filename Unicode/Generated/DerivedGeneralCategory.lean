/-
  Unicode.Generated.DerivedGeneralCategory

  General_Category extracted from `lemma/lean/Unicode/Ucd/UnicodeData.txt`
  (UCD 17.0.0) at module load. Pattern follows
  `fgdorais/lean4-unicode-basic`.

  Semantics: General_Category per UAX #44 §5.7.1. The 30 atomic
  categories fall into seven major groupings — Letter (Lu/Ll/Lt/Lm/Lo),
  Mark (Mn/Mc/Me), Number (Nd/Nl/No), Punctuation (Pc/Pd/Ps/Pe/Pi/Pf/Po),
  Symbol (Sm/Sc/Sk/So), Separator (Zs/Zl/Zp), and Other
  (Cc/Cf/Cs/Co/Cn). The `explicitRanges` table covers every codepoint
  listed in UnicodeData.txt (including compressed `First>/Last>` runs
  such as CJK Ideograph and Hangul Syllable); codepoints outside the
  listed ranges default to `Cn` (Unassigned) via the `defaultGC`
  fallback, matching UAX #44's implicit-default convention.
-/

namespace Unicode.Generated.DerivedGeneralCategory

/-- The 30 General_Category values defined by UAX #44 §5.7.1. -/
inductive GC where
  | Lu | Ll | Lt | Lm | Lo
  | Mn | Mc | Me
  | Nd | Nl | No
  | Pc | Pd | Ps | Pe | Pi | Pf | Po
  | Sm | Sc | Sk | So
  | Zs | Zl | Zp
  | Cc | Cf | Cs | Co | Cn
  deriving DecidableEq, Repr, Inhabited

/-- Default GC for codepoints not listed in UnicodeData.txt. -/
def defaultGC : GC := .Cn

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

def parseGC? : String → Option GC
  | "Lu" => some .Lu | "Ll" => some .Ll | "Lt" => some .Lt
  | "Lm" => some .Lm | "Lo" => some .Lo
  | "Mn" => some .Mn | "Mc" => some .Mc | "Me" => some .Me
  | "Nd" => some .Nd | "Nl" => some .Nl | "No" => some .No
  | "Pc" => some .Pc | "Pd" => some .Pd | "Ps" => some .Ps
  | "Pe" => some .Pe | "Pi" => some .Pi | "Pf" => some .Pf
  | "Po" => some .Po
  | "Sm" => some .Sm | "Sc" => some .Sc | "Sk" => some .Sk
  | "So" => some .So
  | "Zs" => some .Zs | "Zl" => some .Zl | "Zp" => some .Zp
  | "Cc" => some .Cc | "Cf" => some .Cf | "Cs" => some .Cs
  | "Co" => some .Co | "Cn" => some .Cn
  | unknownGcLabel => Function.const String none unknownGcLabel

/-- Intermediate parsed row: codepoint, name field, GC. The name
    field is needed to detect `<XYZ, First>` / `<XYZ, Last>` range
    markers. -/
structure RawRow where
  cp   : Nat
  name : String
  gc   : GC
  deriving Inhabited

def parseRawRow (rawLine : String) : Option RawRow :=
  let line := trimS rawLine
  if line.isEmpty then none else
  let fields := String.splitOn line ";"
  if fields.length < 3 then none else
  let cp := parseHex (trimS fields[0]!)
  let name := trimS fields[1]!
  match parseGC? (trimS fields[2]!) with
  | some gc => some ⟨cp, name, gc⟩
  | none    => none

/-- Walk the parsed rows and pair `<XYZ, First>` markers with their
    matching `<XYZ, Last>` markers, emitting one closed range per
    pair. Non-paired rows emit singleton ranges `(cp, cp, gc)`. -/
def coalesceStep (rows : Array RawRow) (i : Nat)
    (acc : Array (Nat × Nat × GC)) : Array (Nat × Nat × GC) :=
  if h : i < rows.size then
    let r := rows[i]
    if r.name.endsWith ", First>" ∧ i + 1 < rows.size then
      let r' := rows[i + 1]!
      if r'.name.endsWith ", Last>" ∧ r'.gc = r.gc then
        coalesceStep rows (i + 2) (acc.push (r.cp, r'.cp, r.gc))
      else
        coalesceStep rows (i + 1) (acc.push (r.cp, r.cp, r.gc))
    else
      coalesceStep rows (i + 1) (acc.push (r.cp, r.cp, r.gc))
  else acc
termination_by rows.size - i

def coalesceRanges (rows : Array RawRow) : Array (Nat × Nat × GC) :=
  coalesceStep rows 0 #[]

/-- Raw text of `UnicodeData.txt`, embedded at compile time. -/
def unicodeDataRaw : String := include_str "../Ucd/UnicodeData.txt"

/-! Per-range General_Category assignments. First/Last marker pairs in
    the source are paired into a single closed range; other rows are
    singleton ranges. -/
def explicitRanges : Array (Nat × Nat × GC) :=
  coalesceRanges
    ((unicodeDataRaw.splitOn "\n").filterMap parseRawRow).toArray

/-- Look up the General_Category for a codepoint. Returns the
    `explicitRanges` entry whose range covers `cp`, or `defaultGC`
    (`Cn`) if no range covers it. -/
def lookup (cp : Nat) : GC :=
  match explicitRanges.findSome? (fun ⟨min, max, gc⟩ =>
          if min ≤ cp ∧ cp ≤ max then some gc else none) with
  | some g => g
  | none   => defaultGC

end Unicode.Generated.DerivedGeneralCategory
