/-
  Unicode.Generated.IdentifierType

  Identifier_Type ranges from `lemma/lean/Unicode/Ucd/IdentifierType.txt`
  (UTS #39 16.0.0), embedded as a String constant via `include_str`
  and parsed once at module load. Pattern follows
  `fgdorais/lean4-unicode-basic`.

  Semantics: each explicit range maps its codepoints to a SET of
  Identifier_Type values (UTS #39 Table 1). Set membership is ordered by
  the source file's column convention but logically unordered. Codepoints
  not covered by an explicit range fall back to the LAST `defaultRanges`
  entry whose range contains them — matching the `@missing` header.
-/

namespace Unicode.Generated.IdentifierType

/-- The 12 Identifier_Type atomic values defined by UTS #39 Table 1. The
    Lean constructor name removes the underscore from the UCD long name. -/
inductive IdentifierType where
  | NotCharacter
  | Deprecated
  | DefaultIgnorable
  | NotNFKC
  | NotXID
  | Exclusion
  | Obsolete
  | Technical
  | UncommonUse
  | LimitedUse
  | Inclusion
  | Recommended
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

def parseIdentifierType? : String → Option IdentifierType
  | "Not_Character"      => some .NotCharacter
  | "Deprecated"         => some .Deprecated
  | "Default_Ignorable"  => some .DefaultIgnorable
  | "Not_NFKC"           => some .NotNFKC
  | "Not_XID"            => some .NotXID
  | "Exclusion"          => some .Exclusion
  | "Obsolete"           => some .Obsolete
  | "Technical"          => some .Technical
  | "Uncommon_Use"       => some .UncommonUse
  | "Limited_Use"        => some .LimitedUse
  | "Inclusion"          => some .Inclusion
  | "Recommended"        => some .Recommended
  | unknownIdentifierType => Function.const String none unknownIdentifierType

/-- Parse the type-set field (space-separated long names). -/
def parseTypeSet (s : String) : Array IdentifierType :=
  ((s.splitOn " ").filterMap (fun tok =>
    let t := trimS tok
    if t.isEmpty then none else parseIdentifierType? t)).toArray

/-- Parse one IdentifierType.txt explicit row. -/
def parseExplicitRow
    (rawLine : String) : Option (Nat × Nat × Array IdentifierType) :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | [rngField, typesField] =>
    let (lo, hi) := parseRange (trimS rngField)
    let types := parseTypeSet (trimS typesField)
    if types.isEmpty then none else some (lo, hi, types)
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Parse one `@missing:` directive. Format:
    `# @missing: <range>; <type-set>`. -/
def parseMissingRow
    (rawLine : String) : Option (Nat × Nat × Array IdentifierType) :=
  let line := trimS rawLine
  if !line.startsWith "# @missing:" then none else
  let body := trimS (line.drop "# @missing:".length).toString
  match String.splitOn body ";" with
  | [rngField, typesField] =>
    let (lo, hi) := parseRange (trimS rngField)
    let types := parseTypeSet (trimS typesField)
    if types.isEmpty then none else some (lo, hi, types)
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `IdentifierType.txt`, embedded at compile time. -/
def identifierTypeRaw : String := include_str "../Ucd/IdentifierType.txt"

/-! Per-range Identifier_Type assignments. -/
def explicitRanges : Array (Nat × Nat × Array IdentifierType) :=
  ((identifierTypeRaw.splitOn "\n").filterMap parseExplicitRow).toArray

/-! `@missing` default assignments from the source header. -/
def defaultRanges : Array (Nat × Nat × Array IdentifierType) :=
  ((identifierTypeRaw.splitOn "\n").filterMap parseMissingRow).toArray

end Unicode.Generated.IdentifierType
