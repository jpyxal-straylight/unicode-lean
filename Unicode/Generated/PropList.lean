/-
  Unicode.Generated.PropList

  PropList from `lemma/lean/Unicode/Ucd/PropList.txt` (UCD 17.0.0),
  embedded as a String constant via `include_str` and parsed once at
  module load. Pattern follows `fgdorais/lean4-unicode-basic`.

  Semantics (UAX #44 §5.7): each entry assigns a binary property to a
  range of codepoints. A codepoint may have multiple binary properties
  set; each property assignment appears as a separate row. Codepoints
  not covered by any row do not have the property set.

  Counts: 38 properties, 1744 ranges.
-/

namespace Unicode.Generated.PropList

inductive BinaryProperty where
  | ASCII_Hex_Digit
  | Bidi_Control
  | Dash
  | Deprecated
  | Diacritic
  | Extender
  | Hex_Digit
  | Hyphen
  | ID_Compat_Math_Continue
  | ID_Compat_Math_Start
  | Ideographic
  | IDS_Binary_Operator
  | IDS_Trinary_Operator
  | IDS_Unary_Operator
  | Join_Control
  | Logical_Order_Exception
  | Modifier_Combining_Mark
  | Noncharacter_Code_Point
  | Other_Alphabetic
  | Other_Default_Ignorable_Code_Point
  | Other_Grapheme_Extend
  | Other_ID_Continue
  | Other_ID_Start
  | Other_Lowercase
  | Other_Math
  | Other_Uppercase
  | Pattern_Syntax
  | Pattern_White_Space
  | Prepended_Concatenation_Mark
  | Quotation_Mark
  | Radical
  | Regional_Indicator
  | Sentence_Terminal
  | Soft_Dotted
  | Terminal_Punctuation
  | Unified_Ideograph
  | Variation_Selector
  | White_Space
  deriving DecidableEq, Repr, Inhabited

/-- Map a property-name string from `PropList.txt` to its enum
    constructor. Returns `none` for unrecognised names; the caller
    drops such rows. -/
def parseBinaryProperty? : String → Option BinaryProperty
  | "ASCII_Hex_Digit"                    => some .ASCII_Hex_Digit
  | "Bidi_Control"                       => some .Bidi_Control
  | "Dash"                               => some .Dash
  | "Deprecated"                         => some .Deprecated
  | "Diacritic"                          => some .Diacritic
  | "Extender"                           => some .Extender
  | "Hex_Digit"                          => some .Hex_Digit
  | "Hyphen"                             => some .Hyphen
  | "ID_Compat_Math_Continue"            => some .ID_Compat_Math_Continue
  | "ID_Compat_Math_Start"               => some .ID_Compat_Math_Start
  | "Ideographic"                        => some .Ideographic
  | "IDS_Binary_Operator"                => some .IDS_Binary_Operator
  | "IDS_Trinary_Operator"               => some .IDS_Trinary_Operator
  | "IDS_Unary_Operator"                 => some .IDS_Unary_Operator
  | "Join_Control"                       => some .Join_Control
  | "Logical_Order_Exception"            => some .Logical_Order_Exception
  | "Modifier_Combining_Mark"            => some .Modifier_Combining_Mark
  | "Noncharacter_Code_Point"            => some .Noncharacter_Code_Point
  | "Other_Alphabetic"                   => some .Other_Alphabetic
  | "Other_Default_Ignorable_Code_Point" => some .Other_Default_Ignorable_Code_Point
  | "Other_Grapheme_Extend"              => some .Other_Grapheme_Extend
  | "Other_ID_Continue"                  => some .Other_ID_Continue
  | "Other_ID_Start"                     => some .Other_ID_Start
  | "Other_Lowercase"                    => some .Other_Lowercase
  | "Other_Math"                         => some .Other_Math
  | "Other_Uppercase"                    => some .Other_Uppercase
  | "Pattern_Syntax"                     => some .Pattern_Syntax
  | "Pattern_White_Space"                => some .Pattern_White_Space
  | "Prepended_Concatenation_Mark"       => some .Prepended_Concatenation_Mark
  | "Quotation_Mark"                     => some .Quotation_Mark
  | "Radical"                            => some .Radical
  | "Regional_Indicator"                 => some .Regional_Indicator
  | "Sentence_Terminal"                  => some .Sentence_Terminal
  | "Soft_Dotted"                        => some .Soft_Dotted
  | "Terminal_Punctuation"               => some .Terminal_Punctuation
  | "Unified_Ideograph"                  => some .Unified_Ideograph
  | "Variation_Selector"                 => some .Variation_Selector
  | "White_Space"                        => some .White_Space
  | unknownPropertyName                  =>
      Function.const String none unknownPropertyName

/-- Convert a single ASCII hex digit to its Nat value. Returns 0 for
    non-hex inputs (caller is expected to feed validated digit chars
    extracted from the UCD source). -/
def hexDigitVal (c : Char) : Nat :=
  let n := c.toNat
  if n ≥ 0x30 ∧ n ≤ 0x39 then n - 0x30           -- '0'..'9'
  else if n ≥ 0x61 ∧ n ≤ 0x66 then n - 0x61 + 10 -- 'a'..'f'
  else if n ≥ 0x41 ∧ n ≤ 0x46 then n - 0x41 + 10 -- 'A'..'F'
  else 0

/-- Parse a hex string (e.g., `"0x10FFFF"` or `"10FFFF"`) to a `Nat`.
    Whitespace is not stripped — the caller is expected to trim. -/
def parseHex (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexDigitVal c) 0

/-- Trim ASCII whitespace, returning a `String` (not the deprecated
    Slice form). -/
@[inline]
def trimS (s : String) : String := (String.trimAscii s).toString

/-- Parse one PropList.txt row. Returns `none` for blank/comment lines
    or rows whose property name is not in `BinaryProperty`. -/
def parsePropListRow (rawLine : String) : Option (Nat × Nat × BinaryProperty) :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line : String := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | [rngField, propField] =>
    let rng : String := trimS rngField
    let (lo, hi) :=
      match String.splitOn rng ".." with
      | [single]  => let n := parseHex single; (n, n)
      | [a, b]    => (parseHex a, parseHex b)
      | irregularRange => Function.const (List String) (0, 0) irregularRange
    match parseBinaryProperty? (trimS propField) with
    | some prop => some (lo, hi, prop)
    | none      => none
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `PropList.txt`, embedded at compile time. -/
def propListRaw : String := include_str "../Ucd/PropList.txt"

/-- Range table mapping codepoint ranges to binary properties from
    PropList.txt. Inclusive on both ends. -/
def propRanges : Array (Nat × Nat × BinaryProperty) :=
  ((String.splitOn propListRaw "\n").filterMap parsePropListRow).toArray

theorem propRanges_count : propRanges.size = 1744 := by native_decide

end Unicode.Generated.PropList
