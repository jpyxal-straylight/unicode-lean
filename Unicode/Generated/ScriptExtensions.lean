/-
  Unicode.Generated.ScriptExtensions

  Derived from `lemma/lean/Unicode/Ucd/ScriptExtensions.txt` (UCD 17.0.0).

  Do not hand-edit. Regenerate from the source file to update.

  Semantics (UAX #24): Script_Extensions assigns a SET of script
  abbreviations to a codepoint, listing the scripts that commonly use
  it. Codepoints not covered by any range fall back to their primary
  Script property value (see `Unicode.Generated.Scripts`).

  Script abbreviations are the four-letter codes from PropertyValueAliases
  (e.g. `Latn` for Latin, `Cyrl` for Cyrillic). The mapping back to the
  long-form Script enum is intentionally not provided here; callers that
  need it should consult the UCD `PropertyValueAliases.txt` table.

  Counts: 99 abbreviations, 206 ranges.
-/

namespace Unicode.Generated.ScriptExtensions

inductive ScriptAbbrev where
  | Adlm
  | Aghb
  | Arab
  | Armn
  | Avst
  | Beng
  | Bopo
  | Bugi
  | Buhd
  | Cakm
  | Cari
  | Cher
  | Copt
  | Cpmn
  | Cprt
  | Cyrl
  | Deva
  | Dogr
  | Dupl
  | Elba
  | Ethi
  | Gara
  | Geor
  | Glag
  | Gong
  | Gonm
  | Goth
  | Gran
  | Grek
  | Gujr
  | Gukh
  | Guru
  | Hang
  | Hani
  | Hano
  | Hebr
  | Hira
  | Hung
  | Java
  | Kali
  | Kana
  | Khoj
  | Knda
  | Kthi
  | Latn
  | Limb
  | Lina
  | Linb
  | Lisu
  | Lyci
  | Lydi
  | Mahj
  | Mand
  | Mani
  | Mero
  | Mlym
  | Modi
  | Mong
  | Mult
  | Mymr
  | Nand
  | Newa
  | Nkoo
  | Onao
  | Orkh
  | Orya
  | Osge
  | Ougr
  | Perm
  | Phag
  | Phlp
  | Rohg
  | Runr
  | Samr
  | Shaw
  | Shrd
  | Sind
  | Sinh
  | Sogd
  | Sunu
  | Sylo
  | Syrc
  | Tagb
  | Takr
  | Tale
  | Taml
  | Tang
  | Telu
  | Tfng
  | Tglg
  | Thaa
  | Thai
  | Tibt
  | Tirh
  | Todr
  | Toto
  | Tutg
  | Yezi
  | Yiii
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

def parseScriptAbbrev? : String → Option ScriptAbbrev
  | "Adlm" => some .Adlm
  | "Aghb" => some .Aghb
  | "Arab" => some .Arab
  | "Armn" => some .Armn
  | "Avst" => some .Avst
  | "Beng" => some .Beng
  | "Bopo" => some .Bopo
  | "Bugi" => some .Bugi
  | "Buhd" => some .Buhd
  | "Cakm" => some .Cakm
  | "Cari" => some .Cari
  | "Cher" => some .Cher
  | "Copt" => some .Copt
  | "Cpmn" => some .Cpmn
  | "Cprt" => some .Cprt
  | "Cyrl" => some .Cyrl
  | "Deva" => some .Deva
  | "Dogr" => some .Dogr
  | "Dupl" => some .Dupl
  | "Elba" => some .Elba
  | "Ethi" => some .Ethi
  | "Gara" => some .Gara
  | "Geor" => some .Geor
  | "Glag" => some .Glag
  | "Gong" => some .Gong
  | "Gonm" => some .Gonm
  | "Goth" => some .Goth
  | "Gran" => some .Gran
  | "Grek" => some .Grek
  | "Gujr" => some .Gujr
  | "Gukh" => some .Gukh
  | "Guru" => some .Guru
  | "Hang" => some .Hang
  | "Hani" => some .Hani
  | "Hano" => some .Hano
  | "Hebr" => some .Hebr
  | "Hira" => some .Hira
  | "Hung" => some .Hung
  | "Java" => some .Java
  | "Kali" => some .Kali
  | "Kana" => some .Kana
  | "Khoj" => some .Khoj
  | "Knda" => some .Knda
  | "Kthi" => some .Kthi
  | "Latn" => some .Latn
  | "Limb" => some .Limb
  | "Lina" => some .Lina
  | "Linb" => some .Linb
  | "Lisu" => some .Lisu
  | "Lyci" => some .Lyci
  | "Lydi" => some .Lydi
  | "Mahj" => some .Mahj
  | "Mand" => some .Mand
  | "Mani" => some .Mani
  | "Mero" => some .Mero
  | "Mlym" => some .Mlym
  | "Modi" => some .Modi
  | "Mong" => some .Mong
  | "Mult" => some .Mult
  | "Mymr" => some .Mymr
  | "Nand" => some .Nand
  | "Newa" => some .Newa
  | "Nkoo" => some .Nkoo
  | "Onao" => some .Onao
  | "Orkh" => some .Orkh
  | "Orya" => some .Orya
  | "Osge" => some .Osge
  | "Ougr" => some .Ougr
  | "Perm" => some .Perm
  | "Phag" => some .Phag
  | "Phlp" => some .Phlp
  | "Rohg" => some .Rohg
  | "Runr" => some .Runr
  | "Samr" => some .Samr
  | "Shaw" => some .Shaw
  | "Shrd" => some .Shrd
  | "Sind" => some .Sind
  | "Sinh" => some .Sinh
  | "Sogd" => some .Sogd
  | "Sunu" => some .Sunu
  | "Sylo" => some .Sylo
  | "Syrc" => some .Syrc
  | "Tagb" => some .Tagb
  | "Takr" => some .Takr
  | "Tale" => some .Tale
  | "Taml" => some .Taml
  | "Tang" => some .Tang
  | "Telu" => some .Telu
  | "Tfng" => some .Tfng
  | "Tglg" => some .Tglg
  | "Thaa" => some .Thaa
  | "Thai" => some .Thai
  | "Tibt" => some .Tibt
  | "Tirh" => some .Tirh
  | "Todr" => some .Todr
  | "Toto" => some .Toto
  | "Tutg" => some .Tutg
  | "Yezi" => some .Yezi
  | "Yiii" => some .Yiii
  | unknownScriptAbbrev => Function.const String none unknownScriptAbbrev

/-- Parse one ScriptExtensions.txt row. Returns `none` for blank/comment
    lines or rows whose abbreviation list is empty / unrecognised. -/
def parseScriptExtensionRow
    (rawLine : String) : Option (Nat × Nat × Array ScriptAbbrev) :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | [rngField, abbrevField] =>
    let (lo, hi) := parseRange (trimS rngField)
    let abbrevs := (((trimS abbrevField).splitOn " ").filterMap (fun tok =>
      let t := trimS tok
      if t.isEmpty then none else parseScriptAbbrev? t)).toArray
    if abbrevs.isEmpty then none else some (lo, hi, abbrevs)
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `ScriptExtensions.txt`, embedded at compile time. -/
def scriptExtensionsRaw : String := include_str "../Ucd/ScriptExtensions.txt"

/-- Range table from ScriptExtensions.txt. Each row carries the set of
    Script_Extensions for one inclusive codepoint range. -/
def scriptExtensionRanges : Array (Nat × Nat × Array ScriptAbbrev) :=
  ((scriptExtensionsRaw.splitOn "\n").filterMap parseScriptExtensionRow).toArray

end Unicode.Generated.ScriptExtensions
