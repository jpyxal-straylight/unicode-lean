/-
  Unicode.Generated.Scripts

  Script ranges from `lemma/lean/Unicode/Ucd/Scripts.txt` (UCD 17.0.0),
  embedded as a String constant via `include_str` and parsed once at
  module load. Pattern follows `fgdorais/lean4-unicode-basic`.

  Semantics (UAX #24): every assigned codepoint has exactly one Script
  property value. Codepoints not covered by any range take the
  `defaultScript` (`Unknown`).

  Counts: 174 scripts in the data + `Unknown` default, 2287 ranges.
-/

namespace Unicode.Generated.Scripts

inductive Script where
  | Unknown
  | Adlam
  | Ahom
  | Anatolian_Hieroglyphs
  | Arabic
  | Armenian
  | Avestan
  | Balinese
  | Bamum
  | Bassa_Vah
  | Batak
  | Bengali
  | Beria_Erfe
  | Bhaiksuki
  | Bopomofo
  | Brahmi
  | Braille
  | Buginese
  | Buhid
  | Canadian_Aboriginal
  | Carian
  | Caucasian_Albanian
  | Chakma
  | Cham
  | Cherokee
  | Chorasmian
  | Common
  | Coptic
  | Cuneiform
  | Cypriot
  | Cypro_Minoan
  | Cyrillic
  | Deseret
  | Devanagari
  | Dives_Akuru
  | Dogra
  | Duployan
  | Egyptian_Hieroglyphs
  | Elbasan
  | Elymaic
  | Ethiopic
  | Garay
  | Georgian
  | Glagolitic
  | Gothic
  | Grantha
  | Greek
  | Gujarati
  | Gunjala_Gondi
  | Gurmukhi
  | Gurung_Khema
  | Han
  | Hangul
  | Hanifi_Rohingya
  | Hanunoo
  | Hatran
  | Hebrew
  | Hiragana
  | Imperial_Aramaic
  | Inherited
  | Inscriptional_Pahlavi
  | Inscriptional_Parthian
  | Javanese
  | Kaithi
  | Kannada
  | Katakana
  | Kawi
  | Kayah_Li
  | Kharoshthi
  | Khitan_Small_Script
  | Khmer
  | Khojki
  | Khudawadi
  | Kirat_Rai
  | Lao
  | Latin
  | Lepcha
  | Limbu
  | Linear_A
  | Linear_B
  | Lisu
  | Lycian
  | Lydian
  | Mahajani
  | Makasar
  | Malayalam
  | Mandaic
  | Manichaean
  | Marchen
  | Masaram_Gondi
  | Medefaidrin
  | Meetei_Mayek
  | Mende_Kikakui
  | Meroitic_Cursive
  | Meroitic_Hieroglyphs
  | Miao
  | Modi
  | Mongolian
  | Mro
  | Multani
  | Myanmar
  | Nabataean
  | Nag_Mundari
  | Nandinagari
  | Newa
  | New_Tai_Lue
  | Nko
  | Nushu
  | Nyiakeng_Puachue_Hmong
  | Ogham
  | Ol_Chiki
  | Old_Hungarian
  | Old_Italic
  | Old_North_Arabian
  | Old_Permic
  | Old_Persian
  | Old_Sogdian
  | Old_South_Arabian
  | Old_Turkic
  | Old_Uyghur
  | Ol_Onal
  | Oriya
  | Osage
  | Osmanya
  | Pahawh_Hmong
  | Palmyrene
  | Pau_Cin_Hau
  | Phags_Pa
  | Phoenician
  | Psalter_Pahlavi
  | Rejang
  | Runic
  | Samaritan
  | Saurashtra
  | Sharada
  | Shavian
  | Siddham
  | Sidetic
  | SignWriting
  | Sinhala
  | Sogdian
  | Sora_Sompeng
  | Soyombo
  | Sundanese
  | Sunuwar
  | Syloti_Nagri
  | Syriac
  | Tagalog
  | Tagbanwa
  | Tai_Le
  | Tai_Tham
  | Tai_Viet
  | Tai_Yo
  | Takri
  | Tamil
  | Tangsa
  | Tangut
  | Telugu
  | Thaana
  | Thai
  | Tibetan
  | Tifinagh
  | Tirhuta
  | Todhri
  | Tolong_Siki
  | Toto
  | Tulu_Tigalari
  | Ugaritic
  | Vai
  | Vithkuqi
  | Wancho
  | Warang_Citi
  | Yezidi
  | Yi
  | Zanabazar_Square
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

def parseScript? : String → Option Script
  | "Unknown" => some .Unknown
  | "Adlam" => some .Adlam
  | "Ahom" => some .Ahom
  | "Anatolian_Hieroglyphs" => some .Anatolian_Hieroglyphs
  | "Arabic" => some .Arabic
  | "Armenian" => some .Armenian
  | "Avestan" => some .Avestan
  | "Balinese" => some .Balinese
  | "Bamum" => some .Bamum
  | "Bassa_Vah" => some .Bassa_Vah
  | "Batak" => some .Batak
  | "Bengali" => some .Bengali
  | "Beria_Erfe" => some .Beria_Erfe
  | "Bhaiksuki" => some .Bhaiksuki
  | "Bopomofo" => some .Bopomofo
  | "Brahmi" => some .Brahmi
  | "Braille" => some .Braille
  | "Buginese" => some .Buginese
  | "Buhid" => some .Buhid
  | "Canadian_Aboriginal" => some .Canadian_Aboriginal
  | "Carian" => some .Carian
  | "Caucasian_Albanian" => some .Caucasian_Albanian
  | "Chakma" => some .Chakma
  | "Cham" => some .Cham
  | "Cherokee" => some .Cherokee
  | "Chorasmian" => some .Chorasmian
  | "Common" => some .Common
  | "Coptic" => some .Coptic
  | "Cuneiform" => some .Cuneiform
  | "Cypriot" => some .Cypriot
  | "Cypro_Minoan" => some .Cypro_Minoan
  | "Cyrillic" => some .Cyrillic
  | "Deseret" => some .Deseret
  | "Devanagari" => some .Devanagari
  | "Dives_Akuru" => some .Dives_Akuru
  | "Dogra" => some .Dogra
  | "Duployan" => some .Duployan
  | "Egyptian_Hieroglyphs" => some .Egyptian_Hieroglyphs
  | "Elbasan" => some .Elbasan
  | "Elymaic" => some .Elymaic
  | "Ethiopic" => some .Ethiopic
  | "Garay" => some .Garay
  | "Georgian" => some .Georgian
  | "Glagolitic" => some .Glagolitic
  | "Gothic" => some .Gothic
  | "Grantha" => some .Grantha
  | "Greek" => some .Greek
  | "Gujarati" => some .Gujarati
  | "Gunjala_Gondi" => some .Gunjala_Gondi
  | "Gurmukhi" => some .Gurmukhi
  | "Gurung_Khema" => some .Gurung_Khema
  | "Han" => some .Han
  | "Hangul" => some .Hangul
  | "Hanifi_Rohingya" => some .Hanifi_Rohingya
  | "Hanunoo" => some .Hanunoo
  | "Hatran" => some .Hatran
  | "Hebrew" => some .Hebrew
  | "Hiragana" => some .Hiragana
  | "Imperial_Aramaic" => some .Imperial_Aramaic
  | "Inherited" => some .Inherited
  | "Inscriptional_Pahlavi" => some .Inscriptional_Pahlavi
  | "Inscriptional_Parthian" => some .Inscriptional_Parthian
  | "Javanese" => some .Javanese
  | "Kaithi" => some .Kaithi
  | "Kannada" => some .Kannada
  | "Katakana" => some .Katakana
  | "Kawi" => some .Kawi
  | "Kayah_Li" => some .Kayah_Li
  | "Kharoshthi" => some .Kharoshthi
  | "Khitan_Small_Script" => some .Khitan_Small_Script
  | "Khmer" => some .Khmer
  | "Khojki" => some .Khojki
  | "Khudawadi" => some .Khudawadi
  | "Kirat_Rai" => some .Kirat_Rai
  | "Lao" => some .Lao
  | "Latin" => some .Latin
  | "Lepcha" => some .Lepcha
  | "Limbu" => some .Limbu
  | "Linear_A" => some .Linear_A
  | "Linear_B" => some .Linear_B
  | "Lisu" => some .Lisu
  | "Lycian" => some .Lycian
  | "Lydian" => some .Lydian
  | "Mahajani" => some .Mahajani
  | "Makasar" => some .Makasar
  | "Malayalam" => some .Malayalam
  | "Mandaic" => some .Mandaic
  | "Manichaean" => some .Manichaean
  | "Marchen" => some .Marchen
  | "Masaram_Gondi" => some .Masaram_Gondi
  | "Medefaidrin" => some .Medefaidrin
  | "Meetei_Mayek" => some .Meetei_Mayek
  | "Mende_Kikakui" => some .Mende_Kikakui
  | "Meroitic_Cursive" => some .Meroitic_Cursive
  | "Meroitic_Hieroglyphs" => some .Meroitic_Hieroglyphs
  | "Miao" => some .Miao
  | "Modi" => some .Modi
  | "Mongolian" => some .Mongolian
  | "Mro" => some .Mro
  | "Multani" => some .Multani
  | "Myanmar" => some .Myanmar
  | "Nabataean" => some .Nabataean
  | "Nag_Mundari" => some .Nag_Mundari
  | "Nandinagari" => some .Nandinagari
  | "Newa" => some .Newa
  | "New_Tai_Lue" => some .New_Tai_Lue
  | "Nko" => some .Nko
  | "Nushu" => some .Nushu
  | "Nyiakeng_Puachue_Hmong" => some .Nyiakeng_Puachue_Hmong
  | "Ogham" => some .Ogham
  | "Ol_Chiki" => some .Ol_Chiki
  | "Old_Hungarian" => some .Old_Hungarian
  | "Old_Italic" => some .Old_Italic
  | "Old_North_Arabian" => some .Old_North_Arabian
  | "Old_Permic" => some .Old_Permic
  | "Old_Persian" => some .Old_Persian
  | "Old_Sogdian" => some .Old_Sogdian
  | "Old_South_Arabian" => some .Old_South_Arabian
  | "Old_Turkic" => some .Old_Turkic
  | "Old_Uyghur" => some .Old_Uyghur
  | "Ol_Onal" => some .Ol_Onal
  | "Oriya" => some .Oriya
  | "Osage" => some .Osage
  | "Osmanya" => some .Osmanya
  | "Pahawh_Hmong" => some .Pahawh_Hmong
  | "Palmyrene" => some .Palmyrene
  | "Pau_Cin_Hau" => some .Pau_Cin_Hau
  | "Phags_Pa" => some .Phags_Pa
  | "Phoenician" => some .Phoenician
  | "Psalter_Pahlavi" => some .Psalter_Pahlavi
  | "Rejang" => some .Rejang
  | "Runic" => some .Runic
  | "Samaritan" => some .Samaritan
  | "Saurashtra" => some .Saurashtra
  | "Sharada" => some .Sharada
  | "Shavian" => some .Shavian
  | "Siddham" => some .Siddham
  | "Sidetic" => some .Sidetic
  | "SignWriting" => some .SignWriting
  | "Sinhala" => some .Sinhala
  | "Sogdian" => some .Sogdian
  | "Sora_Sompeng" => some .Sora_Sompeng
  | "Soyombo" => some .Soyombo
  | "Sundanese" => some .Sundanese
  | "Sunuwar" => some .Sunuwar
  | "Syloti_Nagri" => some .Syloti_Nagri
  | "Syriac" => some .Syriac
  | "Tagalog" => some .Tagalog
  | "Tagbanwa" => some .Tagbanwa
  | "Tai_Le" => some .Tai_Le
  | "Tai_Tham" => some .Tai_Tham
  | "Tai_Viet" => some .Tai_Viet
  | "Tai_Yo" => some .Tai_Yo
  | "Takri" => some .Takri
  | "Tamil" => some .Tamil
  | "Tangsa" => some .Tangsa
  | "Tangut" => some .Tangut
  | "Telugu" => some .Telugu
  | "Thaana" => some .Thaana
  | "Thai" => some .Thai
  | "Tibetan" => some .Tibetan
  | "Tifinagh" => some .Tifinagh
  | "Tirhuta" => some .Tirhuta
  | "Todhri" => some .Todhri
  | "Tolong_Siki" => some .Tolong_Siki
  | "Toto" => some .Toto
  | "Tulu_Tigalari" => some .Tulu_Tigalari
  | "Ugaritic" => some .Ugaritic
  | "Vai" => some .Vai
  | "Vithkuqi" => some .Vithkuqi
  | "Wancho" => some .Wancho
  | "Warang_Citi" => some .Warang_Citi
  | "Yezidi" => some .Yezidi
  | "Yi" => some .Yi
  | "Zanabazar_Square" => some .Zanabazar_Square
  | unknownScriptName => Function.const String none unknownScriptName

/-- Parse one Scripts.txt row. Returns `none` for blank/comment lines
    or rows whose script name is not in the enum. -/
def parseScriptRow (rawLine : String) : Option (Nat × Nat × Script) :=
  let stripped : String := (rawLine.takeWhile (· != '#')).toString
  let line := trimS stripped
  if line.isEmpty then none else
  match String.splitOn line ";" with
  | [rngField, scriptField] =>
    let (lo, hi) := parseRange (trimS rngField)
    match parseScript? (trimS scriptField) with
    | some s => some (lo, hi, s)
    | none   => none
  | irregularSplit => Function.const (List String) none irregularSplit

/-- Raw text of `Scripts.txt`, embedded at compile time. -/
def scriptsRaw : String := include_str "../Ucd/Scripts.txt"

/-- Range table mapping codepoint ranges to their Script property value
    from Scripts.txt. Inclusive on both ends. -/
def scriptRanges : Array (Nat × Nat × Script) :=
  ((scriptsRaw.splitOn "\n").filterMap parseScriptRow).toArray

/-- `@missing 0000..10FFFF; Unknown` — the default Script value for
    codepoints not covered by `scriptRanges`. -/
def defaultScript : Script := .Unknown

end Unicode.Generated.Scripts
