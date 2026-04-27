/-
  Unicode

  Root import for the Unicode standard's machine-checked specifications,
  pinned at UCD 17.0.0 and Lean 4.28.0.
-/

-- Normalization (UAX #15)
import Unicode.Normalization.QuickCheckSoundnessTheorem
import Unicode.Normalization.NFKC
import Unicode.Normalization.NFKD
import Unicode.Normalization.CompatDecompose

-- PRECIS (RFC 8264 / 8265)
import Unicode.Precis.Preparation
import Unicode.Precis.IdentifierClass
import Unicode.Precis.OpaqueString
import Unicode.Precis.BidiRule
import Unicode.Precis.Categories
import Unicode.Precis.WidthMapping
import Unicode.Precis.CaseMapping
import Unicode.Precis.ZsPreservation

-- Bidirectional Algorithm (UAX #9)
import Unicode.Bidi.Algorithm

-- Confusables (UTS #39 §4)
import Unicode.Confusables

-- UAX #15 conformance — official NormalizationTest.txt against
-- toNFC / toNFD / toNFKC / toNFKD across all six @Part sections
import Unicode.Conformance.NormalizationTest

-- Case-fold commutation and round-trip
import Unicode.CaseFoldCommutation
import Unicode.CaseFoldRoundtrip

-- Refinement-typed wrappers and invariants
import Unicode.Refined
import Unicode.Invariants

-- Generated UCD-derived tables (UCD 17.0.0)
import Unicode.Generated.CompatDecomp
import Unicode.Generated.DerivedCoreProperties
import Unicode.Generated.EastAsianWidth
import Unicode.Generated.IdentifierType
import Unicode.Generated.IdnaMapping
import Unicode.Generated.PropList
import Unicode.Generated.ScriptExtensions
import Unicode.Generated.Scripts
