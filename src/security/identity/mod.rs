//! Identity-spoofing detector family.
//!
//! Detectors for codepoints and sequences that pose as legitimate
//! identifiers — UTS #39 §4 confusable / homoglyph attacks,
//! Mathematical Alphanumeric Symbols posing as Latin, fullwidth
//! Latin variants, NFC-form drift, cross-script mixing, and
//! UTS #39 restriction-level breaches.

pub mod homoglyph_confusable;
pub mod ucd;
