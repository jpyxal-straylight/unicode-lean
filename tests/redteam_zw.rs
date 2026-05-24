//! Brutal red-team — ZeroWidthPayload detector.
//!
//! The current `is_zero_width` predicate hardcodes ~15 codepoints:
//!
//!     0x200B..=0x200F | 0x2060..=0x2064 | 0x202F | 0xFEFF
//!     | 0xFFF9..=0xFFFB
//!
//! UAX #44 Default_Ignorable_Code_Point covers ~four dozen
//! visually-invisible codepoints beyond that.  This test
//! enumerates the gap codepoints and asserts the detector
//! catches them.  Any miss is a real hole — an attacker
//! can splice the invisible codepoint into an identifier
//! and the ZeroWidthPayload detector won't see it.

use unicode_rust::security::ClassificationKind;
use unicode_rust::security::covert::zero_width_payload as zw;
use unicode_rust::security::identity::ucd;

// All Default_Ignorable_Code_Point ranges per UAX #44, MINUS the
// ranges that are explicitly handled by OTHER detectors:
//   - U+FE00..U+FE0F (VS1..VS16)         — VariationSelectorPayload
//   - U+E0100..U+E01EF (VS17..VS256)     — VariationSelectorPayload
//   - U+E0000..U+E007F (Tag block)       — TagBlockPayload
// Bidi controls in this set (U+202A..E, U+2066..U+2069) ARE invisible
// AND not bidi formatting in the LR sense — they ARE bidi but we
// expect both ZW and Bidi to flag them.
//
// The candidates below are codepoints that ARE invisible /
// default-ignorable but NEITHER caught by ZW today NOR claimed by
// a sibling detector.  Each should fire ZeroWidthPayload but
// currently doesn't.
const INVISIBLE_BUT_NOT_DETECTED: &[(u32, &str)] = &[
    (0x00AD, "SOFT HYPHEN"),
    (0x034F, "COMBINING GRAPHEME JOINER"),
    (0x061C, "ARABIC LETTER MARK"),
    (0x115F, "HANGUL CHOSEONG FILLER"),
    (0x1160, "HANGUL JUNGSEONG FILLER"),
    (0x17B4, "KHMER VOWEL INHERENT AQ"),
    (0x17B5, "KHMER VOWEL INHERENT AA"),
    (0x180B, "MONGOLIAN FREE VARIATION SELECTOR ONE"),
    (0x180C, "MONGOLIAN FREE VARIATION SELECTOR TWO"),
    (0x180D, "MONGOLIAN FREE VARIATION SELECTOR THREE"),
    (0x180E, "MONGOLIAN VOWEL SEPARATOR"),
    (0x180F, "MONGOLIAN FREE VARIATION SELECTOR FOUR"),
    (0x2065, "<reserved> (default-ignorable)"),
    (0x206A, "INHIBIT SYMMETRIC SWAPPING"),
    (0x206B, "ACTIVATE SYMMETRIC SWAPPING"),
    (0x206C, "INHIBIT ARABIC FORM SHAPING"),
    (0x206D, "ACTIVATE ARABIC FORM SHAPING"),
    (0x206E, "NATIONAL DIGIT SHAPES"),
    (0x206F, "NOMINAL DIGIT SHAPES"),
    (0x3164, "HANGUL FILLER"),
    (0xFFA0, "HALFWIDTH HANGUL FILLER"),
    (0xFFF0, "<reserved> (default-ignorable)"),
    (0xFFF8, "<reserved> (default-ignorable)"),
    (0x1BCA0, "SHORTHAND FORMAT LETTER OVERLAP"),
    (0x1BCA1, "SHORTHAND FORMAT CONTINUING OVERLAP"),
    (0x1BCA2, "SHORTHAND FORMAT DOWN STEP"),
    (0x1BCA3, "SHORTHAND FORMAT UP STEP"),
    (0x1D173, "MUSICAL SYMBOL BEGIN BEAM"),
    (0x1D17A, "MUSICAL SYMBOL END PHRASE"),
];

#[test]
fn zw_bypass_via_unhandled_invisibles() {
    let mut breaks = Vec::new();
    let mut caught = 0;
    let mut also_default_ignorable = 0;
    for (cp, name) in INVISIBLE_BUT_NOT_DETECTED {
        // Confirm Unicode considers this default-ignorable
        // (sanity-check against our test list).
        let is_di = ucd::is_default_ignorable(*cp);
        if is_di {
            also_default_ignorable += 1;
        }
        // Splice the invisible into a normal identifier
        let input = [0x61u32, *cp, 0x62];
        let v = zw::detect(&input);
        let tag = v.sub.as_ref().map(|s| s.tag());
        if v.kind == ClassificationKind::Hazard {
            caught += 1;
            eprintln!(
                "  U+{:04X} {}: caught (sub={:?})",
                cp, name, tag,
            );
        } else {
            breaks.push(format!(
                "U+{:04X} {} (is_default_ignorable={}): {:?}",
                cp, name, is_di, v.kind,
            ));
        }
    }
    eprintln!(
        "ZW BYPASS: {}/{} caught, {} are also Default_Ignorable per UCD",
        caught,
        INVISIBLE_BUT_NOT_DETECTED.len(),
        also_default_ignorable,
    );
    if !breaks.is_empty() {
        eprintln!("ZW MISSES:");
        for b in &breaks {
            eprintln!("  {}", b);
        }
        panic!(
            "ZeroWidthPayload missed {} invisible-codepoint insertions",
            breaks.len(),
        );
    }
}
