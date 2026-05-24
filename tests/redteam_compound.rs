//! Systematic compound-attack sweep — Move 5 of state-level
//! red-team plan.  Every unordered pair of the 5 active detectors
//! (TagBlockPayload, VariationSelectorPayload, ZeroWidthPayload,
//! BidiControlBalance, HomoglyphConfusable) is exercised with a
//! single input that triggers BOTH families.  Each detector must
//! fire independently on the compound input; aggregator-side
//! priority dispatch is verified by the existing RunAll machinery
//! (Lean-side; rust-port aggregator forthcoming).
//!
//! The point: attacks in the wild are rarely single-class.  A
//! GoodSide-style LLM prompt-injection may carry a TagBlock
//! payload AND a ZW disguise AND a TargetMatch typosquat in the
//! visible portion.  If one detector masks another's input, the
//! attack class is missed.  This file proves no such masking
//! occurs.

use unicode_rust::security::ClassificationKind;
use unicode_rust::security::covert::{
    bidi_control_balance as bidi,
    tag_block_payload as tag,
    variation_selector_payload as vs,
    zero_width_payload as zw,
};
use unicode_rust::security::identity::homoglyph_confusable as h;

// Helper: assert ALL of the listed detectors fire Hazard on the
// given input.  Reports which ones missed so debugging is easy.
fn assert_all_fire(input: &[u32], detectors: &[(&str, bool)]) {
    let mut misses: Vec<&str> = Vec::new();
    for (name, fired) in detectors {
        if !*fired {
            misses.push(*name);
        }
    }
    if !misses.is_empty() {
        eprintln!("COMPOUND BREAK on input {:X?}", input);
        eprintln!("  detectors that DIDN'T fire: {:?}", misses);
        panic!("compound input must fire all participating detectors");
    }
}

// ════════════════════════════════════════════════════════════════════
// Pair 1 / 10 — TagBlock + VariationSelector
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_tag_plus_vs() {
    // CJK base + VS payload, followed by tag-block payload.
    let input = [
        0x4E00, 0xFE04, 0xFE01,        // CJK + VS pair → VS DirectPayload
        0xE0041, 0xE0042,              // Tag block AB → Tag DirectAscii
    ];
    let v_tag = tag::detect(&input);
    let v_vs = vs::detect(&input);
    assert_all_fire(&input, &[
        ("Tag",  v_tag.kind == ClassificationKind::Hazard),
        ("VS",   v_vs.kind  == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Pair 2 / 10 — TagBlock + ZeroWidth
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_tag_plus_zw() {
    let input = [
        0xE0041, 0xE0042,              // Tag block AB
        0x200B,                        // ZWSP
    ];
    let v_tag = tag::detect(&input);
    let v_zw = zw::detect(&input);
    assert_all_fire(&input, &[
        ("Tag", v_tag.kind == ClassificationKind::Hazard),
        ("ZW",  v_zw.kind  == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Pair 3 / 10 — TagBlock + BidiControlBalance
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_tag_plus_bidi() {
    let input = [
        0xE0041, 0xE0042,              // Tag block AB
        0x202E,                        // RLO (unbalanced)
    ];
    let v_tag = tag::detect(&input);
    let v_bidi = bidi::detect(&input);
    assert_all_fire(&input, &[
        ("Tag",  v_tag.kind  == ClassificationKind::Hazard),
        ("Bidi", v_bidi.kind == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Pair 4 / 10 — TagBlock + Homoglyph
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_tag_plus_homoglyph() {
    // "Nethereum" + Cyrillic-е typosquat + invisible tag-block
    // payload after.
    let mut input: Vec<u32> = vec![
        0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D,
    ];
    // Append tag-block payload "pwn" hidden after the visible name.
    input.push(0xE0070);
    input.push(0xE0077);
    input.push(0xE006E);
    let v_tag = tag::detect(&input);
    let v_h = h::detect(&input);
    assert_all_fire(&input, &[
        ("Tag",       v_tag.kind == ClassificationKind::Hazard),
        ("Homoglyph", v_h.kind   == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Pair 5 / 10 — VariationSelector + ZeroWidth
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_vs_plus_zw() {
    let input = [
        0x4E00, 0xFE04, 0xFE01,        // CJK + VS DirectPayload
        0x200B,                        // ZWSP
    ];
    let v_vs = vs::detect(&input);
    let v_zw = zw::detect(&input);
    assert_all_fire(&input, &[
        ("VS", v_vs.kind == ClassificationKind::Hazard),
        ("ZW", v_zw.kind == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Pair 6 / 10 — VariationSelector + BidiControlBalance
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_vs_plus_bidi() {
    let input = [
        0x4E00, 0xFE04, 0xFE01,        // CJK + VS DirectPayload
        0x202E,                        // RLO (unbalanced)
    ];
    let v_vs = vs::detect(&input);
    let v_bidi = bidi::detect(&input);
    assert_all_fire(&input, &[
        ("VS",   v_vs.kind   == ClassificationKind::Hazard),
        ("Bidi", v_bidi.kind == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Pair 7 / 10 — VariationSelector + Homoglyph
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_vs_plus_homoglyph() {
    // Nethereum typosquat + a trailing CJK base with VS payload.
    let input = [
        0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D,
        0x4E00, 0xFE04, 0xFE01,
    ];
    let v_vs = vs::detect(&input);
    let v_h = h::detect(&input);
    assert_all_fire(&input, &[
        ("VS",        v_vs.kind == ClassificationKind::Hazard),
        ("Homoglyph", v_h.kind  == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Pair 8 / 10 — ZeroWidth + BidiControlBalance
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_zw_plus_bidi() {
    let input = [0x200B, 0x202E];      // ZWSP + lone RLO
    let v_zw = zw::detect(&input);
    let v_bidi = bidi::detect(&input);
    assert_all_fire(&input, &[
        ("ZW",   v_zw.kind   == ClassificationKind::Hazard),
        ("Bidi", v_bidi.kind == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Pair 9 / 10 — ZeroWidth + Homoglyph
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_zw_plus_homoglyph() {
    // Nethereum + Cyrillic-е + a ZWSP injected mid-string.
    let input = [
        0x4E, 0x65, 0x74, 0x200B, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D,
    ];
    let v_zw = zw::detect(&input);
    let v_h = h::detect(&input);
    assert_all_fire(&input, &[
        ("ZW",        v_zw.kind == ClassificationKind::Hazard),
        ("Homoglyph", v_h.kind  == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Pair 10 / 10 — Bidi + Homoglyph
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_bidi_plus_homoglyph() {
    // Nethereum + Cyrillic-е wrapped in RLO/PDF (Bidi-balanced
    // would let Bidi pass Clear — use a LONE RLO to force Bidi
    // hazard fire on the unbalanced control).
    let input = [
        0x202E,
        0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D,
    ];
    let v_bidi = bidi::detect(&input);
    let v_h = h::detect(&input);
    assert_all_fire(&input, &[
        ("Bidi",      v_bidi.kind == ClassificationKind::Hazard),
        ("Homoglyph", v_h.kind    == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Triple combinations (sample) — TagBlock + ZW + Homoglyph
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_tag_plus_zw_plus_homoglyph() {
    let input = [
        0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D,
        0x200B,                            // ZWSP
        0xE0070, 0xE0077, 0xE006E,         // Tag block "pwn"
    ];
    let v_tag = tag::detect(&input);
    let v_zw = zw::detect(&input);
    let v_h = h::detect(&input);
    assert_all_fire(&input, &[
        ("Tag",       v_tag.kind == ClassificationKind::Hazard),
        ("ZW",        v_zw.kind  == ClassificationKind::Hazard),
        ("Homoglyph", v_h.kind   == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Quadruple — TagBlock + VS + ZW + Bidi (most realistic LLM-attack shape)
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_tag_vs_zw_bidi_full_stack() {
    let input = [
        0x4E00, 0xFE04, 0xFE01,            // CJK + VS payload
        0x200B,                            // ZWSP
        0x202E,                            // lone RLO
        0xE0041, 0xE0042,                  // Tag block AB
    ];
    let v_tag = tag::detect(&input);
    let v_vs = vs::detect(&input);
    let v_zw = zw::detect(&input);
    let v_bidi = bidi::detect(&input);
    assert_all_fire(&input, &[
        ("Tag",  v_tag.kind  == ClassificationKind::Hazard),
        ("VS",   v_vs.kind   == ClassificationKind::Hazard),
        ("ZW",   v_zw.kind   == ClassificationKind::Hazard),
        ("Bidi", v_bidi.kind == ClassificationKind::Hazard),
    ]);
}

// ════════════════════════════════════════════════════════════════════
// Quintuple — all 5 detectors fire (every-class compound)
// ════════════════════════════════════════════════════════════════════

#[test]
fn compound_all_five_detectors_fire() {
    let input = [
        // HomoglyphConfusable: Nethereum + Cyrillic-е
        0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D,
        // VariationSelectorPayload: CJK + VS payload
        0x4E00, 0xFE04, 0xFE01,
        // ZeroWidthPayload: ZWSP
        0x200B,
        // BidiControlBalance: lone RLO
        0x202E,
        // TagBlockPayload: tag chars
        0xE0041, 0xE0042,
    ];
    let v_tag = tag::detect(&input);
    let v_vs = vs::detect(&input);
    let v_zw = zw::detect(&input);
    let v_bidi = bidi::detect(&input);
    let v_h = h::detect(&input);
    assert_all_fire(&input, &[
        ("Tag",       v_tag.kind  == ClassificationKind::Hazard),
        ("VS",        v_vs.kind   == ClassificationKind::Hazard),
        ("ZW",        v_zw.kind   == ClassificationKind::Hazard),
        ("Bidi",      v_bidi.kind == ClassificationKind::Hazard),
        ("Homoglyph", v_h.kind    == ClassificationKind::Hazard),
    ]);
}
