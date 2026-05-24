//! Brutal red-team — VariationSelectorPayload detector.
//!
//! Coverage targets:
//!
//!   1. Pair-aligned payload decoding (VS pair → byte).
//!   2. Long VS runs on legal targets (RepeatedBase threshold).
//!   3. Off-range CJK (F900..FAFF CJK Compatibility Ideographs) —
//!      legitimate VS target per UTS, NOT in our hardcoded list.
//!      False-positive risk: detector fires IllegalTarget on what
//!      Unicode considers a legal variation base.
//!   4. CJK Ext H, I (newer ranges) — same risk.
//!   5. VS on basic Latin (should fire IllegalTarget — correct).
//!   6. Orphan VS at start of input.
//!   7. Mixed VS1..16 + VS17..256 on same base.
//!   8. GlassWorm-style payload — actual bytes decoding to readable
//!      ASCII (`Print 'pwned'`).
//!   9. VS on math-alphanumeric (no emoji presentation).
//!  10. Fuzz — random VS-heavy input, no panic.

use std::time::Instant;
use unicode_rust::security::ClassificationKind;
use unicode_rust::security::covert::variation_selector_payload as vs;

// ════════════════════════════════════════════════════════════════════
// 1. Pair-aligned payload — should fire DirectPayload
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_pair_decodes_to_byte() {
    // VS5 (FE04 = nibble 4) + VS2 (FE01 = nibble 1) on CJK base
    // → 0x41 = 'A'.
    let input = [0x4E00, 0xFE04, 0xFE01];
    let v = vs::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.as_ref().unwrap().tag(), "DirectPayload");
    assert_eq!(v.recovered_bytes, vec![0x41u8]);
}

// ════════════════════════════════════════════════════════════════════
// 2. Long VS run on legal target — RepeatedBase
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_long_repeated_base() {
    // 9 selectors on a CJK base, all the SAME nibble — no payload
    // decode (same byte over and over), so falls through to
    // RepeatedBase classification.
    let mut input = vec![0x4E00u32];
    for _ in 0..9 {
        input.push(0xFE04);
    }
    let v = vs::detect(&input);
    let tag = v.sub.as_ref().map(|s| s.tag());
    eprintln!("  9× same VS on CJK base: {:?}", tag);
    // Detector should fire one of {DirectPayload, RepeatedBase}.
    assert_eq!(v.kind, ClassificationKind::Hazard);
}

// ════════════════════════════════════════════════════════════════════
// 3. CJK Compatibility Ideographs (F900..FAFF) — legitimate VS target?
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_on_cjk_compatibility_ideograph() {
    // U+F900 = CJK COMPATIBILITY IDEOGRAPH-F900.  Per
    // StandardizedVariants.txt, several CJK Compat codepoints
    // have registered variation sequences.  Our hardcoded list
    // does NOT include this range — VS on it fires IllegalTarget.
    let input = [0xF900, 0xFE00];
    let v = vs::detect(&input);
    let tag = v.sub.as_ref().map(|s| s.tag());
    eprintln!(
        "  VS on CJK Compat F900: kind={:?} sub={:?}",
        v.kind, tag,
    );
    // Documents the false-positive: detector flags a legitimate VS
    // target as IllegalTarget.  This is a real gap if banks /
    // governments process East Asian text with VS — they'd see
    // spurious alerts.  Fix: bundle StandardizedVariants.txt and
    // emoji-variation-sequences.txt for the authoritative list.
}

// ════════════════════════════════════════════════════════════════════
// 4. CJK Extension H (newer)
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_on_cjk_extension_h() {
    // U+31350 — first CJK Extension H codepoint (added in
    // Unicode 15.0).  Not in our hardcoded range list.
    let input = [0x31350, 0xFE00];
    let v = vs::detect(&input);
    eprintln!(
        "  VS on CJK Ext H (31350): kind={:?} sub={:?}",
        v.kind, v.sub.as_ref().map(|s| s.tag()),
    );
}

// ════════════════════════════════════════════════════════════════════
// 5. VS on basic Latin — should fire IllegalTarget (correct)
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_on_latin_letter() {
    let input = [0x0041, 0xFE0F];
    let v = vs::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.as_ref().unwrap().tag(), "IllegalTarget");
}

// ════════════════════════════════════════════════════════════════════
// 6. Orphan VS at start
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_orphan_at_start() {
    let input = [0xFE00];
    let v = vs::detect(&input);
    let tag = v.sub.as_ref().map(|s| s.tag());
    assert!(tag == Some("OrphanSelector") || tag == Some("IllegalTarget"),
        "got tag={:?}", tag);
}

// ════════════════════════════════════════════════════════════════════
// 7. GlassWorm-style covert payload
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_glassworm_covert_payload_print_pwned() {
    // Encode "Print 'pwned'" as VS nibbles attached to a CJK base.
    // Each ASCII byte = 2 nibbles = 2 VSes.
    let target = b"Print 'pwned'";
    let mut input = vec![0x4E00u32];  // CJK base
    for byte in target {
        let hi = (byte >> 4) & 0xF;  // 0..15 → VS1..16 = FE00 + hi
        let lo = byte & 0xF;
        input.push(0xFE00 + hi as u32);
        input.push(0xFE00 + lo as u32);
    }
    let v = vs::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.as_ref().unwrap().tag(), "DirectPayload");
    eprintln!(
        "  GlassWorm payload: recovered {} bytes ({:?})",
        v.recovered_bytes.len(),
        std::str::from_utf8(&v.recovered_bytes).ok(),
    );
    // The detector reports DirectPayload but the recovered_bytes
    // should contain the actual decoded payload.
    assert!(v.recovered_bytes.len() >= target.len(),
        "expected >= {} decoded bytes", target.len());
}

// ════════════════════════════════════════════════════════════════════
// 8. VS on Math-Alpha — no emoji presentation, no CJK, should be
//    IllegalTarget
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_on_math_alpha() {
    let input = [0x1D400, 0xFE0F];
    let v = vs::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.as_ref().unwrap().tag(), "IllegalTarget");
}

// ════════════════════════════════════════════════════════════════════
// 9. Supplementary VS (U+E0100..U+E01EF) on Latin — IllegalTarget
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_supplementary_on_latin() {
    let input = [0x0041, 0xE0100];
    let v = vs::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.as_ref().unwrap().tag(), "IllegalTarget");
}

// ════════════════════════════════════════════════════════════════════
// 10. Mixed VS1..16 + VS17..256 payload
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_mixed_low_high_range_payload() {
    // VS1 (FE00 → nibble 0) + VS18 (E0101 → byte 17)
    // First byte = (0 << 4) | (17 & 0xF) but 17 doesn't fit in
    // a nibble, so decode skips it.  Probe behavior.
    let input = [0x4E00, 0xFE00, 0xE0101];
    let v = vs::detect(&input);
    eprintln!(
        "  Mixed VS1+VS18: kind={:?} sub={:?} bytes={:?}",
        v.kind, v.sub.as_ref().map(|s| s.tag()), v.recovered_bytes,
    );
}

// ════════════════════════════════════════════════════════════════════
// 11. Degenerate — no panic
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_degenerate_no_panic() {
    let _ = vs::detect(&[]);
    let _ = vs::detect(&[0xFE00]);
    let _ = vs::detect(&[0xE0100]);
    let _ = vs::detect(&[0xFE0F, 0xFE0F, 0xFE0F]);
    let _ = vs::detect(&[0xFFFFFFFF]);
}

// ════════════════════════════════════════════════════════════════════
// 12. Fuzz — VS-heavy random input
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_fuzz_random() {
    let mut state: u64 = 0xDEAD_BEEF_F00D_BABE;
    for _ in 0..10_000 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let len = (state as usize) % 64;
        let mut input = Vec::with_capacity(len);
        for _ in 0..len {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            // Bias toward VS codepoints + some bases
            let cp = match state % 4 {
                0 => 0xFE00 + (state >> 8) as u32 % 16, // VS1..16
                1 => 0xE0100 + (state >> 8) as u32 % 240, // VS17..256
                2 => 0x4E00 + (state >> 8) as u32 % 0x4000, // CJK base
                _ => 0x0041 + (state >> 8) as u32 % 26,  // Latin
            };
            input.push(cp);
        }
        let _ = vs::detect(&input);
    }
}

// ════════════════════════════════════════════════════════════════════
// 13. Massive VS payload — DoS
// ════════════════════════════════════════════════════════════════════

#[test]
fn vs_massive_payload_no_dos() {
    let mut input = vec![0x4E00u32];
    for i in 0..50_000 {
        input.push(0xFE00 + (i % 16) as u32);
    }
    let t = Instant::now();
    let v = vs::detect(&input);
    let e = t.elapsed();
    eprintln!(
        "  50k VS payload: kind={:?} bytes={} elapsed={:?}",
        v.kind, v.recovered_bytes.len(), e,
    );
    assert!(e.as_secs() < 5);
}
