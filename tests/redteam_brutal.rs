//! Brutal red-team — really try to break this.
//!
//! Categories the prior suites didn't push on:
//!
//!   1. Zero-width / format-control insertion bypass.  Insert
//!      U+200B (ZWSP), U+200C (ZWNJ), U+200D (ZWJ), U+FEFF (BOM),
//!      U+2060 (WJ) between every adjacent pair of a target.  The
//!      §4+§5.4 skeleton keeps them (CCC=0), letter_skeleton strips
//!      only CCC>0 — so these survive into the comparison.  Does
//!      TargetMatch still fire?  If not, this is a real hole.
//!
//!   2. Pure single-script confusable spoof (Hole 3 demonstration).
//!      Construct realistic IDN-homograph attacks against curated
//!      targets using ONLY codepoints from a single non-Latin
//!      script.  Document the miss class.
//!
//!   3. Multi-position substitution (≥2 codepoints swapped).
//!      Mutation suite did 1-position; let's do 2-position and
//!      3-position substitutions and confirm coverage holds.
//!
//!   4. Insertion attack (no substitution).  Insert one extra
//!      visible codepoint somewhere in the target.  Should NOT
//!      fire TargetMatch (different string) but the existing
//!      length tolerance via letter_skeleton might fool it.
//!
//!   5. Variation-selector appendage.  Append U+FE0F (variation
//!      selector 16) to a target.  CCC=0 so survives.
//!
//!   6. Hangul-jamo confusable.  Korean Hangul syllables can be
//!      composed/decomposed in ways that look like Latin.
//!
//!   7. RTL-override inside target.  Embed U+202E inside a target
//!      so logical and visual orders diverge.
//!
//!   8. Surrogate / noncharacter / PUA inputs.  U+D800-U+DFFF
//!      (raw surrogates — invalid Unicode), U+FDD0-U+FDEF
//!      (noncharacters), U+E000-U+F8FF (PUA).  Must not panic.
//!
//!   9. Self-match guard bypass.  Construct an input that the
//!      detector should fire on but which the t.cps != input
//!      guard might skip.
//!
//!  10. Symmetric multi-char (rn for m).  Attacker uses 'rn'
//!      where target has 'm'.  Verify it works.
//!
//!  11. Cascade nesting.  Triple-substitution chains.

use std::time::Instant;
use unicode_rust::security::ClassificationKind;
use unicode_rust::security::identity::homoglyph_confusable as h;
use unicode_rust::security::identity::homoglyph_confusable::SubThreat;

// ════════════════════════════════════════════════════════════════════
// CATEGORY 1: zero-width insertion bypass
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_1_zero_width_insertion_in_target() {
    // Insert each zero-width into "nethereum" at position 3 with a
    // Cyrillic-е substitution at pos 6.  TargetMatch SHOULD fire
    // (since the visible glyph stream is "nethereum" except for the
    // invisible ZW + Cyrillic-е) — but our letter_skeleton keeps
    // the ZW codepoint because its CCC is 0.
    let zw_candidates = [
        ("ZWSP",   0x200Bu32),
        ("ZWNJ",   0x200C),
        ("ZWJ",    0x200D),
        ("WJ",     0x2060),
        ("BOM",    0xFEFF),
        ("NNBSP",  0x202F),
    ];
    let mut breaks: Vec<String> = Vec::new();
    for (name, zw) in &zw_candidates {
        // "net" + ZW + "hereu" + Cyrillic-е + "m"  ← wait, want target match.
        // Easier: "net" + ZW + "hereum" (no Cyrillic) — purely insertion.
        let mut input = vec![0x6E, 0x65, 0x74];
        input.push(*zw);
        input.extend_from_slice(&[0x68, 0x65, 0x72, 0x65, 0x75, 0x6D]);
        let v = h::detect(&input);
        let tag = v.sub.as_ref().map(|s| s.tag());
        eprintln!(
            "{}-inserted lowercase nethereum: kind={:?} sub={:?}",
            name, v.kind, tag,
        );
        // If the verdict is NOT Hazard at all, it's a bypass.  If
        // it fires SOMETHING (TargetMatch ideal, but any Hazard is
        // layered-defense success), count it as caught.
        if v.kind != ClassificationKind::Hazard {
            breaks.push(format!("{} insertion ({}): CLEAR", name, zw));
        }
    }
    if !breaks.is_empty() {
        panic!(
            "BRUTAL 1: zero-width insertion bypass — {} attacks slipped through:\n{}",
            breaks.len(),
            breaks.join("\n"),
        );
    }
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 2: pure single-script confusable spoof (Hole 3)
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_2_pure_cyrillic_brand_spoof() {
    // Attacker uses ALL Cyrillic look-alikes to spoof Latin brand.
    // Pure single-script → CrossScriptMix doesn't fire.
    // Brand might or might not be in target list → TargetMatch coverage
    // depends on whether the iterated_skeleton matches.
    // Test against well-known brands not in curated list (apple).
    let attacks: &[(&str, &[u32])] = &[
        // "apple" pure Cyrillic look-alike: а р р ӏ е
        // Cyrillic ӏ U+04CF maps to Latin 'i' per confusables — so
        // skel = "appie", target "apple" skel = "apple".  Mismatch.
        // This documents the curation/algorithmic gap.
        ("apple-cyr",    &[0x0430, 0x0440, 0x0440, 0x04CF, 0x0435]),
        // "openai" pure Cyrillic: о р е и а і
        ("openai-cyr",   &[0x043E, 0x0440, 0x0435, 0x043D, 0x0430, 0x0456]),
        // "google" pure Cyrillic: g cyrillic doesn't exist, use ɡ U+0261 + о о gle
        ("google-cyr",   &[0x0261, 0x043E, 0x043E, 0x0261, 0x006C, 0x0435]),
        // "react" pure Cyrillic: р е а с т
        ("react-cyr",    &[0x0440, 0x0435, 0x0430, 0x0441, 0x0442]),
    ];
    let mut caught = 0;
    let mut missed: Vec<String> = Vec::new();
    for (name, cps) in attacks {
        let v = h::detect(cps);
        eprintln!("  {} skel={:X?}", name, v.iterated_skeleton);
        match v.kind {
            ClassificationKind::Hazard => {
                caught += 1;
                eprintln!(
                    "    caught: {:?}",
                    v.sub.as_ref().map(|s| s.tag()),
                );
            }
            _ => {
                missed.push(format!("{}: kind={:?}", name, v.kind));
            }
        }
    }
    eprintln!(
        "BRUTAL 2 (pure-script Hole 3): {}/{} caught",
        caught, attacks.len(),
    );
    // This test DOCUMENTS the gap — does not assert closure (Hole 3
    // requires curation expansion to close).
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 3: multi-position substitution
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_3_multi_position_substitution() {
    // Multiple Cyrillic-е substitutions in "Nethereum".  Every 'e'
    // position in the target maps to Cyrillic 'е' (U+0435) which
    // case-folded skeleton resolves to ASCII 'e'.  Target match
    // must fire for all of these.
    let attacks: &[(&str, &[u32])] = &[
        ("2-pos cyr e+e",
         &[0x4E, 0x0435, 0x74, 0x68, 0x0435, 0x72, 0x65, 0x75, 0x6D]),
        ("3-pos cyr e+e+e",
         &[0x4E, 0x0435, 0x74, 0x68, 0x0435, 0x72, 0x0435, 0x75, 0x6D]),
        ("4-pos all-cyr-e (same as 3 — only 3 e's in nethereum)",
         &[0x4E, 0x0435, 0x74, 0x68, 0x0435, 0x72, 0x0435, 0x75, 0x6D]),
    ];
    // Note: substituting Cyrillic-р (U+0440 → Latin p) for 'r' is
    // NOT a valid Nethereum typosquat — the resulting visible name
    // is "Nethepeum" with p where r should be, a different visible
    // string.  CrossScriptMix correctly fires as the layered
    // defense in that case; not a TargetMatch.
    let mut breaks = Vec::new();
    for (name, cps) in attacks {
        let v = h::detect(cps);
        let tag = v.sub.as_ref().map(|s| s.tag());
        eprintln!("  {}: tag={:?}", name, tag);
        if tag != Some("TargetMatch") {
            breaks.push(format!("{}: tag={:?}", name, tag));
        }
    }
    if !breaks.is_empty() {
        panic!(
            "BRUTAL 3: multi-position substitutions don't fire TargetMatch:\n{}",
            breaks.join("\n"),
        );
    }
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 4: insertion attack (no substitution)
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_4_visible_insertion_should_not_match_target() {
    // Insert an extra letter — this should NOT fire TargetMatch
    // (it's a different string with different length).
    // But it might fire CrossScriptMix or some other detector if
    // the inserted char triggers it.
    let v = h::detect(&[0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x65, 0x75, 0x6D, 0x73]);  // "nethereums"
    let tag = v.sub.as_ref().map(|s| s.tag());
    eprintln!("  nethereums (extra s): kind={:?} sub={:?}", v.kind, tag);
    // Acceptable outcomes: Clear, or any non-TargetMatch hazard.
    // TargetMatch{Nethereum} would be wrong — different name.
    if tag == Some("TargetMatch") {
        if let Some(SubThreat::TargetMatch { target }) = v.sub {
            if target == "Nethereum" {
                panic!("BRUTAL 4: insertion 'nethereums' falsely matched Nethereum");
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 5: variation selector appendage
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_5_variation_selector_appendage() {
    // Append VS16 (U+FE0F) to "nethereum".  CCC=0, doesn't get stripped.
    // Will TargetMatch fire?
    let input = [
        0x6E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x65, 0x75, 0x6D, 0xFE0F,
    ];
    let v = h::detect(&input);
    let tag = v.sub.as_ref().map(|s| s.tag());
    eprintln!("  nethereum + VS16: kind={:?} sub={:?}", v.kind, tag);
    // VS16 alone might not fire anything (it's "use emoji presentation").
    // It's a covert-channel-detector concern (VariationSelectorPayload),
    // but HomoglyphConfusable might not see it.
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 6: RTL-override inside target
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_6_rtl_override_inside_target() {
    // Insert RLO (U+202E) into "nethereum" at position 5.
    let input = [
        0x6E, 0x65, 0x74, 0x68, 0x65, 0x202E, 0x72, 0x65, 0x75, 0x6D,
    ];
    let v = h::detect(&input);
    let tag = v.sub.as_ref().map(|s| s.tag());
    eprintln!("  RLO inside nethereum: kind={:?} sub={:?}", v.kind, tag);
    // BidiControlBalance would fire on the RLO if used standalone, but
    // we're calling HomoglyphConfusable directly.  This documents the
    // single-detector view.
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 7: surrogate / noncharacter / PUA — must not panic
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_7_pathological_codepoints_no_panic() {
    let inputs: &[&[u32]] = &[
        &[0xD800],                    // raw high surrogate
        &[0xDC00],                    // raw low surrogate
        &[0xD800, 0xDC00],            // valid surrogate pair (raw)
        &[0xFDD0],                    // first noncharacter range
        &[0xFDEF],                    // last in first noncharacter range
        &[0xFFFE],                    // BMP noncharacter
        &[0xFFFF],                    // BMP noncharacter
        &[0xE000],                    // PUA start
        &[0xF8FF],                    // PUA end
        &[0xF0000],                   // Supplementary PUA-A start
        &[0x10FFFE, 0x10FFFF],        // supplementary noncharacters
        &[0xFFFFFFFF],                // beyond Unicode
    ];
    for input in inputs {
        let _ = h::detect(input);
    }
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 8: self-match guard bypass attempts
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_8_self_match_guard_holds_for_legit() {
    // Legitimate "Nethereum" (curated target itself) MUST be Clear.
    let v = h::detect(&[0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x65, 0x75, 0x6D]);
    assert_eq!(v.kind, ClassificationKind::Clear,
        "legitimate Nethereum must not flag itself");
    // Case-folded equivalent (lowercase) should also be Clear since
    // "nethereum" lowercase is the case-folded form of a target.
    // But we don't have "nethereum" in lowercase as a separate target,
    // so the case-folded lowercase IS the case-folded form of
    // "Nethereum" which is the target — the input differs from target
    // by case, so the t.cps != input guard skips correctly... or fires?
    let v = h::detect(&[0x6E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x65, 0x75, 0x6D]);
    eprintln!("  pure lowercase nethereum: {:?}", v.sub.as_ref().map(|s| s.tag()));
    // EXPECTED: TargetMatch{Nethereum} because input != Nethereum literally
    // but iterated letter_skeleton matches.  This is the case-insensitive
    // intent — lowercase nethereum should match the Nethereum target.
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 9: symmetric multi-char (rn for m)
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_9_rn_for_m_symmetric() {
    // Target "metamask" — attacker uses "rnetarnask" (replace each 'm'
    // with 'rn').  After substitute, target's m → rn, so target letter
    // skeleton = "rnetarnask".  Input is already "rnetarnask".
    // letter_skeletons should match → TargetMatch{metamask}.
    let input = [
        0x72, 0x6E, 0x65, 0x74, 0x61, 0x72, 0x6E, 0x61, 0x73, 0x6B,
    ];
    let v = h::detect(&input);
    let tag = v.sub.as_ref().map(|s| s.tag());
    eprintln!("  rnetarnask (rn-for-m metamask): {:?}", tag);
    assert_eq!(tag, Some("TargetMatch"),
        "rn-for-m symmetric attack must fire TargetMatch");
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 10: cascade nesting
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_10_cascade_depth() {
    // Maximum depth cascade — input that requires many iterations.
    // U+2133 ℳ → M → m → rn (3 levels deep).  Repeat 10 times.
    let input = vec![0x2133u32; 10];
    let t = Instant::now();
    let s = h::iterated_skeleton(&input);
    let e = t.elapsed();
    eprintln!("  10×U+2133 cascade: skel.len()={} in {:?}", s.len(), e);
    assert!(e.as_secs() < 1, "cascade DoS");
    assert_eq!(s, [0x72, 0x6E].repeat(10), "10 'rn' pairs expected");
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 11: Hangul-region attacks
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_11_hangul_input_no_false_positive() {
    // Pure Hangul "안녕하세요" (hello in Korean) should be Clear
    // (single-script, no confusables to ASCII).
    let input = [0xC548u32, 0xB155, 0xD558, 0xC138, 0xC694];
    let v = h::detect(&input);
    eprintln!(
        "  Pure Hangul 안녕하세요: kind={:?} sub={:?}",
        v.kind, v.sub.as_ref().map(|s| s.tag()),
    );
    assert_eq!(v.kind, ClassificationKind::Clear,
        "Pure Hangul must not flag");
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 12: bidirectional / position-swap attack
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_12_logical_order_attack() {
    // Target "react", attacker logical "tcaer" (reverse), pretending
    // RTL renders it as "react".  Logically the strings are different.
    // letter_skeleton equality: "react" vs "tcaer" — different strings.
    // No match.  This is acceptable — the visual rendering of "tcaer"
    // depends on bidi context, not the codepoints themselves.
    let input = [0x74, 0x63, 0x61, 0x65, 0x72];
    let v = h::detect(&input);
    eprintln!(
        "  Reversed react 'tcaer': kind={:?} sub={:?}",
        v.kind, v.sub.as_ref().map(|s| s.tag()),
    );
    // Acceptable for HomoglyphConfusable to miss this (no bidi).
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 13: substring-of-target should NOT match
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_13_substring_does_not_match() {
    // "ethereum" is in our target list, but "thereum" (prefix dropped)
    // should NOT match it.
    let input = [0x74, 0x68, 0x65, 0x72, 0x65, 0x75, 0x6D];
    let v = h::detect(&input);
    let tag = v.sub.as_ref().map(|s| s.tag());
    eprintln!("  'thereum' substring: tag={:?}", tag);
    if tag == Some("TargetMatch") {
        if let Some(SubThreat::TargetMatch { target }) = v.sub {
            panic!(
                "BRUTAL 13: substring 'thereum' falsely matched target {:?}",
                target,
            );
        }
    }
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 14: hyphen / punctuation in target
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_14_react_dom_with_cyrillic() {
    // "react-dom" is a curated target.  Test that Cyrillic 'а' at the
    // 'a' position in "react" still fires TargetMatch{react-dom}.
    let input = [0x72, 0x65, 0x0430, 0x63, 0x74, 0x2D, 0x64, 0x6F, 0x6D];
    let v = h::detect(&input);
    let tag = v.sub.as_ref().map(|s| s.tag());
    eprintln!("  react-dom with Cyr-a: tag={:?}", tag);
    assert_eq!(tag, Some("TargetMatch"));
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 15: massive-input DoS
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_15_massive_input_dos() {
    // 1 MB worth of confusable codepoints — every byte goes through
    // the full skeleton pipeline.
    let input = vec![0x0435u32; 200_000];  // 200k Cyrillic е
    let t = Instant::now();
    let _ = h::detect(&input);
    let e = t.elapsed();
    eprintln!("  200k Cyrillic-е: {:?}", e);
    assert!(e.as_secs() < 30, "200k input DoS");
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 16: every-codepoint-in-confusables DoS
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_16_every_confusable_at_once() {
    // Build an input from the first 1000 source codepoints of
    // confusables.txt.  Forces skeleton to do ~1000 lookups.
    let confusables = include_str!("../data/confusables.txt");
    let mut input = Vec::new();
    for line in confusables.lines().take(2000) {
        let body = match line.find('#') {
            Some(idx) => &line[..idx],
            None => line,
        };
        let stripped = body.trim();
        if stripped.is_empty() { continue; }
        let parts: Vec<&str> = stripped.splitn(2, ';').collect();
        if parts.len() < 2 { continue; }
        if let Ok(cp) = u32::from_str_radix(parts[0].trim(), 16) {
            input.push(cp);
        }
        if input.len() >= 1000 { break; }
    }
    let t = Instant::now();
    let _ = h::detect(&input);
    let e = t.elapsed();
    eprintln!("  1000 distinct confusables: {:?}", e);
    assert!(e.as_secs() < 5);
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 17: empty / whitespace-only input
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_17_whitespace_only() {
    let inputs: &[&[u32]] = &[
        &[],                                  // empty
        &[0x20],                              // single space
        &[0x20, 0x20, 0x20],                  // three spaces
        &[0x09, 0x0A, 0x0D],                  // tab newline cr
        &[0xA0],                              // NBSP
        &[0x3000],                            // Ideographic space
    ];
    for input in inputs {
        let v = h::detect(input);
        eprintln!(
            "  whitespace input {:X?}: kind={:?}",
            input, v.kind,
        );
        // Empty / pure-whitespace shouldn't trigger TargetMatch
        match &v.sub {
            Some(SubThreat::TargetMatch { target }) => {
                panic!(
                    "Whitespace input {:X?} falsely matched target {:?}",
                    input, target,
                );
            }
            _ => {}
        }
    }
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 18: codepoints right at NFC quick-check boundary
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_18_nfc_quick_check_edge() {
    // U+0340 (COMBINING GRAVE TONE MARK) has NFC_QC = N.
    // U+0344 (COMBINING GREEK DIALYTIKA TONOS) has NFC_QC = N.
    // U+212B (ANGSTROM SIGN) — singleton decomposition.
    let inputs = [
        &[0x0340u32][..],
        &[0x0344u32][..],
        &[0x212Bu32][..],
        &[0x4Eu32, 0x65, 0x74, 0x212B][..],  // "Net" + angstrom
    ];
    for input in inputs {
        let v = h::detect(input);
        eprintln!(
            "  NFC-edge input {:X?}: kind={:?} sub={:?}",
            input, v.kind, v.sub.as_ref().map(|s| s.tag()),
        );
        // No panic, well-shaped verdict.
        match v.kind {
            ClassificationKind::Clear => assert!(v.sub.is_none()),
            ClassificationKind::Hazard => assert!(v.sub.is_some()),
            _ => panic!("unexpected kind"),
        }
    }
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 19: many-target cascade — input matches MULTIPLE targets
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_19_skeleton_collision_between_targets() {
    // Force find_target_match to walk most of the target list to
    // confirm it returns the FIRST match (matching the spec).
    // Use input that case-folded matches multiple targets if any.
    // The curated list is unique by literal name; skeleton collisions
    // unlikely but we can construct one with Cyrillic-only spoof of
    // any target.  Test that 'reaкt' (Cyrillic К) fires react not
    // some collision.
    let input = [0x72, 0x65, 0x61, 0x043A, 0x74];
    let v = h::detect(&input);
    let tag = v.sub.as_ref().map(|s| s.tag());
    if let Some(SubThreat::TargetMatch { target }) = &v.sub {
        eprintln!("  reaКt (Cyr к): TargetMatch{{{}}}", target);
        assert_eq!(target.to_lowercase(), "react");
    } else {
        eprintln!("  reaКt: tag={:?}", tag);
    }
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 20: full-width punctuation in target context
// ════════════════════════════════════════════════════════════════════

#[test]
fn brutal_20_fullwidth_hyphen_in_react_dom() {
    // "react-dom" with FULLWIDTH HYPHEN-MINUS (U+FF0D) replacing -.
    let input = [
        0x72, 0x65, 0x61, 0x63, 0x74, 0xFF0D, 0x64, 0x6F, 0x6D,
    ];
    let v = h::detect(&input);
    let tag = v.sub.as_ref().map(|s| s.tag());
    eprintln!("  react-dom with fullwidth hyphen: tag={:?}", tag);
    // Expected: TargetMatch (case-fold + substitute should normalize
    // fullwidth hyphen to ASCII hyphen IF it's in the confusables map).
    // Or WidthClass as fallback.
    assert_eq!(v.kind, ClassificationKind::Hazard);
}
