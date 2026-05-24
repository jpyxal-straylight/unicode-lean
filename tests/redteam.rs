//! Red-team test suite — adversarial attacks I would actually try
//! if my job was to slip past this detector.  Each test names the
//! attack class, the rationale, and the expected detector behaviour.
//! A test PASSING means the detector caught me.  A test FAILING
//! means I found a hole.

use unicode_rust::security::ClassificationKind;
use unicode_rust::security::identity::homoglyph_confusable;
use unicode_rust::security::identity::ucd;

fn caught(input: &[u32], expected_tag: &str) -> bool {
    let v = homoglyph_confusable::detect(input);
    if v.kind != ClassificationKind::Hazard {
        eprintln!(
            "MISS: input {:X?} not flagged (expected {})",
            input, expected_tag,
        );
        return false;
    }
    match &v.sub {
        Some(sub) => {
            let got = sub.tag();
            if got != expected_tag {
                eprintln!(
                    "WRONG TAG: input {:X?} got {} (expected {})",
                    input, got, expected_tag,
                );
            }
            true
        }
        None => false,
    }
}

fn caught_any(input: &[u32]) -> bool {
    let v = homoglyph_confusable::detect(input);
    if v.kind != ClassificationKind::Hazard {
        eprintln!(
            "MISS: input {:X?} not flagged at all",
            input,
        );
        return false;
    }
    true
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 1: Lowercase canonical
// Curated target is "Nethereum" (preserved case).  NuGet IDs are
// case-INSENSITIVE.  Attacker registers lowercase "nethereum" with
// Cyrillic-е at position 6.  Will our case-sensitive target match
// catch it?
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_1_lowercase_canonical_with_cyrillic() {
    // "nethereum" with Cyrillic SMALL LETTER IE at pos 6.
    let input = [0x6E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D];
    assert!(caught_any(&input), "ATTACK 1: lowercase NuGet-style typosquat");
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 2: Uppercase canonical
// Like attack 1 but ALL CAPS.  Cyrillic CAPITAL IE U+0415.
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_2_uppercase_canonical_with_cyrillic() {
    // "NETHEREUM" with Cyrillic CAPITAL IE at pos 6.
    let input = [0x4E, 0x45, 0x54, 0x48, 0x45, 0x52, 0x0415, 0x55, 0x4D];
    assert!(caught_any(&input), "ATTACK 2: all-caps NuGet-style typosquat");
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 3: Letterlike Symbols (U+2100..U+214F)
// The Mathematical Alphanumeric block (U+1D400..U+1D7FF) is covered.
// But there's a SEPARATE Letterlike Symbols block at U+2100..U+214F
// containing ℕ ℝ ℂ ℤ ℋ ℘ etc. — double-struck capitals identical
// to Latin uppercase.  Attack: "ℕethereum" (U+2115 + ethereum).
// Will MathAlpha catch this?  TargetMatch?  Anything?
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_3_letterlike_symbol_N() {
    // ℕ (U+2115) followed by "ethereum".
    let input = [0x2115, 0x65, 0x74, 0x68, 0x65, 0x72, 0x65, 0x75, 0x6D];
    assert!(caught_any(&input), "ATTACK 3: ℕ U+2115 spoof");
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 4: Cherokee letter look-alike (classic confusables.txt gap)
// Cherokee LETTER A (U+13AA) is visually identical to Latin D.
// Was historically NOT in confusables.txt and slipped past detectors
// for years.  Has Unicode added it?  Does our skeleton catch
// "Etherea" → "EthereD" with Cherokee A?
// Testing the inverse: a target containing 'D' substituted with
// Cherokee letter that looks like D.
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_4_cherokee_letter_lookalike() {
    // Cherokee LETTER MV (U+13DB) looks like Latin O.  Test:
    // "Nethereum" → "NethereuO" with M+V substitution?  Wait this
    // doesn't match a known target.  Try: target list includes "OpenAI"?
    let targets = unicode_rust::security::identity::homoglyph_confusable
        ::iterated_skeleton(&[]);
    // Force the skeleton to be loaded so we don't measure miss as
    // a load failure.
    drop(targets);
    // Use a clearer test: Cherokee LETTER A (U+13AA) → ? in confusables.
    // Just check if it skeletons to Latin D or anything ASCII.
    let cherokee_a = [0x13AAu32];
    let skel = homoglyph_confusable::skeleton(&cherokee_a);
    eprintln!("Cherokee A (U+13AA) skeletons to: {:X?}", skel);
    // If skel == [0x13AA] (unchanged), it's NOT in confusables → a gap.
    // If skel contains an ASCII letter, the spoof would map and we're OK.
    // This test is INFORMATIONAL — it doesn't assert; it reports.
    if skel == cherokee_a {
        eprintln!("GAP: U+13AA Cherokee LETTER A has no skeleton entry");
    }
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 5: Precomposed-form bypass for DecompositionSwap
// DecompositionSwap fires when input != NFC(input).
// If input is ALREADY in NFC, no fire.  Attacker uses precomposed
// é (U+00E9) — already NFC.  Will detector see anything?
// Test target with accented chars: registered "café" using U+00E9
// vs legit "café" using e + ◌́.  Both look identical.
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_5_precomposed_form_already_nfc() {
    // "café" with composed é = [c, a, f, é] = [0x63, 0x61, 0x66, 0xE9]
    let input = [0x63u32, 0x61, 0x66, 0xE9];
    let nfc = ucd::to_nfc(&input);
    eprintln!("NFC of composed café: {:X?} (expected unchanged)", nfc);
    assert_eq!(nfc, input.to_vec(), "Composed form should be in NFC");

    // Decomposed form: c + a + f + e + combining-acute
    let decomposed = [0x63u32, 0x61, 0x66, 0x65, 0x0301];
    let nfc2 = ucd::to_nfc(&decomposed);
    eprintln!("NFC of decomposed café: {:X?} (expected [63,61,66,E9])", nfc2);
    assert_eq!(
        nfc2,
        vec![0x63, 0x61, 0x66, 0xE9],
        "Decomposed should NFC to composed"
    );
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 6: Iterated skeleton cycle / non-termination
// What if confusables happen to form a cycle?  E.g. A → B and
// B → A.  iteratedSkeleton would loop forever.
// Also: what if a single skeleton expands without shrinking (so
// iteratedSkeleton grows the input forever)?
// Test: feed pathological inputs and ensure detector terminates.
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_6_iterated_skeleton_terminates() {
    use std::time::Instant;
    // 1024 random-ish codepoints chosen to stress confusables.
    let mut input = Vec::with_capacity(1024);
    for i in 0..1024 {
        input.push((0x0400 + (i % 0x80)) as u32);  // Cyrillic block
    }
    let start = Instant::now();
    let _skel = homoglyph_confusable::iterated_skeleton(&input);
    let elapsed = start.elapsed();
    eprintln!("iteratedSkeleton over 1024 Cyrillic cps: {:?}", elapsed);
    assert!(
        elapsed.as_millis() < 1000,
        "iteratedSkeleton should not be quadratic-or-worse"
    );
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 7: ZWJ stuffing inside an identifier
// "Net​herеum" — ZWSP inserted between codepoints.
// Skeleton ignores ZWSP (passes through).  Iterated skeleton of
// input would still contain the ZWSP, breaking TargetMatch.
// But ZeroWidthPayload should fire as a layered defence.
// What does the priority ordering pick?
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_7_zwsp_inside_identifier() {
    // "Nethere" + ZWSP + Cyrillic-е + "um"
    let input = [
        0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x65, 0x200B,
        0x0435, 0x75, 0x6D,
    ];
    let v = homoglyph_confusable::detect(&input);
    eprintln!(
        "Cyrillic+ZWSP attack: kind={:?} sub={:?}",
        v.kind, v.sub
    );
    // HomoglyphConfusable doesn't check ZWSP, so this might be
    // CrossScriptMix (because ZWSP is Common+ignored, Cyrillic 'е'
    // remains as the only non-Latin, but no Latin needs Latin to be
    // counted — wait, all non-Cyrillic codepoints are Latin or
    // Common.  So script_union = {Latn, Cyrl}, count == 2.  Would
    // fire CrossScriptMix.
    // OR: ZWSP IS Common but Cyrillic 'е' (U+0435) skeletons to
    // Latin 'e' (U+0065), so iterated_skeleton([..., 0x200B, 0x0435,
    // ...]) might be [..., 0x200B, 0x0065, ...] — still doesn't
    // match the canonical Nethereum target (because of the inserted
    // ZWSP).  So TargetMatch wouldn't fire.
    assert!(
        v.kind == ClassificationKind::Hazard,
        "ATTACK 7: ZWSP-stuffed typosquat MUST flag somehow"
    );
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 8: Compound bidi + confusable
// Wrap the Cyrillic-е variant in bidi controls so it visually
// renders differently.  Bidi detector should fire on the
// unbalanced bidi; homoglyph detector should still also flag.
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_8_bidi_wrapped_confusable() {
    use unicode_rust::security::covert::bidi_control_balance;
    // RLO + Nethereum with Cyrillic + PDF
    let input = [
        0x202E, // RLO
        0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D,
        0x202C, // PDF
    ];
    let bidi = bidi_control_balance::detect(&input);
    eprintln!("Bidi verdict on RLO-wrapped: kind={:?}", bidi.kind);
    let homo = homoglyph_confusable::detect(&input);
    eprintln!("Homoglyph verdict on RLO-wrapped: kind={:?} sub={:?}",
              homo.kind, homo.sub);
    // The Cyrillic + RLO + PDF doesn't break homoglyph TargetMatch
    // because bidi controls are Common-script (ignored) and don't
    // appear in skeleton output... but they DO appear in input, so
    // iterated_skeleton(input) != iterated_skeleton("Nethereum").
    // Will detect anything?
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 9: Cyrillic-only spoof (looks like Latin "apple")
// аррlе — fully Cyrillic but reads as "apple"
// All Cyrillic, no script-mix → no CrossScriptMix.
// All in confusables → iteratedSkeleton == [a,p,p,l,e].
// "apple" is NOT in our 67-target list, so TargetMatch doesn't fire.
// Single-script Cyrillic → HighlyRestrictive → RestrictionLow no.
// RESULT: HomoglyphConfusable returns CLEAR.
// This is the classic IDN homograph attack vector and our
// detector misses it because "apple" isn't a curated target.
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_9_cyrillic_only_apple_spoof() {
    // Cyrillic а р р ӏ е = U+0430 U+0440 U+0440 U+04CF U+0435
    let input = [0x0430u32, 0x0440, 0x0440, 0x04CF, 0x0435];
    let v = homoglyph_confusable::detect(&input);
    let rl = ucd::restriction_level(&input);
    eprintln!("RL of pure-Cyrillic 'apple': {:?}", rl);
    eprintln!(
        "Pure-Cyrillic apple-spoof: kind={:?} sub={:?}",
        v.kind, v.sub,
    );
    // KNOWN MISS: not in target list, single-script Cyrillic.
    // This documents the gap, NOT a defect to fix at the detector
    // layer — it's a curation gap.
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 10: Empty / degenerate inputs (DoS / panic)
// Confirm detector terminates on:
//   - Empty input
//   - Single zero codepoint (NUL)
//   - Single codepoint at scalar ceiling (U+10FFFF)
//   - Codepoint beyond scalar ceiling (U+110000) — invalid Unicode
//   - Surrogate (U+D800) — invalid scalar
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_10_degenerate_no_panic() {
    let _ = homoglyph_confusable::detect(&[]);
    let _ = homoglyph_confusable::detect(&[0]);
    let _ = homoglyph_confusable::detect(&[0x10FFFF]);
    let _ = homoglyph_confusable::detect(&[0x110000]);
    let _ = homoglyph_confusable::detect(&[0xD800]);
    let _ = homoglyph_confusable::detect(&[0xFFFFFFFF]);  // beyond all
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 11: NFC bomb (decomposition explosion)
// Some codepoints decompose to many.  Stack U+FDFA (ARABIC LIGATURE
// SALLALLAHOU ALAYHE WASALLAM) which decomposes into 18 codepoints.
// Decomposing 10000 of these = 180_000 codepoint output.
// Will to_nfc terminate in reasonable time?
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_11_nfc_decomposition_bomb() {
    use std::time::Instant;
    let input = vec![0xFDFAu32; 10_000];
    let start = Instant::now();
    let nfc = ucd::to_nfc(&input);
    let elapsed = start.elapsed();
    eprintln!(
        "NFC of 10k U+FDFA: input_len={} output_len={} in {:?}",
        input.len(), nfc.len(), elapsed,
    );
    assert!(elapsed.as_secs() < 5, "NFC bomb DoS");
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 12: Pathological CCC ordering (combining-mark stack)
// Stack 1000 combining marks on one base.  CCC reorder is
// O(n log n) per run; 1000 marks = bounded.  Stress test.
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_12_combining_mark_stack() {
    use std::time::Instant;
    let mut input = vec![0x0041u32];  // 'A'
    for _ in 0..1000 {
        input.push(0x0300);  // combining grave
        input.push(0x0301);  // combining acute
        input.push(0x0327);  // combining cedilla
    }
    let start = Instant::now();
    let _nfc = ucd::to_nfc(&input);
    let elapsed = start.elapsed();
    eprintln!(
        "NFC of A + 3000 combining marks: {:?}",
        elapsed,
    );
    assert!(elapsed.as_secs() < 5, "Combining mark DoS");
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 13: Bidi at exactly depth-limit boundary
// UAX #9 §3.3.2 caps stack depth at 125.  Test 124 (allowed),
// 125 (allowed), 126 (exceeds).
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_13_bidi_depth_boundary() {
    use unicode_rust::security::covert::bidi_control_balance;
    for n in &[124usize, 125, 126] {
        let mut input = vec![0x202Au32; *n];
        input.extend(std::iter::repeat(0x202Cu32).take(*n));
        let v = bidi_control_balance::detect(&input);
        eprintln!(
            "Bidi depth={}: kind={:?} sub={:?}",
            n, v.kind, v.sub.as_ref().map(|s| s.tag()),
        );
    }
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 14: VariationSelector on legal target — payload bypass
// VS on a CJK ideograph is "legitimate".  But attacker stuffs an
// 8-VS payload (= 4 bytes covert data) on an ideograph base.
// Our isLegalVariationTarget says it's "legal", so we don't flag?
// Wait — we check IllegalTarget for non-CJK bases, but we don't
// flag DirectPayload on legal-target bases.  CHECK.
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_14_vs_payload_on_ideograph() {
    use unicode_rust::security::covert::variation_selector_payload;
    // U+4E00 (一 first CJK Unified Ideograph) + 8 variation selectors
    let mut input = vec![0x4E00u32];
    for i in 0..8 {
        input.push(0xE0100 + i);
    }
    let v = variation_selector_payload::detect(&input);
    eprintln!(
        "VS payload on CJK ideograph (8 selectors): kind={:?} sub={:?}",
        v.kind,
        v.sub.as_ref().map(|s| s.tag()),
    );
}

// ════════════════════════════════════════════════════════════════════
// ATTACK 15: NFC-form-vs-decomposed for an attack target
// Target "Nethereum" is plain ASCII so no NFC drift.  But if a
// target had accents, attacker could use the OTHER form.
// Synthetic test: would our skeleton normalize through NFC?
// The Lean reference applies NFD as part of skeleton.  We don't.
// Confirm this gap.
// ════════════════════════════════════════════════════════════════════
#[test]
fn attack_15_skeleton_doesnt_normalize() {
    // U+00E9 = é precomposed
    let precomposed = [0xE9u32];
    let skel_pre = homoglyph_confusable::skeleton(&precomposed);
    // U+0065 + U+0301 = e + combining acute (decomposed)
    let decomposed = [0x65u32, 0x0301];
    let skel_dec = homoglyph_confusable::skeleton(&decomposed);
    eprintln!("Skeleton of composed é: {:X?}", skel_pre);
    eprintln!("Skeleton of decomposed é: {:X?}", skel_dec);
    if skel_pre != skel_dec {
        eprintln!(
            "GAP: skeleton does not normalize through NFD.  \
             Precomposed and decomposed forms have different skeletons.  \
             UTS #39 §4 specifies NFD as part of skeleton."
        );
    }
}
