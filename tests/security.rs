use unicode_rust::security::ClassificationKind;
use unicode_rust::security::covert::{
    bidi_control_balance, tag_block_payload, variation_selector_payload,
    zero_width_payload,
};
use unicode_rust::security::identity::homoglyph_confusable;

// ─────────────────────────────────────────────────────────────────────
// TagBlockPayload
// ─────────────────────────────────────────────────────────────────────

#[test]
fn tag_block_empty_clear() {
    assert_eq!(tag_block_payload::detect(&[]).kind, ClassificationKind::Clear);
}

#[test]
fn tag_block_ascii_clear() {
    let v = tag_block_payload::detect(&[0x48, 0x65, 0x6C, 0x6C, 0x6F]);
    assert_eq!(v.kind, ClassificationKind::Clear);
}

#[test]
fn tag_block_direct_ascii_ab() {
    let v = tag_block_payload::detect(&[0xE0041, 0xE0042]);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.unwrap().tag(), "DirectAscii");
    assert_eq!(v.recovered_ascii, "AB");
}

#[test]
fn tag_block_goodside_decodes() {
    let v = tag_block_payload::detect(&[
        0xE0050, 0xE0072, 0xE0069, 0xE006E, 0xE0074,
        0xE0020, 0xE0027, 0xE0070, 0xE0077, 0xE006E,
        0xE0065, 0xE0064, 0xE0027,
    ]);
    assert_eq!(v.recovered_ascii, "Print 'pwned'");
}

#[test]
fn tag_block_language_tag_revival() {
    let v = tag_block_payload::detect(&[0xE0001, 0xE0065, 0xE006E]);
    assert_eq!(v.sub.unwrap().tag(), "LanguageTagRevival");
}

#[test]
fn tag_block_mixed_block() {
    let v = tag_block_payload::detect(&[0x48, 0x69, 0xE0070, 0xE0077, 0xE006E, 0xE0064]);
    assert_eq!(v.sub.unwrap().tag(), "MixedBlock");
}

#[test]
fn tag_block_cancel_bare() {
    let v = tag_block_payload::detect(&[0xE007F]);
    assert_eq!(v.sub.unwrap().tag(), "BareTagPresent");
}

// ─────────────────────────────────────────────────────────────────────
// BidiControlBalance
// ─────────────────────────────────────────────────────────────────────

#[test]
fn bidi_empty_clear() {
    assert_eq!(bidi_control_balance::detect(&[]).kind, ClassificationKind::Clear);
}

#[test]
fn bidi_balanced_embedding_clear() {
    let v = bidi_control_balance::detect(&[0x202A, 0x41, 0x202C]);
    assert_eq!(v.kind, ClassificationKind::Clear);
}

#[test]
fn bidi_balanced_isolate_clear() {
    let v = bidi_control_balance::detect(&[0x2066, 0x41, 0x2069]);
    assert_eq!(v.kind, ClassificationKind::Clear);
}

#[test]
fn bidi_lone_rlo_unbalanced() {
    let v = bidi_control_balance::detect(&[0x202E, 0x41]);
    assert_eq!(v.sub.unwrap().tag(), "UnbalancedEmbedding");
}

#[test]
fn bidi_lone_pdf_orphan() {
    let v = bidi_control_balance::detect(&[0x202C]);
    assert_eq!(v.sub.unwrap().tag(), "OrphanPop");
}

#[test]
fn bidi_lone_lri_unbalanced_isolate() {
    let v = bidi_control_balance::detect(&[0x2067, 0x41]);
    assert_eq!(v.sub.unwrap().tag(), "UnbalancedIsolate");
}

#[test]
fn bidi_depth_exceeded() {
    let mut input = vec![0x202A_u32; 126];
    input.extend(std::iter::repeat(0x202C_u32).take(126));
    let v = bidi_control_balance::detect(&input);
    assert_eq!(v.sub.unwrap().tag(), "DepthExceeded");
}

#[test]
fn bidi_trojan_source_unbalanced() {
    let v = bidi_control_balance::detect(&[0x69, 0x66, 0x20, 0x202E, 0x29, 0x7B]);
    assert_eq!(v.sub.unwrap().tag(), "UnbalancedEmbedding");
}

// ─────────────────────────────────────────────────────────────────────
// ZeroWidthPayload
// ─────────────────────────────────────────────────────────────────────

#[test]
fn zw_empty_clear() {
    assert_eq!(zero_width_payload::detect(&[]).kind, ClassificationKind::Clear);
}

#[test]
fn zw_ascii_clear() {
    let v = zero_width_payload::detect(&[0x48, 0x69]);
    assert_eq!(v.kind, ClassificationKind::Clear);
}

#[test]
fn zw_single_zwsp_bare() {
    let v = zero_width_payload::detect(&[0x61, 0x200B, 0x62]);
    assert_eq!(v.sub.unwrap().tag(), "BareZeroWidth");
}

#[test]
fn zw_word_joiner_injection() {
    let v = zero_width_payload::detect(&[0x61, 0x2060, 0x62]);
    assert_eq!(v.sub.unwrap().tag(), "WordJoinerInjection");
}

#[test]
fn zw_multiple_nnbsp_watermark() {
    let v = zero_width_payload::detect(&[0x61, 0x202F, 0x62, 0x202F, 0x63]);
    assert_eq!(v.sub.unwrap().tag(), "AiWatermarkNNBSP");
}

#[test]
fn zw_multiple_zwsp_binary_payload() {
    let v = zero_width_payload::detect(&[0x61, 0x200B, 0x200B, 0x200B, 0x200B]);
    assert_eq!(v.sub.unwrap().tag(), "BinaryPayload");
}

#[test]
fn zw_annotation_misuse() {
    let v = zero_width_payload::detect(&[0x61, 0xFFF9, 0x62]);
    assert_eq!(v.sub.unwrap().tag(), "AnnotationMisuse");
}

// ─────────────────────────────────────────────────────────────────────
// VariationSelectorPayload
// ─────────────────────────────────────────────────────────────────────

#[test]
fn vs_empty_clear() {
    assert_eq!(
        variation_selector_payload::detect(&[]).kind,
        ClassificationKind::Clear,
    );
}

#[test]
fn vs_ascii_clear() {
    let v = variation_selector_payload::detect(&[0x48, 0x69]);
    assert_eq!(v.kind, ClassificationKind::Clear);
}

#[test]
fn vs_illegal_target_latin() {
    let v = variation_selector_payload::detect(&[0x0041, 0xFE0F]);
    assert_eq!(v.sub.unwrap().tag(), "IllegalTarget");
}

#[test]
fn vs_direct_payload_byte() {
    let v = variation_selector_payload::detect(&[0x0061, 0xFE04, 0xFE01]);
    assert_eq!(v.sub.unwrap().tag(), "DirectPayload");
    assert_eq!(v.recovered_bytes, vec![0x41_u8]);
}

#[test]
fn vs_repeated_base() {
    let v = variation_selector_payload::detect(&[
        0x0061, 0xFE04, 0xFE04, 0xFE04, 0xFE04,
        0xFE04, 0xFE04, 0xFE04, 0xFE04,
    ]);
    assert_eq!(v.sub.unwrap().tag(), "RepeatedBase");
}

#[test]
fn vs_supplementary_on_latin() {
    let v = variation_selector_payload::detect(&[0x0041, 0xE0100]);
    assert_eq!(v.sub.unwrap().tag(), "IllegalTarget");
}

// ─────────────────────────────────────────────────────────────────────
// HomoglyphConfusable
// ─────────────────────────────────────────────────────────────────────

#[test]
fn homoglyph_empty_clear() {
    let v = homoglyph_confusable::detect(&[]);
    assert_eq!(v.kind, ClassificationKind::Clear);
}

#[test]
fn homoglyph_pure_ascii_clear() {
    // "hello" — no confusables, no math-alpha, no fullwidth.
    let v = homoglyph_confusable::detect(&[0x68, 0x65, 0x6C, 0x6C, 0x6F]);
    assert_eq!(v.kind, ClassificationKind::Clear);
}

#[test]
fn homoglyph_nethereum_cyrillic_e_target_match() {
    // "Nethereum" with the second 'e' (between r and u) replaced by
    // Cyrillic SMALL LETTER IE (U+0435) — the Oct 2025 NuGet
    // supply-chain attack vector.
    let input = [0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D];
    let v = homoglyph_confusable::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.as_ref().unwrap().tag(), "TargetMatch");
    if let Some(homoglyph_confusable::SubThreat::TargetMatch { target }) = v.sub {
        assert_eq!(target, "Nethereum");
    } else {
        panic!("expected TargetMatch sub-threat");
    }
}

#[test]
fn homoglyph_math_alpha_a() {
    // U+1D400 MATHEMATICAL BOLD CAPITAL A.
    let v = homoglyph_confusable::detect(&[0x1D400]);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.as_ref().unwrap().tag(), "MathAlpha");
}

#[test]
fn homoglyph_math_alpha_count() {
    // Three Mathematical Bold capitals.
    let v = homoglyph_confusable::detect(&[0x1D400, 0x1D401, 0x1D402]);
    if let Some(homoglyph_confusable::SubThreat::MathAlpha { count, .. }) = v.sub {
        assert_eq!(count, 3);
    } else {
        panic!("expected MathAlpha sub-threat");
    }
}

#[test]
fn homoglyph_fullwidth_a() {
    // U+FF21 FULLWIDTH LATIN CAPITAL LETTER A.  Note: this also
    // maps to 'A' in confusables, so target match takes precedence
    // if "A" is in the targets file — it is not, so WidthClass wins.
    let v = homoglyph_confusable::detect(&[0xFF21]);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.as_ref().unwrap().tag(), "WidthClass");
}

#[test]
fn homoglyph_skeleton_cyrillic_to_latin() {
    // Cyrillic 'е' (U+0435) should skeleton to Latin 'e' (U+0065).
    let s = homoglyph_confusable::skeleton(&[0x0435]);
    assert_eq!(s, vec![0x0065]);
}

#[test]
fn homoglyph_iterated_skeleton_fixed_point() {
    // Pure ASCII 'a' has no further skeletons.
    let s = homoglyph_confusable::iterated_skeleton(&[0x61]);
    assert_eq!(s, vec![0x61]);
}

#[test]
fn homoglyph_math_block_predicate() {
    assert!(homoglyph_confusable::is_math_alphanumeric(0x1D400));
    assert!(homoglyph_confusable::is_math_alphanumeric(0x1D7FF));
    assert!(!homoglyph_confusable::is_math_alphanumeric(0x1D3FF));
    assert!(!homoglyph_confusable::is_math_alphanumeric(0x1D800));
}

#[test]
fn homoglyph_fullwidth_block_predicate() {
    assert!(homoglyph_confusable::is_fullwidth_halfwidth(0xFF01));
    assert!(homoglyph_confusable::is_fullwidth_halfwidth(0xFFEF));
    assert!(!homoglyph_confusable::is_fullwidth_halfwidth(0xFF00));
    assert!(!homoglyph_confusable::is_fullwidth_halfwidth(0xFFF0));
}

#[test]
fn homoglyph_decomposition_swap_a_grave() {
    // 'A' (U+0041) + COMBINING GRAVE ACCENT (U+0300) is not in NFC;
    // toNFC composes it into À (U+00C0).
    let v = homoglyph_confusable::detect(&[0x0041, 0x0300]);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.as_ref().unwrap().tag(), "DecompositionSwap");
}

#[test]
fn homoglyph_cross_script_latin_hebrew() {
    // Latin 'a' (U+0061) + Hebrew ALEF (U+05D0) — disjoint scripts,
    // neither in confusables.  Fires CrossScriptMix.
    let v = homoglyph_confusable::detect(&[0x0061, 0x05D0]);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.as_ref().unwrap().tag(), "CrossScriptMix");
}

#[test]
fn homoglyph_pure_greek_clear() {
    // "λόγος" — single-script Greek, no spoofing structure.
    let v = homoglyph_confusable::detect(&[
        0x03BB, 0x03CC, 0x03B3, 0x03BF, 0x03C2,
    ]);
    assert_eq!(v.kind, ClassificationKind::Clear);
}
