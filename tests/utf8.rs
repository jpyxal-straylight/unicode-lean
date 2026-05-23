use unicode_rust::{
    Utf8RejectKind,
    decode_to_codepoints,
    encode_codepoint,
    encode_codepoints,
    first_invalid_utf8_offset,
    is_valid_utf8,
};

// ─────────────────────────────────────────────────────────────────────
// Acceptance
// ─────────────────────────────────────────────────────────────────────

#[test]
fn accepts_empty_input() {
    assert!(is_valid_utf8(&[]));
    assert_eq!(first_invalid_utf8_offset(&[]), None);
}

#[test]
fn accepts_pure_ascii() {
    // "Hello"
    let bytes = b"Hello";
    assert!(is_valid_utf8(bytes));
    assert_eq!(
        decode_to_codepoints(bytes),
        vec![0x48, 0x65, 0x6C, 0x6C, 0x6F]
    );
}

#[test]
fn accepts_two_byte_sequence() {
    // U+00E9 é
    let bytes = &[0xC3, 0xA9];
    assert!(is_valid_utf8(bytes));
    assert_eq!(decode_to_codepoints(bytes), vec![0xE9]);
}

#[test]
fn accepts_three_byte_sequence() {
    // U+4E2D 中
    let bytes = &[0xE4, 0xB8, 0xAD];
    assert!(is_valid_utf8(bytes));
    assert_eq!(decode_to_codepoints(bytes), vec![0x4E2D]);
}

#[test]
fn accepts_four_byte_sequence() {
    // U+1F600 😀
    let bytes = &[0xF0, 0x9F, 0x98, 0x80];
    assert!(is_valid_utf8(bytes));
    assert_eq!(decode_to_codepoints(bytes), vec![0x1F600]);
}

// ─────────────────────────────────────────────────────────────────────
// Rejection — every Utf8RejectKind
// ─────────────────────────────────────────────────────────────────────

#[test]
fn rejects_overlong_two_byte_via_invalid_start() {
    // 0xC0 / 0xC1 are rejected at the start-byte level.
    let bytes = &[0xC0, 0xAF];
    assert!(!is_valid_utf8(bytes));
    assert_eq!(
        first_invalid_utf8_offset(bytes),
        Some((0, Utf8RejectKind::InvalidStartByte))
    );
}

#[test]
fn rejects_overlong_three_byte() {
    // 0xE0 0x80 0xAF — overlong encoding of U+002F
    let bytes = &[0xE0, 0x80, 0xAF];
    assert!(!is_valid_utf8(bytes));
    assert_eq!(
        first_invalid_utf8_offset(bytes),
        Some((0, Utf8RejectKind::OverlongEncoding))
    );
}

#[test]
fn rejects_high_surrogate() {
    // U+D800 attempted as 0xED 0xA0 0x80
    let bytes = &[0xED, 0xA0, 0x80];
    assert!(!is_valid_utf8(bytes));
    assert_eq!(
        first_invalid_utf8_offset(bytes).map(|(_, k)| k),
        Some(Utf8RejectKind::SurrogateCodepoint)
    );
}

#[test]
fn rejects_codepoint_beyond_max() {
    // U+110000 attempted as 0xF4 0x90 0x80 0x80
    let bytes = &[0xF4, 0x90, 0x80, 0x80];
    assert!(!is_valid_utf8(bytes));
    assert_eq!(
        first_invalid_utf8_offset(bytes).map(|(_, k)| k),
        Some(Utf8RejectKind::CodepointBeyondMax)
    );
}

#[test]
fn rejects_truncated_two_byte_sequence() {
    let bytes = &[0xC2];
    assert!(!is_valid_utf8(bytes));
    assert_eq!(
        first_invalid_utf8_offset(bytes),
        Some((1, Utf8RejectKind::TruncatedSequence))
    );
}

#[test]
fn rejects_invalid_start_byte() {
    let bytes = &[0x80];
    assert!(!is_valid_utf8(bytes));
    assert_eq!(
        first_invalid_utf8_offset(bytes),
        Some((0, Utf8RejectKind::InvalidStartByte))
    );
}

#[test]
fn rejects_invalid_continuation_byte() {
    let bytes = &[0xC2, 0x00];
    assert!(!is_valid_utf8(bytes));
    assert_eq!(
        first_invalid_utf8_offset(bytes),
        Some((1, Utf8RejectKind::InvalidContinuationByte))
    );
}

#[test]
fn rejects_0xf5_start_byte() {
    let bytes = &[0xF5, 0x80, 0x80, 0x80];
    assert!(!is_valid_utf8(bytes));
    assert_eq!(
        first_invalid_utf8_offset(bytes).map(|(_, k)| k),
        Some(Utf8RejectKind::InvalidStartByte)
    );
}

// ─────────────────────────────────────────────────────────────────────
// Encoder
// ─────────────────────────────────────────────────────────────────────

#[test]
fn encodes_one_byte_codepoints() {
    assert_eq!(encode_codepoint(0x00), vec![0x00]);
    assert_eq!(encode_codepoint(0x41), vec![0x41]);
    assert_eq!(encode_codepoint(0x7F), vec![0x7F]);
}

#[test]
fn encodes_two_byte_codepoints() {
    assert_eq!(encode_codepoint(0x80), vec![0xC2, 0x80]);
    assert_eq!(encode_codepoint(0xE9), vec![0xC3, 0xA9]);
    assert_eq!(encode_codepoint(0x7FF), vec![0xDF, 0xBF]);
}

#[test]
fn encodes_three_byte_codepoints() {
    assert_eq!(encode_codepoint(0x800), vec![0xE0, 0xA0, 0x80]);
    assert_eq!(encode_codepoint(0x4E2D), vec![0xE4, 0xB8, 0xAD]);
    assert_eq!(encode_codepoint(0xFFFF), vec![0xEF, 0xBF, 0xBF]);
}

#[test]
fn encodes_four_byte_codepoints() {
    assert_eq!(encode_codepoint(0x10000), vec![0xF0, 0x90, 0x80, 0x80]);
    assert_eq!(encode_codepoint(0x1F600), vec![0xF0, 0x9F, 0x98, 0x80]);
    assert_eq!(encode_codepoint(0x10FFFF), vec![0xF4, 0x8F, 0xBF, 0xBF]);
}

// ─────────────────────────────────────────────────────────────────────
// Roundtrips
// ─────────────────────────────────────────────────────────────────────

#[test]
fn roundtrips_mixed_codepoint_sequence() {
    // 'H', 'i', U+00E9 é, U+4E2D 中, U+6587 文, U+1F600 😀
    let cps = vec![0x48u32, 0x69, 0xE9, 0x4E2D, 0x6587, 0x1F600];
    let encoded = encode_codepoints(&cps);
    assert!(is_valid_utf8(&encoded));
    assert_eq!(decode_to_codepoints(&encoded), cps);
}

#[test]
fn roundtrips_byte_class_boundaries() {
    let boundaries: [u32; 10] = [
        0x00, 0x7F,         // 1-byte
        0x80, 0x7FF,        // 2-byte
        0x800, 0xD7FF,      // 3-byte just below surrogates
        0xE000, 0xFFFF,     // 3-byte just above surrogates
        0x10000, 0x10FFFF,  // 4-byte
    ];
    for cp in boundaries {
        let encoded = encode_codepoint(cp);
        assert!(is_valid_utf8(&encoded), "cp = U+{:04X}", cp);
        assert_eq!(decode_to_codepoints(&encoded), vec![cp]);
    }
}
