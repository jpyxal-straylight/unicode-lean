use unicode_rust::bom::{detect, strip, BomKind};

#[test]
fn returns_none_on_empty_input() {
    assert_eq!(detect(&[]), None);
}

#[test]
fn returns_none_on_non_bom_bytes() {
    assert_eq!(detect(&[0x41, 0x42, 0x43]), None);
}

#[test]
fn detects_utf8_bom() {
    assert_eq!(detect(&[0xEF, 0xBB, 0xBF]), Some((BomKind::Utf8, 3)));
}

#[test]
fn detects_utf16_be_bom() {
    assert_eq!(detect(&[0xFE, 0xFF]), Some((BomKind::Utf16BE, 2)));
}

#[test]
fn detects_utf16_le_bom_two_bytes() {
    assert_eq!(detect(&[0xFF, 0xFE]), Some((BomKind::Utf16LE, 2)));
}

#[test]
fn detects_utf32_be_bom() {
    assert_eq!(
        detect(&[0x00, 0x00, 0xFE, 0xFF]),
        Some((BomKind::Utf32BE, 4))
    );
}

#[test]
fn detects_utf32_le_precedence_over_utf16_le() {
    assert_eq!(
        detect(&[0xFF, 0xFE, 0x00, 0x00]),
        Some((BomKind::Utf32LE, 4))
    );
}

#[test]
fn detects_utf16_le_when_followed_by_nonzero() {
    assert_eq!(
        detect(&[0xFF, 0xFE, 0x41]),
        Some((BomKind::Utf16LE, 2))
    );
}

#[test]
fn reports_bomlength_for_each_kind() {
    assert_eq!(BomKind::Utf8.len(), 3);
    assert_eq!(BomKind::Utf16BE.len(), 2);
    assert_eq!(BomKind::Utf16LE.len(), 2);
    assert_eq!(BomKind::Utf32BE.len(), 4);
    assert_eq!(BomKind::Utf32LE.len(), 4);
}

#[test]
fn strip_returns_kind_and_rest() {
    let bytes = [0xEF, 0xBB, 0xBF, 0x48, 0x69];
    let (kind, rest) = strip(&bytes);
    assert_eq!(kind, Some(BomKind::Utf8));
    assert_eq!(rest, &[0x48, 0x69]);
}

#[test]
fn strip_passes_through_when_no_bom() {
    let bytes = [0x41, 0x42];
    let (kind, rest) = strip(&bytes);
    assert_eq!(kind, None);
    assert_eq!(rest, &bytes[..]);
}
