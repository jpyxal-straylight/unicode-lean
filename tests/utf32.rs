use unicode_rust::utf32::{
    decode_one_be, decode_one_le, encode_be, encode_le,
    encode_one_be, encode_one_le,
};

#[test]
fn encodes_ascii_be_le() {
    assert_eq!(encode_one_be(0x41), vec![0x00, 0x00, 0x00, 0x41]);
    assert_eq!(encode_one_le(0x41), vec![0x41, 0x00, 0x00, 0x00]);
}

#[test]
fn encodes_bmp_be_le() {
    assert_eq!(encode_one_be(0x4E2D), vec![0x00, 0x00, 0x4E, 0x2D]);
    assert_eq!(encode_one_le(0x4E2D), vec![0x2D, 0x4E, 0x00, 0x00]);
}

#[test]
fn encodes_supplementary_be_le() {
    assert_eq!(encode_one_be(0x1F600), vec![0x00, 0x01, 0xF6, 0x00]);
    assert_eq!(encode_one_le(0x1F600), vec![0x00, 0xF6, 0x01, 0x00]);
}

#[test]
fn encodes_u10ffff() {
    assert_eq!(encode_one_be(0x10FFFF), vec![0x00, 0x10, 0xFF, 0xFF]);
    assert_eq!(encode_one_le(0x10FFFF), vec![0xFF, 0xFF, 0x10, 0x00]);
}

#[test]
fn decodes_valid_scalars_be_le() {
    assert_eq!(decode_one_be(&[0x00, 0x00, 0x00, 0x41]), Some(0x41));
    assert_eq!(decode_one_le(&[0x41, 0x00, 0x00, 0x00]), Some(0x41));
}

#[test]
fn rejects_surrogates() {
    assert_eq!(decode_one_be(&[0x00, 0x00, 0xD8, 0x00]), None);
    assert_eq!(decode_one_le(&[0xFF, 0xDF, 0x00, 0x00]), None);
}

#[test]
fn rejects_beyond_max() {
    assert_eq!(decode_one_be(&[0x00, 0x11, 0x00, 0x00]), None);
    assert_eq!(decode_one_le(&[0x00, 0x00, 0x11, 0x00]), None);
}

#[test]
fn rejects_invalid_lengths() {
    for n in [0, 1, 2, 3, 5, 6, 8] {
        assert_eq!(decode_one_be(&vec![0u8; n]), None);
        assert_eq!(decode_one_le(&vec![0u8; n]), None);
    }
}

#[test]
fn roundtrips_boundaries() {
    for cp in [
        0x00u32, 0x7F, 0x80, 0xD7FF, 0xE000, 0xFFFF, 0x10000, 0x10FFFF,
    ] {
        assert_eq!(decode_one_be(&encode_one_be(cp)), Some(cp));
        assert_eq!(decode_one_le(&encode_one_le(cp)), Some(cp));
    }
}

#[test]
fn encodes_sequence_be() {
    let out = encode_be(&[0x41, 0x4E2D, 0x1F600]);
    assert_eq!(out.len(), 12);
    assert_eq!(&out[0..4], &[0x00, 0x00, 0x00, 0x41]);
    assert_eq!(&out[4..8], &[0x00, 0x00, 0x4E, 0x2D]);
    assert_eq!(&out[8..12], &[0x00, 0x01, 0xF6, 0x00]);
}

#[test]
fn encodes_sequence_le() {
    let out = encode_le(&[0x41, 0x4E2D, 0x1F600]);
    assert_eq!(out.len(), 12);
    assert_eq!(&out[0..4], &[0x41, 0x00, 0x00, 0x00]);
}
