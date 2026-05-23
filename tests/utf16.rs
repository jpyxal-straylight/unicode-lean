use unicode_rust::utf16::{
    decode_one_be, decode_one_le, encode_be, encode_le,
    encode_one_be, encode_one_le,
};

#[test]
fn encodes_ascii_bmp_be_le() {
    assert_eq!(encode_one_be(0x0041), vec![0x00, 0x41]);
    assert_eq!(encode_one_le(0x0041), vec![0x41, 0x00]);
}

#[test]
fn encodes_supplementary_plane() {
    assert_eq!(
        encode_one_be(0x1F600),
        vec![0xD8, 0x3D, 0xDE, 0x00],
    );
    assert_eq!(
        encode_one_le(0x1F600),
        vec![0x3D, 0xD8, 0x00, 0xDE],
    );
}

#[test]
fn encodes_u10ffff_as_maximal_pair() {
    assert_eq!(
        encode_one_be(0x10FFFF),
        vec![0xDB, 0xFF, 0xDF, 0xFF],
    );
}

#[test]
fn decodes_bmp_be_le() {
    assert_eq!(decode_one_be(&[0x00, 0x41]), Some(0x0041));
    assert_eq!(decode_one_le(&[0x41, 0x00]), Some(0x0041));
}

#[test]
fn decodes_supplementary_pair() {
    assert_eq!(
        decode_one_be(&[0xD8, 0x3D, 0xDE, 0x00]),
        Some(0x1F600)
    );
    assert_eq!(
        decode_one_le(&[0x3D, 0xD8, 0x00, 0xDE]),
        Some(0x1F600)
    );
}

#[test]
fn rejects_lone_high_surrogate() {
    assert_eq!(decode_one_be(&[0xD8, 0x00]), None);
    assert_eq!(decode_one_le(&[0x00, 0xD8]), None);
}

#[test]
fn rejects_lone_low_surrogate() {
    assert_eq!(decode_one_be(&[0xDC, 0x00]), None);
}

#[test]
fn rejects_high_followed_by_non_low() {
    assert_eq!(
        decode_one_be(&[0xD8, 0x00, 0x00, 0x42]),
        None
    );
}

#[test]
fn rejects_invalid_lengths() {
    for n in [0, 1, 3, 5, 6] {
        assert_eq!(decode_one_be(&vec![0u8; n]), None);
        assert_eq!(decode_one_le(&vec![0u8; n]), None);
    }
}

#[test]
fn roundtrips_boundaries() {
    for cp in [
        0x0000u32, 0x007F, 0x0080, 0xD7FF, 0xE000, 0xFFFD,
        0x10000, 0x1F600, 0x10FFFD, 0x10FFFF,
    ] {
        assert_eq!(decode_one_be(&encode_one_be(cp)), Some(cp));
        assert_eq!(decode_one_le(&encode_one_le(cp)), Some(cp));
    }
}

#[test]
fn encodes_mixed_sequence_be() {
    assert_eq!(
        encode_be(&[0x0041, 0x1F600]),
        vec![0x00, 0x41, 0xD8, 0x3D, 0xDE, 0x00],
    );
}

#[test]
fn encodes_mixed_sequence_le() {
    assert_eq!(
        encode_le(&[0x0041, 0x1F600]),
        vec![0x41, 0x00, 0x3D, 0xD8, 0x00, 0xDE],
    );
}
