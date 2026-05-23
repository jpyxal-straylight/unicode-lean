use unicode_rust::noncharacters::{all_noncharacters, is_noncharacter};

#[test]
fn flags_bmp_block() {
    for cp in 0xFDD0u32..=0xFDEFu32 {
        assert!(is_noncharacter(cp), "U+{:04X}", cp);
    }
}

#[test]
fn flags_plane_ends() {
    for n in 0u32..=16u32 {
        assert!(is_noncharacter(n * 0x10000 + 0xFFFE));
        assert!(is_noncharacter(n * 0x10000 + 0xFFFF));
    }
}

#[test]
fn rejects_ascii() {
    for cp in [0x00u32, 0x41, 0x7F] {
        assert!(!is_noncharacter(cp));
    }
}

#[test]
fn rejects_adjacent_to_fddx_block() {
    assert!(!is_noncharacter(0xFDCF));
    assert!(!is_noncharacter(0xFDF0));
}

#[test]
fn rejects_replacement_character() {
    assert!(!is_noncharacter(0xFFFD));
}

#[test]
fn rejects_codepoints_above_max() {
    assert!(!is_noncharacter(0x110000));
    assert!(!is_noncharacter(0x10FFFF + 0xFFFF));
}

#[test]
fn enumerates_exactly_66() {
    assert_eq!(all_noncharacters().len(), 66);
}

#[test]
fn enumeration_is_ascending() {
    let all = all_noncharacters();
    for w in all.windows(2) {
        assert!(w[0] < w[1]);
    }
}

#[test]
fn every_enumerated_satisfies_predicate() {
    for cp in all_noncharacters() {
        assert!(is_noncharacter(cp), "U+{:04X}", cp);
    }
}
