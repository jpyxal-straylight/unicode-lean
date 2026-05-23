use unicode_rust::opaque_blob::{is_utf8_blob, Utf8Blob};

#[test]
fn accepts_valid_utf8() {
    assert!(is_utf8_blob(b"Hi"));
    assert!(is_utf8_blob(&[0xC3, 0xA9]));
    assert!(is_utf8_blob(&[0xF0, 0x9F, 0x98, 0x80]));
}

#[test]
fn rejects_invalid_utf8() {
    assert!(!is_utf8_blob(&[0xC0, 0x80]));
    assert!(!is_utf8_blob(&[0xED, 0xA0, 0x80]));
}

#[test]
fn refinement_builds_within_bound() {
    let blob = Utf8Blob::of(b"Hi".to_vec(), 16).unwrap();
    assert_eq!(blob.bytes(), b"Hi");
    assert_eq!(blob.max_bytes(), 16);
}

#[test]
fn refinement_rejects_over_bound() {
    assert!(Utf8Blob::of(b"Hi!".to_vec(), 2).is_none());
}

#[test]
fn refinement_rejects_malformed_utf8() {
    assert!(Utf8Blob::of(vec![0xC0, 0x80], 16).is_none());
}

#[test]
fn refinement_accepts_empty_under_any_bound() {
    assert!(Utf8Blob::of(vec![], 32).is_some());
}
