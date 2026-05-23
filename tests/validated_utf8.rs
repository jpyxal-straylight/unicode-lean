use unicode_rust::ValidatedUtf8;

#[test]
fn validates_valid_input() {
    assert!(ValidatedUtf8::validate(b"Hi".to_vec()).is_some());
}

#[test]
fn rejects_overlong_nul() {
    assert!(ValidatedUtf8::validate(vec![0xC0, 0x80]).is_none());
}

#[test]
fn rejects_surrogate_codepoint() {
    assert!(ValidatedUtf8::validate(vec![0xED, 0xA0, 0x80]).is_none());
}

#[test]
fn rejects_codepoint_beyond_max() {
    assert!(ValidatedUtf8::validate(vec![0xF4, 0x90, 0x80, 0x80]).is_none());
}

#[test]
fn rejects_truncated_sequence() {
    assert!(ValidatedUtf8::validate(vec![0xC2]).is_none());
}

#[test]
fn as_bytes_borrows_the_validated_bytes() {
    let v = ValidatedUtf8::validate(b"Hi".to_vec()).unwrap();
    assert_eq!(v.as_bytes(), b"Hi");
}

#[test]
fn into_bytes_consumes_the_claim() {
    let v = ValidatedUtf8::validate(b"Hi".to_vec()).unwrap();
    let bytes = v.into_bytes();
    assert_eq!(bytes, b"Hi");
}

#[test]
fn roundtrips_empty_input() {
    let v = ValidatedUtf8::validate(vec![]).unwrap();
    assert!(v.as_bytes().is_empty());
}
