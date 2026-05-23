use unicode_rust::identifier::{
    first_invalid_identifier_continue_from,
    is_identifier_continue_byte,
    is_identifier_start_byte,
    is_valid_identifier_bytes,
    IdentifierUtf8,
};

#[test]
fn accepts_start_bytes() {
    for c in b"AZazMno_" {
        assert!(is_identifier_start_byte(*c));
    }
}

#[test]
fn rejects_digits_and_punctuation_as_start() {
    for c in b"0123-.@$" {
        assert!(!is_identifier_start_byte(*c));
    }
}

#[test]
fn accepts_continue_bytes() {
    for c in b"Az_09" {
        assert!(is_identifier_continue_byte(*c));
    }
}

#[test]
fn rejects_punctuation_as_continue() {
    for c in b"-.@$ " {
        assert!(!is_identifier_continue_byte(*c));
    }
}

#[test]
fn rejects_empty_input() {
    assert!(!is_valid_identifier_bytes(b""));
}

#[test]
fn accepts_single_underscore() {
    assert!(is_valid_identifier_bytes(b"_"));
}

#[test]
fn accepts_typical_identifiers() {
    for s in ["x", "foo", "foo_bar", "X123", "_x9"] {
        assert!(is_valid_identifier_bytes(s.as_bytes()), "{}", s);
    }
}

#[test]
fn rejects_starting_with_digit() {
    assert!(!is_valid_identifier_bytes(b"1abc"));
}

#[test]
fn rejects_punctuation_inside() {
    for s in ["foo-bar", "a.b", "a@b", "a b"] {
        assert!(!is_valid_identifier_bytes(s.as_bytes()), "{}", s);
    }
}

#[test]
fn rejects_non_ascii_bytes() {
    assert!(!is_valid_identifier_bytes(&[0x80]));
    assert!(!is_valid_identifier_bytes(&[0x41, 0xC2, 0xA0]));
}

#[test]
fn walker_returns_none_on_all_valid() {
    assert_eq!(
        first_invalid_identifier_continue_from(b"abc123", 1),
        None
    );
}

#[test]
fn walker_returns_first_invalid_offset() {
    assert_eq!(
        first_invalid_identifier_continue_from(b"foo-bar", 1),
        Some((3, b'-'))
    );
}

#[test]
fn refinement_builds_when_valid_and_within_bound() {
    let id = IdentifierUtf8::of(b"foo".to_vec(), 16).unwrap();
    assert_eq!(id.bytes(), b"foo");
    assert_eq!(id.max_bytes(), 16);
}

#[test]
fn refinement_rejects_over_bound() {
    assert!(IdentifierUtf8::of(b"foo_bar".to_vec(), 4).is_none());
}

#[test]
fn refinement_rejects_invalid() {
    assert!(IdentifierUtf8::of(b"1abc".to_vec(), 16).is_none());
}
