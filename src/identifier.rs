//! Strict ASCII identifier predicate — `[a-zA-Z_][a-zA-Z0-9_]*`.
//!
//!   - The first byte MUST be in 0x41..0x5A (A–Z),
//!     0x61..0x7A (a–z), or 0x5F (_).
//!   - Subsequent bytes MUST be in the first-byte set OR
//!     0x30..0x39 (0–9).
//!   - Empty byte sequences are REJECTED.
//!
//! The codec stays strict ASCII permanently.  Callers needing
//! Unicode identifiers route through a PRECIS identifier codec
//! (RFC 8264 / 8265) layered on top, providing defense-in-depth:
//! an ASCII belt plus PRECIS suspenders.

/// Whether `b` may start an ASCII identifier: A–Z, a–z, or `_`.
pub fn is_identifier_start_byte(b: u8) -> bool {
    (0x41..=0x5A).contains(&b) || (0x61..=0x7A).contains(&b) || b == 0x5F
}

/// Whether `b` may continue an ASCII identifier: the start-byte
/// set plus 0–9.
pub fn is_identifier_continue_byte(b: u8) -> bool {
    is_identifier_start_byte(b) || (0x30..=0x39).contains(&b)
}

/// Walk the continuation positions of `bytes` starting at `from`,
/// returning the offset and value of the first byte that fails
/// `is_identifier_continue_byte`.  Returns `None` when every
/// position from `from` onward is a valid continuation byte.
pub fn first_invalid_identifier_continue_from(
    bytes: &[u8],
    from: usize,
) -> Option<(usize, u8)> {
    for (idx, &b) in bytes.iter().enumerate().skip(from) {
        if !is_identifier_continue_byte(b) {
            return Some((idx, b));
        }
    }
    None
}

/// ASCII-identifier predicate: non-empty, valid start byte at
/// position zero, and every subsequent byte a valid continuation
/// byte.
pub fn is_valid_identifier_bytes(bytes: &[u8]) -> bool {
    if bytes.is_empty() {
        return false;
    }
    if !is_identifier_start_byte(bytes[0]) {
        return false;
    }
    first_invalid_identifier_continue_from(bytes, 1).is_none()
}

/// A byte sequence carrying its size bound and identifier-validity
/// claim.  The constructor is hidden; [`IdentifierUtf8::of`] is
/// the only entry point.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IdentifierUtf8 {
    bytes: Vec<u8>,
    max_bytes: usize,
}

impl IdentifierUtf8 {
    /// Build an `IdentifierUtf8` under the size bound `max_bytes`.
    /// Returns `None` when either the bound or identifier
    /// validity is violated.
    pub fn of(bytes: Vec<u8>, max_bytes: usize) -> Option<Self> {
        if bytes.len() > max_bytes {
            return None;
        }
        if !is_valid_identifier_bytes(&bytes) {
            return None;
        }
        Some(Self { bytes, max_bytes })
    }

    /// The underlying bytes.
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// The declared size bound.
    pub fn max_bytes(&self) -> usize {
        self.max_bytes
    }
}
