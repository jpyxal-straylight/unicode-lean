//! Opaque text predicate — structurally valid UTF-8,
//! size-bounded.
//!
//! No character-class or codepoint filtering beyond UTF-8
//! validity.  Intended for callers who apply their own text
//! hardening downstream; hardened identifier and printable
//! profiles layer on top of this predicate.

use crate::utf8::is_valid_utf8;

/// Opaque-blob predicate: structurally valid UTF-8.  Exposed
/// under this name so the "blob" framing — no character-class
/// hardening — is explicit at the call site.
pub fn is_utf8_blob(bytes: &[u8]) -> bool {
    is_valid_utf8(bytes)
}

/// A byte sequence carrying its size bound and UTF-8 validity
/// claim.  The constructor is hidden; [`Utf8Blob::of`] is the only
/// entry point.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Utf8Blob {
    bytes: Vec<u8>,
    max_bytes: usize,
}

impl Utf8Blob {
    /// Build a `Utf8Blob` under the size bound `max_bytes`.
    /// Returns `None` when either the bound or UTF-8 validity is
    /// violated.
    pub fn of(bytes: Vec<u8>, max_bytes: usize) -> Option<Self> {
        if bytes.len() > max_bytes {
            return None;
        }
        if !is_utf8_blob(&bytes) {
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
