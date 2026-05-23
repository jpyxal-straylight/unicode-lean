//! Refinement type for bytes validated as strict RFC 3629 UTF-8.
//!
//! The validity claim is pinned at the module-boundary level: the
//! only way to construct a `ValidatedUtf8` is via the smart
//! constructor [`ValidatedUtf8::validate`], which routes through
//! the strict decoder state machine.
//!
//! Rationale: the ingestion layer is security-critical.  A plain
//! `Vec<u8>` field on a codec output type carries no claim about
//! its UTF-8 validity — downstream consumers have to either
//! re-validate or trust the producer.  `ValidatedUtf8` makes the
//! claim module-level, so a downstream consumer that wants the
//! raw bytes has to explicitly `into_bytes` — which reads as "I
//! am consuming the RFC 3629 claim here".

use crate::utf8::is_valid_utf8;

/// A `Vec<u8>` that has been validated as strict RFC 3629 UTF-8.
/// The constructor is intentionally private;
/// [`ValidatedUtf8::validate`] is the only blessed way to build a
/// `ValidatedUtf8`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ValidatedUtf8 {
    bytes: Vec<u8>,
}

impl ValidatedUtf8 {
    /// Validate a byte vector and, on success, return a
    /// `ValidatedUtf8` carrying the RFC 3629 validity claim.
    /// Returns `None` when the bytes fail the strict state
    /// machine.
    pub fn validate(bytes: Vec<u8>) -> Option<Self> {
        if is_valid_utf8(&bytes) {
            Some(Self { bytes })
        } else {
            None
        }
    }

    /// Borrow the validated bytes.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Consume the validity claim, returning the underlying
    /// bytes.  After this call the validity claim is no longer
    /// carried at the module-boundary level — the caller owns the
    /// "these bytes are RFC 3629 valid" reasoning from here
    /// forward.
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}
