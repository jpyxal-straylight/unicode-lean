//! Byte-Order-Mark detection across the five Unicode encodings.
//!
//!   UTF-8     : EF BB BF              (3 bytes)
//!   UTF-16 BE : FE FF                 (2 bytes)
//!   UTF-16 LE : FF FE                 (2 bytes)
//!   UTF-32 BE : 00 00 FE FF           (4 bytes)
//!   UTF-32 LE : FF FE 00 00           (4 bytes)
//!
//! Order matters: the UTF-32 BOMs share their leading bytes with
//! the UTF-16 BOMs, so the 4-byte patterns must be checked BEFORE
//! the 2-byte patterns.  Specifically, `FF FE 00 00` is a UTF-32
//! LE BOM, not a UTF-16 LE BOM followed by two NUL bytes.

/// The five Unicode encoding kinds distinguishable by their BOM.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BomKind {
    Utf8,
    Utf16BE,
    Utf16LE,
    Utf32BE,
    Utf32LE,
}

impl BomKind {
    /// The byte length of this BOM.
    pub fn len(self) -> usize {
        match self {
            BomKind::Utf8 => 3,
            BomKind::Utf16BE | BomKind::Utf16LE => 2,
            BomKind::Utf32BE | BomKind::Utf32LE => 4,
        }
    }
}

fn byte_at(bytes: &[u8], i: usize) -> u8 {
    bytes.get(i).copied().unwrap_or(0)
}

/// Detect a leading BOM, returning the encoding kind and the
/// number of BOM bytes to skip.  The 4-byte UTF-32 BOMs are tested
/// before the 2-byte UTF-16 BOMs.  Returns `None` if the input
/// does not begin with any recognised BOM.
pub fn detect(bytes: &[u8]) -> Option<(BomKind, usize)> {
    let b0 = byte_at(bytes, 0);
    let b1 = byte_at(bytes, 1);
    let b2 = byte_at(bytes, 2);
    let b3 = byte_at(bytes, 3);
    if bytes.len() >= 4 && b0 == 0x00 && b1 == 0x00 && b2 == 0xFE && b3 == 0xFF {
        return Some((BomKind::Utf32BE, 4));
    }
    if bytes.len() >= 4 && b0 == 0xFF && b1 == 0xFE && b2 == 0x00 && b3 == 0x00 {
        return Some((BomKind::Utf32LE, 4));
    }
    if bytes.len() >= 3 && b0 == 0xEF && b1 == 0xBB && b2 == 0xBF {
        return Some((BomKind::Utf8, 3));
    }
    if bytes.len() >= 2 && b0 == 0xFE && b1 == 0xFF {
        return Some((BomKind::Utf16BE, 2));
    }
    if bytes.len() >= 2 && b0 == 0xFF && b1 == 0xFE {
        return Some((BomKind::Utf16LE, 2));
    }
    None
}

/// Strip the BOM from `bytes` if one is present, returning the
/// remaining content together with the detected encoding.  When
/// the input does not begin with a recognised BOM the function
/// returns the input unchanged and `kind = None`.
pub fn strip(bytes: &[u8]) -> (Option<BomKind>, &[u8]) {
    match detect(bytes) {
        Some((kind, k)) => (Some(kind), &bytes[k..]),
        None => (None, bytes),
    }
}
