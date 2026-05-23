//! UTF-32 codec — big-endian and little-endian variants.
//!
//! Each scalar Unicode codepoint encodes to exactly 4 bytes; the
//! invariant is straight identity, no length-dependent escape
//! sequences.  The decoder rejects inputs whose length is not
//! exactly 4, 4-byte sequences encoding a surrogate codepoint
//! U+D800..U+DFFF, and 4-byte sequences encoding a value above
//! U+10FFFF.

/// Encode a scalar codepoint as 4 bytes in big-endian order.
pub fn encode_one_be(cp: u32) -> Vec<u8> {
    cp.to_be_bytes().to_vec()
}

/// Encode a scalar codepoint as 4 bytes in little-endian order.
pub fn encode_one_le(cp: u32) -> Vec<u8> {
    cp.to_le_bytes().to_vec()
}

fn scalar(cp: u32) -> Option<u32> {
    if cp > 0x10FFFF {
        return None;
    }
    if (0xD800..=0xDFFF).contains(&cp) {
        return None;
    }
    Some(cp)
}

/// Decode 4 bytes as a big-endian UTF-32 codepoint.
///
/// Returns `None` when the length is not exactly 4, the decoded
/// value is a surrogate, or the value exceeds U+10FFFF.
pub fn decode_one_be(bytes: &[u8]) -> Option<u32> {
    if bytes.len() != 4 {
        return None;
    }
    let cp = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    scalar(cp)
}

/// Decode 4 bytes as a little-endian UTF-32 codepoint.
pub fn decode_one_le(bytes: &[u8]) -> Option<u32> {
    if bytes.len() != 4 {
        return None;
    }
    let cp = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    scalar(cp)
}

/// Concatenate the UTF-32 BE encodings of a codepoint sequence.
pub fn encode_be(cps: &[u32]) -> Vec<u8> {
    let mut out = Vec::with_capacity(cps.len() * 4);
    for &cp in cps {
        out.extend(encode_one_be(cp));
    }
    out
}

/// Concatenate the UTF-32 LE encodings of a codepoint sequence.
pub fn encode_le(cps: &[u32]) -> Vec<u8> {
    let mut out = Vec::with_capacity(cps.len() * 4);
    for &cp in cps {
        out.extend(encode_one_le(cp));
    }
    out
}
