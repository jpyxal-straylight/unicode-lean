//! UTF-16 codec — big-endian and little-endian variants.
//!
//! Each scalar Unicode codepoint encodes to either 2 bytes (BMP)
//! or 4 bytes (supplementary planes via surrogate pair).  The
//! supplementary pair is constructed as
//!
//!   X    = cp - 0x10000          (20-bit value)
//!   high = 0xD800 + (X >> 10)    (high surrogate, 0xD800..0xDBFF)
//!   low  = 0xDC00 + (X & 0x3FF)  (low  surrogate, 0xDC00..0xDFFF)
//!
//! The decoder rejects inputs whose length is not exactly 2 or 4,
//! 2-byte sequences in the surrogate range U+D800..U+DFFF (lone
//! surrogate), and 4-byte sequences not forming a valid
//! (high, low) surrogate pair.

/// Encode a scalar codepoint as 2 or 4 bytes in big-endian UTF-16.
///
/// The function trusts its input: codepoints outside the valid
/// scalar range (0..0x10FFFF minus surrogates) produce bogus
/// output.  The decoder rejects them.
pub fn encode_one_be(cp: u32) -> Vec<u8> {
    if cp < 0x10000 {
        return vec![((cp >> 8) & 0xFF) as u8, (cp & 0xFF) as u8];
    }
    let x = cp - 0x10000;
    let high = 0xD800 + (x >> 10);
    let low = 0xDC00 + (x & 0x3FF);
    vec![
        ((high >> 8) & 0xFF) as u8,
        (high & 0xFF) as u8,
        ((low >> 8) & 0xFF) as u8,
        (low & 0xFF) as u8,
    ]
}

/// Encode a scalar codepoint as 2 or 4 bytes in little-endian UTF-16.
pub fn encode_one_le(cp: u32) -> Vec<u8> {
    if cp < 0x10000 {
        return vec![(cp & 0xFF) as u8, ((cp >> 8) & 0xFF) as u8];
    }
    let x = cp - 0x10000;
    let high = 0xD800 + (x >> 10);
    let low = 0xDC00 + (x & 0x3FF);
    vec![
        (high & 0xFF) as u8,
        ((high >> 8) & 0xFF) as u8,
        (low & 0xFF) as u8,
        ((low >> 8) & 0xFF) as u8,
    ]
}

fn scalar_from_pair(high: u32, low: u32) -> Option<u32> {
    if !(0xD800..=0xDBFF).contains(&high) {
        return None;
    }
    if !(0xDC00..=0xDFFF).contains(&low) {
        return None;
    }
    Some(0x10000 + ((high - 0xD800) << 10) + (low - 0xDC00))
}

/// Decode a UTF-16 BE byte sequence as a single codepoint.
///
/// Returns `None` on length mismatch, lone surrogate, or invalid
/// surrogate pair.  Accepts byte sequences of length exactly 2
/// (BMP) or 4 (supplementary-plane surrogate pair).
pub fn decode_one_be(bytes: &[u8]) -> Option<u32> {
    match bytes.len() {
        2 => {
            let u = ((bytes[0] as u32) << 8) | (bytes[1] as u32);
            if (0xD800..=0xDFFF).contains(&u) {
                None
            } else {
                Some(u)
            }
        }
        4 => {
            let high = ((bytes[0] as u32) << 8) | (bytes[1] as u32);
            let low = ((bytes[2] as u32) << 8) | (bytes[3] as u32);
            scalar_from_pair(high, low)
        }
        _ => None,
    }
}

/// Decode a UTF-16 LE byte sequence as a single codepoint.
pub fn decode_one_le(bytes: &[u8]) -> Option<u32> {
    match bytes.len() {
        2 => {
            let u = (bytes[0] as u32) | ((bytes[1] as u32) << 8);
            if (0xD800..=0xDFFF).contains(&u) {
                None
            } else {
                Some(u)
            }
        }
        4 => {
            let high = (bytes[0] as u32) | ((bytes[1] as u32) << 8);
            let low = (bytes[2] as u32) | ((bytes[3] as u32) << 8);
            scalar_from_pair(high, low)
        }
        _ => None,
    }
}

/// Concatenate the UTF-16 BE encodings of a codepoint sequence.
pub fn encode_be(cps: &[u32]) -> Vec<u8> {
    let mut out = Vec::with_capacity(cps.len() * 2);
    for &cp in cps {
        out.extend(encode_one_be(cp));
    }
    out
}

/// Concatenate the UTF-16 LE encodings of a codepoint sequence.
pub fn encode_le(cps: &[u32]) -> Vec<u8> {
    let mut out = Vec::with_capacity(cps.len() * 2);
    for &cp in cps {
        out.extend(encode_one_le(cp));
    }
    out
}
