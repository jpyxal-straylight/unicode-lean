//! Detection of GlassWorm-class invisible payloads encoded in
//! Unicode variation selectors.
//!
//! Threat model.  Tier A1.  Adversary crafts an input consisting of
//! one visible base codepoint followed by a sequence of variation-
//! selector codepoints (U+FE00..U+FE0F union U+E0100..U+E01EF) that
//! the receiving renderer treats as a no-op glyph variant but that
//! a downstream string-processing layer (e.g. an LLM tokenizer or a
//! clipboard pipeline) preserves byte-for-byte.  Decoding pairs of
//! VS codepoints back into bytes recovers an arbitrary payload.
//!
//! This port treats every variation-selector occurrence after a
//! base codepoint as suspicious.  The Lean reference additionally
//! exempts (base, VS) pairs that appear in
//! `StandardizedVariants.txt` and emoji-presentation pairs — those
//! exemptions require UCD tables.

use crate::security::ClassificationKind;

pub fn is_variation_selector(cp: u32) -> bool {
    matches!(cp, 0xFE00..=0xFE0F | 0xE0100..=0xE01EF | 0x180B..=0x180D)
}

/// Decode a single VS codepoint to its nibble value in [0, 255].
/// Uses GlassWorm's bit layout: VS1..VS16 → nibbles 0..15,
/// VS17..VS256 → nibbles 16..255.  Mongolian FVS codepoints
/// (180B..180D) return `None`.
pub fn vs_to_nibble(cp: u32) -> Option<u32> {
    if (0xFE00..=0xFE0F).contains(&cp) {
        Some(cp - 0xFE00)
    } else if (0xE0100..=0xE01EF).contains(&cp) {
        Some(cp - 0xE0100 + 16)
    } else {
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SubThreat {
    DirectPayload { decoded: String },
    IllegalTarget { target_cp: u32, vs_cp: u32 },
    RepeatedBase { base_cp: u32, vs_count: usize },
}

impl SubThreat {
    pub fn tag(&self) -> &'static str {
        match self {
            SubThreat::DirectPayload { .. } => "DirectPayload",
            SubThreat::IllegalTarget { .. } => "IllegalTarget",
            SubThreat::RepeatedBase { .. } => "RepeatedBase",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Verdict {
    pub kind: ClassificationKind,
    pub sub: Option<SubThreat>,
    pub vs_positions: Vec<usize>,
    pub recovered_bytes: Vec<u8>,
}

fn decode_vs_run(input: &[u32], positions: &[usize]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut high: Option<u32> = None;
    for &p in positions {
        let n = match vs_to_nibble(input[p]) {
            Some(n) => n,
            None => continue,
        };
        match high {
            None => high = Some(n),
            Some(h) => {
                out.push(((h << 4) | n) as u8);
                high = None;
            }
        }
    }
    out
}

fn all_same_vs(input: &[u32], positions: &[usize]) -> bool {
    let cp0 = match positions.first() {
        Some(&p0) => input[p0],
        None => return true,
    };
    positions.iter().all(|&p| input[p] == cp0)
}

fn lossy_ascii(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(|&b| {
            if (0x20..=0x7E).contains(&b) || b == 0x09 || b == 0x0A || b == 0x0D {
                b as char
            } else {
                '?'
            }
        })
        .collect()
}

pub fn detect(input: &[u32]) -> Verdict {
    let mut v = Verdict {
        kind: ClassificationKind::Clear,
        sub: None,
        vs_positions: Vec::new(),
        recovered_bytes: Vec::new(),
    };
    v.vs_positions = input
        .iter()
        .enumerate()
        .filter_map(|(i, &cp)| if is_variation_selector(cp) { Some(i) } else { None })
        .collect();

    if v.vs_positions.is_empty() {
        return v;
    }

    v.recovered_bytes = decode_vs_run(input, &v.vs_positions);
    v.kind = ClassificationKind::Hazard;

    if v.vs_positions.len() >= 4 && all_same_vs(input, &v.vs_positions) {
        let p0 = v.vs_positions[0];
        let base = if p0 == 0 { 0 } else { input[p0 - 1] };
        v.sub = Some(SubThreat::RepeatedBase {
            base_cp: base,
            vs_count: v.vs_positions.len(),
        });
    } else if !v.recovered_bytes.is_empty() {
        v.sub = Some(SubThreat::DirectPayload {
            decoded: lossy_ascii(&v.recovered_bytes),
        });
    } else {
        let p = v.vs_positions[0];
        let target = if p == 0 { 0 } else { input[p - 1] };
        v.sub = Some(SubThreat::IllegalTarget {
            target_cp: target,
            vs_cp: input[p],
        });
    }
    v
}
