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
//! Exempts (base, VS) pairs that appear in
//! `StandardizedVariants.txt` (1127 registered variation
//! sequences) and `emoji-variation-sequences.txt` (371 emoji
//! presentation pairs) per UCD 17.0 / UTS #51.  Without this
//! exemption the detector false-positives on legitimate East-
//! Asian text containing CJK Compatibility Ideograph + VS pairs
//! and registered math-symbol variants — a state-level credibility
//! issue for banking / govt deployments processing CJK identifiers.

use std::collections::HashSet;
use std::sync::OnceLock;

use crate::security::ClassificationKind;

// ──────────────────────────────────────────────────────────────────────
// Authoritative legal (base, VS) pair set
// ──────────────────────────────────────────────────────────────────────

const STANDARDIZED_VARIANTS_RAW: &str =
    include_str!("../../../data/StandardizedVariants.txt");
const EMOJI_VARIATION_SEQUENCES_RAW: &str =
    include_str!("../../../data/emoji-variation-sequences.txt");

fn parse_hex_u32(s: &str) -> Option<u32> {
    u32::from_str_radix(s.trim(), 16).ok()
}

fn parse_legal_pairs() -> HashSet<(u32, u32)> {
    let mut out = HashSet::new();
    for source in [STANDARDIZED_VARIANTS_RAW, EMOJI_VARIATION_SEQUENCES_RAW] {
        for raw_line in source.lines() {
            let body = match raw_line.find('#') {
                Some(idx) => &raw_line[..idx],
                None => raw_line,
            };
            let stripped = body.trim();
            if stripped.is_empty() {
                continue;
            }
            // Format: "<base-hex> <vs-hex>; <description>" — we only
            // need the first two whitespace-separated hex tokens
            // before the ';'.
            let semi_idx = stripped.find(';').unwrap_or(stripped.len());
            let pair_part = &stripped[..semi_idx];
            let mut tokens = pair_part.split_whitespace();
            let (Some(base_str), Some(vs_str)) = (tokens.next(), tokens.next())
            else {
                continue;
            };
            let (Some(base), Some(vs)) =
                (parse_hex_u32(base_str), parse_hex_u32(vs_str))
            else {
                continue;
            };
            out.insert((base, vs));
        }
    }
    out
}

/// True iff `(base, vs)` is a registered variation sequence per
/// UCD 17.0 StandardizedVariants.txt or UTS #51
/// emoji-variation-sequences.txt.  Used to exempt legitimate
/// CJK Compatibility / math / emoji-presentation variants from
/// IllegalTarget false-positives.
pub fn is_registered_variation_pair(base: u32, vs: u32) -> bool {
    static SET: OnceLock<HashSet<(u32, u32)>> = OnceLock::new();
    SET.get_or_init(parse_legal_pairs).contains(&(base, vs))
}

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

    // Single-VS exemption: if the entire VS run is exactly ONE
    // VS codepoint following a base, and that (base, VS) pair is
    // registered in StandardizedVariants or emoji-variation-
    // sequences, the input is a legitimate registered variation
    // (e.g. CJK Compatibility Ideograph + FE00, registered math
    // variant, or emoji-style/text-style selector).  Return Clear.
    if v.vs_positions.len() == 1 {
        let p = v.vs_positions[0];
        if p > 0 {
            let base = input[p - 1];
            let vs = input[p];
            if is_registered_variation_pair(base, vs) {
                // Legitimate variant — leave verdict Clear.
                return v;
            }
        }
    }

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
