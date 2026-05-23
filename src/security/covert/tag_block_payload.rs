//! Detection of invisible payloads encoded in the Unicode tag
//! block U+E0000..U+E007F.
//!
//! Threat model.  Tier A1 (local injector).  Adversary crafts an
//! input containing tag-block codepoints that pass through string
//! processing pipelines as zero-width / no-glyph characters but
//! carry a recoverable ASCII payload under the decoder
//!
//!   tag(c) = c + 0xE0000 for c in [0x20, 0x7E].
//!
//! No tag-block codepoint has a legitimate visible glyph or a
//! registered clean use in modern Unicode.  Every occurrence is
//! reportable; the detector's job is to attribute the kind of use
//! (direct payload, language-tag prefix, mixed-in-with-text, or
//! isolated single tag).

use crate::security::ClassificationKind;

/// True iff `cp` is in the Unicode tag block U+E0000..U+E007F.
pub fn is_tag_character(cp: u32) -> bool {
    (0xE0000..=0xE007F).contains(&cp)
}

pub fn is_language_tag(cp: u32) -> bool {
    cp == 0xE0001
}

pub fn is_cancel_tag(cp: u32) -> bool {
    cp == 0xE007F
}

/// Decode a tag-block codepoint to its ASCII correspondent.
/// Returns `None` for tag codepoints outside the printable-ASCII
/// range and for any non-tag codepoint.
pub fn tag_to_ascii(cp: u32) -> Option<char> {
    if (0xE0020..=0xE007E).contains(&cp) {
        char::from_u32(cp - 0xE0000)
    } else {
        None
    }
}

/// Sub-threat variants.  Priority order (highest first):
///
///   1. [`SubThreat::LanguageTagRevival`] — E0001 followed by ≥ 1
///      further tag char.
///   2. [`SubThreat::DirectAscii`] — input is pure tags and
///      decoder produces ≥ 1 printable byte.
///   3. [`SubThreat::MixedBlock`] — tag chars interleaved with
///      non-tag codepoints.
///   4. [`SubThreat::BareTagPresent`] — fallback for isolated
///      single tag-block codepoints.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SubThreat {
    DirectAscii {
        decoded: String,
    },
    LanguageTagRevival {
        lang_tag_pos: usize,
        decoded_tail: String,
    },
    MixedBlock {
        tag_count: usize,
        total_cps: usize,
    },
    BareTagPresent {
        tag_cp: u32,
    },
}

impl SubThreat {
    /// Fixture-row tag string for each variant.
    pub fn tag(&self) -> &'static str {
        match self {
            SubThreat::DirectAscii { .. } => "DirectAscii",
            SubThreat::LanguageTagRevival { .. } => "LanguageTagRevival",
            SubThreat::MixedBlock { .. } => "MixedBlock",
            SubThreat::BareTagPresent { .. } => "BareTagPresent",
        }
    }
}

/// Structured verdict over an input codepoint sequence.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Verdict {
    pub kind: ClassificationKind,
    pub sub: Option<SubThreat>,
    pub tag_positions: Vec<usize>,
    pub recovered_ascii: String,
}

fn decode_tag_run(input: &[u32], positions: &[usize]) -> String {
    let mut s = String::new();
    for &p in positions {
        if p < input.len() {
            if let Some(c) = tag_to_ascii(input[p]) {
                s.push(c);
            }
        }
    }
    s
}

fn has_language_tag_prefix(input: &[u32], tag_positions: &[usize]) -> Option<usize> {
    let lang_pos = *tag_positions.first()?;
    if lang_pos >= input.len() {
        return None;
    }
    if is_language_tag(input[lang_pos]) && tag_positions.len() >= 2 {
        Some(lang_pos)
    } else {
        None
    }
}

fn pick_sub_threat(input: &[u32], tag_positions: &[usize], decoded: &str) -> SubThreat {
    if let Some(lang_pos) = has_language_tag_prefix(input, tag_positions) {
        let tail: Vec<usize> = tag_positions
            .iter()
            .copied()
            .filter(|&p| p != lang_pos)
            .collect();
        return SubThreat::LanguageTagRevival {
            lang_tag_pos: lang_pos,
            decoded_tail: decode_tag_run(input, &tail),
        };
    }
    if input.iter().all(|&cp| is_tag_character(cp)) && !decoded.is_empty() {
        return SubThreat::DirectAscii {
            decoded: decoded.to_string(),
        };
    }
    if input.len() > tag_positions.len() {
        return SubThreat::MixedBlock {
            tag_count: tag_positions.len(),
            total_cps: input.len(),
        };
    }
    SubThreat::BareTagPresent {
        tag_cp: input[tag_positions[0]],
    }
}

/// The TagBlockPayload detection function.  Returns a structured
/// verdict over the codepoint sequence `input`.
pub fn detect(input: &[u32]) -> Verdict {
    let tag_positions: Vec<usize> = input
        .iter()
        .enumerate()
        .filter_map(|(i, &cp)| if is_tag_character(cp) { Some(i) } else { None })
        .collect();

    if tag_positions.is_empty() {
        return Verdict {
            kind: ClassificationKind::Clear,
            sub: None,
            tag_positions: vec![],
            recovered_ascii: String::new(),
        };
    }

    let decoded = decode_tag_run(input, &tag_positions);
    let sub = pick_sub_threat(input, &tag_positions, &decoded);

    Verdict {
        kind: ClassificationKind::Hazard,
        sub: Some(sub),
        tag_positions,
        recovered_ascii: decoded,
    }
}
