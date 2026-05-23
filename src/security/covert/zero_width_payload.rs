//! Detection of payloads encoded in zero-width and near-zero-width
//! Unicode codepoints.
//!
//! Threat model.  Tier A1.  Adversary embeds zero-width / no-glyph
//! codepoints inside otherwise-normal text to carry a covert binary
//! payload, to splice WORD JOINER / byte-order-mark sequences into
//! identifiers, or to emit a suspected AI-watermark NNBSP pattern.
//!
//! This port treats every zero-width occurrence as reportable.  The
//! Lean reference additionally exempts ZWJ flanked by emoji
//! codepoints (RGI-context legitimate emoji-ZWJ sequence) — that
//! exemption requires the UCD emoji-data table.

use crate::security::ClassificationKind;

pub fn is_zero_width(cp: u32) -> bool {
    matches!(cp, 0x200B..=0x200F | 0x2060..=0x2064 | 0x202F | 0xFEFF | 0xFFF9..=0xFFFB)
}

pub fn is_nnbsp(cp: u32) -> bool {
    cp == 0x202F
}

pub fn is_word_joiner(cp: u32) -> bool {
    cp == 0x2060
}

pub fn is_annotation(cp: u32) -> bool {
    (0xFFF9..=0xFFFB).contains(&cp)
}

pub fn is_zwj_or_zwsp(cp: u32) -> bool {
    cp == 0x200B || cp == 0x200D
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SubThreat {
    AnnotationMisuse { count: usize },
    WordJoinerInjection { count: usize },
    AiWatermarkNNBSP { count: usize },
    BinaryPayload { pair_count: usize },
    BareZeroWidth { cp: u32 },
}

impl SubThreat {
    pub fn tag(&self) -> &'static str {
        match self {
            SubThreat::AnnotationMisuse { .. } => "AnnotationMisuse",
            SubThreat::WordJoinerInjection { .. } => "WordJoinerInjection",
            SubThreat::AiWatermarkNNBSP { .. } => "AiWatermarkNNBSP",
            SubThreat::BinaryPayload { .. } => "BinaryPayload",
            SubThreat::BareZeroWidth { .. } => "BareZeroWidth",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Verdict {
    pub kind: ClassificationKind,
    pub sub: Option<SubThreat>,
    pub zero_width_positions: Vec<usize>,
}

pub fn detect(input: &[u32]) -> Verdict {
    let mut v = Verdict {
        kind: ClassificationKind::Clear,
        sub: None,
        zero_width_positions: Vec::new(),
    };
    let mut annotation_count = 0;
    let mut word_joiner_count = 0;
    let mut nnbsp_count = 0;
    let mut zwj_zwsp_count = 0;

    for (i, &cp) in input.iter().enumerate() {
        if !is_zero_width(cp) {
            continue;
        }
        v.zero_width_positions.push(i);
        if is_annotation(cp) {
            annotation_count += 1;
        } else if is_word_joiner(cp) {
            word_joiner_count += 1;
        } else if is_nnbsp(cp) {
            nnbsp_count += 1;
        } else if is_zwj_or_zwsp(cp) {
            zwj_zwsp_count += 1;
        }
    }

    if v.zero_width_positions.is_empty() {
        return v;
    }

    v.kind = ClassificationKind::Hazard;
    if annotation_count > 0 {
        v.sub = Some(SubThreat::AnnotationMisuse {
            count: annotation_count,
        });
    } else if word_joiner_count > 0 {
        v.sub = Some(SubThreat::WordJoinerInjection {
            count: word_joiner_count,
        });
    } else if nnbsp_count >= 2 {
        v.sub = Some(SubThreat::AiWatermarkNNBSP { count: nnbsp_count });
    } else if zwj_zwsp_count >= 2 {
        v.sub = Some(SubThreat::BinaryPayload {
            pair_count: zwj_zwsp_count / 2,
        });
    } else {
        v.sub = Some(SubThreat::BareZeroWidth {
            cp: input[v.zero_width_positions[0]],
        });
    }
    v
}
