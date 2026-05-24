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
use crate::security::identity::ucd;

/// Sibling-detector codepoint ranges — these ARE Default_Ignorable
/// per UAX #44 but are dispatched by their own family detector
/// for richer payload-decoding / bidi-stack tracking, so we
/// EXCLUDE them from the ZW set to avoid double-counting.
///
///   - U+FE00..U+FE0F      VariationSelectorPayload
///   - U+E0100..U+E01EF    VariationSelectorPayload
///   - U+E0000..U+E007F    TagBlockPayload
///   - U+202A..U+202E      BidiControlBalance (LRE/RLE/PDF/LRO/RLO)
///   - U+2066..U+2069      BidiControlBalance (LRI/RLI/FSI/PDI)
///
/// LRM / RLM (U+200E / U+200F) are NOT excluded — they're
/// direction markers, not push/pop bidi controls, and
/// BidiControlBalance doesn't track them.
fn is_sibling_handled(cp: u32) -> bool {
    matches!(cp,
        0xFE00..=0xFE0F
      | 0xE0100..=0xE01EF
      | 0xE0000..=0xE007F
      | 0x202A..=0x202E
      | 0x2066..=0x2069
    )
}

/// True iff `cp` is a Unicode codepoint that renders as nothing
/// OR is in the explicit "tracked zero-width" set (ZWSP, ZWNJ,
/// ZWJ, LRM, RLM, WJ, NNBSP, BOM, annotations).
///
/// The explicit hardcoded list is preserved so existing
/// sub-threat dispatch (NNBSP / WordJoiner / Annotation /
/// BareZeroWidth) reads exactly as before for those codepoints.
/// The UAX #44 Default_Ignorable_Code_Point predicate is the
/// EXTENSION that catches every other invisible codepoint (soft
/// hyphen, CGJ, ALM, Hangul fillers, Mongolian VS / vowel
/// separator, INHIBIT/ACTIVATE controls, shorthand format,
/// music format, etc.).  Sibling-detector ranges are excluded.
pub fn is_zero_width(cp: u32) -> bool {
    // Explicit historical set — preserves sub-threat dispatch.
    if matches!(cp,
        0x200B..=0x200F
      | 0x2060..=0x2064
      | 0x202F
      | 0xFEFF
      | 0xFFF9..=0xFFFB
    ) {
        return true;
    }
    // UAX #44 Default_Ignorable_Code_Point — catches everything
    // else invisible, modulo sibling-detector ranges.
    ucd::is_default_ignorable(cp) && !is_sibling_handled(cp)
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
