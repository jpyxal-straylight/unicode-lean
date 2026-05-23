//! Detection of Trojan-Source-class bidi-control balance hazards
//! (CVE-2021-42574 / CVE-2021-42694).
//!
//! Threat model.  Tier A1.  Adversary embeds Unicode bidi format-
//! control characters (LRE / RLE / LRO / RLO / PDF / LRI / RLI /
//! FSI / PDI) inside source code or identifier-bearing text to
//! reorder the visible glyph stream away from the byte order that
//! compilers and runtime tokenizers see.
//!
//! Detection walks the input with a per-type stack and produces
//! four independent sub-threats:
//!
//!   - [`SubThreat::DepthExceeded`] — nesting > 125 (UAX #9
//!     §3.3.2 cap).
//!   - [`SubThreat::OrphanPop`] — PDF or PDI with no matching
//!     opener.
//!   - [`SubThreat::UnbalancedEmbedding`] — LRE/RLE/LRO opens
//!     unclosed at end.
//!   - [`SubThreat::UnbalancedIsolate`] — LRI/RLI/FSI opens
//!     unclosed at end.
//!
//! An input that has bidi controls but is properly balanced and
//! within depth produces a `Clear` verdict — legitimate inline-
//! Arabic or inline-Hebrew text.

use crate::security::ClassificationKind;

/// UAX #9 §3.3.2 cap on the stack-of-stacks depth.
pub const UAX_DEPTH_LIMIT: usize = 125;

/// LRE (202A), RLE (202B), LRO (202D), RLO (202E).
pub fn opens_embedding(cp: u32) -> bool {
    matches!(cp, 0x202A | 0x202B | 0x202D | 0x202E)
}

pub fn is_pdf(cp: u32) -> bool {
    cp == 0x202C
}

/// LRI (2066), RLI (2067), FSI (2068).
pub fn opens_isolate(cp: u32) -> bool {
    matches!(cp, 0x2066 | 0x2067 | 0x2068)
}

pub fn is_pdi(cp: u32) -> bool {
    cp == 0x2069
}

pub fn is_bidi_format_control(cp: u32) -> bool {
    opens_embedding(cp) || is_pdf(cp) || opens_isolate(cp) || is_pdi(cp)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SubThreat {
    DepthExceeded { max_depth: usize },
    OrphanPop { positions: Vec<usize> },
    UnbalancedEmbedding { open_count: usize, pop_count: usize },
    UnbalancedIsolate { open_count: usize, pop_count: usize },
}

impl SubThreat {
    pub fn tag(&self) -> &'static str {
        match self {
            SubThreat::DepthExceeded { .. } => "DepthExceeded",
            SubThreat::OrphanPop { .. } => "OrphanPop",
            SubThreat::UnbalancedEmbedding { .. } => "UnbalancedEmbedding",
            SubThreat::UnbalancedIsolate { .. } => "UnbalancedIsolate",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Verdict {
    pub kind: ClassificationKind,
    pub sub: Option<SubThreat>,
    pub bidi_positions: Vec<usize>,
    pub emb_open_count: usize,
    pub emb_pop_count: usize,
    pub iso_open_count: usize,
    pub iso_pop_count: usize,
    pub max_depth: usize,
}

pub fn detect(input: &[u32]) -> Verdict {
    let mut v = Verdict {
        kind: ClassificationKind::Clear,
        sub: None,
        bidi_positions: Vec::new(),
        emb_open_count: 0,
        emb_pop_count: 0,
        iso_open_count: 0,
        iso_pop_count: 0,
        max_depth: 0,
    };
    let mut emb_stack: usize = 0;
    let mut iso_stack: usize = 0;
    let mut orphans: Vec<usize> = Vec::new();

    for (i, &cp) in input.iter().enumerate() {
        if !is_bidi_format_control(cp) {
            continue;
        }
        v.bidi_positions.push(i);
        if opens_embedding(cp) {
            emb_stack += 1;
            v.emb_open_count += 1;
            v.max_depth = v.max_depth.max(emb_stack + iso_stack);
        } else if is_pdf(cp) {
            v.emb_pop_count += 1;
            if emb_stack > 0 {
                emb_stack -= 1;
            } else {
                orphans.push(i);
            }
        } else if opens_isolate(cp) {
            iso_stack += 1;
            v.iso_open_count += 1;
            v.max_depth = v.max_depth.max(emb_stack + iso_stack);
        } else if is_pdi(cp) {
            v.iso_pop_count += 1;
            if iso_stack > 0 {
                iso_stack -= 1;
            } else {
                orphans.push(i);
            }
        }
    }

    if v.bidi_positions.is_empty() {
        return v;
    }

    if v.max_depth > UAX_DEPTH_LIMIT {
        v.kind = ClassificationKind::Hazard;
        v.sub = Some(SubThreat::DepthExceeded {
            max_depth: v.max_depth,
        });
        return v;
    }
    if !orphans.is_empty() {
        v.kind = ClassificationKind::Hazard;
        v.sub = Some(SubThreat::OrphanPop { positions: orphans });
        return v;
    }
    if emb_stack > 0 {
        v.kind = ClassificationKind::Hazard;
        v.sub = Some(SubThreat::UnbalancedEmbedding {
            open_count: v.emb_open_count,
            pop_count: v.emb_pop_count,
        });
        return v;
    }
    if iso_stack > 0 {
        v.kind = ClassificationKind::Hazard;
        v.sub = Some(SubThreat::UnbalancedIsolate {
            open_count: v.iso_open_count,
            pop_count: v.iso_pop_count,
        });
        return v;
    }
    // Bidi controls present and balanced.
    v
}
