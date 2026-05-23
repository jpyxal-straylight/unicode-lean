//! Detection of homoglyph / confusable identifier substitution
//! attacks (Nethereum Oct 2025, IDN homograph, Math-Alpha posing,
//! Fullwidth disguise, decomposition swap, cross-script mixing).
//!
//! Threat model.  Tier A1..A3 (local injector → supply-chain
//! injector).  Adversary registers a package / identifier /
//! domain whose visible glyph stream is indistinguishable from
//! a target's but whose byte stream differs at one or more
//! positions.
//!
//! Detection strategy.  Project both the input and a curated list
//! of canonical attack targets onto a confusable-equivalence
//! representative (the UTS #39 §4 skeleton), then test equality.
//! Layered with Mathematical Alphanumeric Symbols range
//! detection (U+1D400..U+1D7FF) and Halfwidth/Fullwidth Forms
//! range detection (U+FF01..U+FFEF).
//!
//! Six sub-threats are evaluated in fixed priority order
//! (highest first):
//!
//!   - `TargetMatch`        — input's iterated skeleton matches
//!     a canonical target's iterated skeleton.
//!   - `MathAlpha`          — input contains Mathematical
//!     Alphanumeric Symbols.
//!   - `WidthClass`         — input contains fullwidth / halfwidth
//!     ASCII variants.
//!   - `DecompositionSwap`  — input is not in NFC; toNFC(input)
//!     differs at one or more positions.
//!   - `CrossScriptMix`     — input mixes two or more non-Common,
//!     non-Inherited scripts and is not Highly Restrictive.
//!   - `RestrictionLow`     — input's UTS #39 §5.1 restriction
//!     level is Minimally Restrictive or Unrestricted.

use std::collections::HashMap;
use std::sync::OnceLock;

use crate::security::ClassificationKind;
use crate::security::identity::ucd;
use crate::security::identity::ucd::RestrictionLevel;

/// UTS #39 confusables data — raw text embedded at compile time.
const CONFUSABLES_RAW: &str = include_str!("../../../data/confusables.txt");

/// Curated attack-target list — raw text embedded at compile time.
const KNOWN_ATTACK_TARGETS_RAW: &str =
    include_str!("../../../data/KnownAttackTargets.txt");

fn parse_hex(s: &str) -> Option<u32> {
    u32::from_str_radix(s.trim(), 16).ok()
}

fn parse_codepoints(field: &str) -> Vec<u32> {
    field
        .split_whitespace()
        .filter_map(parse_hex)
        .collect()
}

fn confusables_map() -> &'static HashMap<u32, Vec<u32>> {
    static MAP: OnceLock<HashMap<u32, Vec<u32>>> = OnceLock::new();
    MAP.get_or_init(|| {
        let mut m = HashMap::new();
        for raw_line in CONFUSABLES_RAW.lines() {
            let body = match raw_line.find('#') {
                Some(idx) => &raw_line[..idx],
                None => raw_line,
            };
            let stripped = body.trim();
            if stripped.is_empty() {
                continue;
            }
            let parts: Vec<&str> = stripped.splitn(3, ';').collect();
            if parts.len() < 2 {
                continue;
            }
            let src = match parse_hex(parts[0].trim()) {
                Some(s) => s,
                None => continue,
            };
            let tgt = parse_codepoints(parts[1]);
            if tgt.is_empty() {
                continue;
            }
            m.insert(src, tgt);
        }
        m
    })
}

fn known_attack_targets() -> &'static Vec<String> {
    static TARGETS: OnceLock<Vec<String>> = OnceLock::new();
    TARGETS.get_or_init(|| {
        let mut out = Vec::new();
        for raw_line in KNOWN_ATTACK_TARGETS_RAW.lines() {
            let trimmed = raw_line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            out.push(trimmed.to_string());
        }
        out
    })
}

/// One application of the UTS #39 confusable mapping.  Each
/// codepoint is replaced by its skeleton image (if present in
/// the confusables map) or by itself (if absent).
pub fn skeleton(input: &[u32]) -> Vec<u32> {
    let map = confusables_map();
    let mut out = Vec::with_capacity(input.len());
    for &cp in input {
        match map.get(&cp) {
            Some(replacement) => out.extend_from_slice(replacement),
            None => out.push(cp),
        }
    }
    out
}

/// Apply `skeleton` until a fixed point is reached.  In practice
/// 1–3 iterations suffice for every published confusable chain.
pub fn iterated_skeleton(input: &[u32]) -> Vec<u32> {
    let mut current = input.to_vec();
    loop {
        let next = skeleton(&current);
        if next == current {
            return current;
        }
        current = next;
    }
}

/// True iff `cp` is in the Mathematical Alphanumeric Symbols
/// block (U+1D400..U+1D7FF).  These render as italic / bold /
/// fraktur / script / sans-serif / double-struck Latin and
/// digit letters and are a common identifier-spoofing vector.
pub fn is_math_alphanumeric(cp: u32) -> bool {
    (0x1D400..=0x1D7FF).contains(&cp)
}

/// True iff `cp` is in the Halfwidth and Fullwidth Forms block
/// (U+FF01..U+FFEF).
pub fn is_fullwidth_halfwidth(cp: u32) -> bool {
    (0xFF01..=0xFFEF).contains(&cp)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SubThreat {
    TargetMatch { target: String },
    MathAlpha { first_cp: u32, count: usize },
    WidthClass { first_cp: u32, count: usize },
    DecompositionSwap { first_diff_pos: usize },
    CrossScriptMix { script_count: usize },
    RestrictionLow { level: RestrictionLevel },
}

impl SubThreat {
    pub fn tag(&self) -> &'static str {
        match self {
            SubThreat::TargetMatch { .. } => "TargetMatch",
            SubThreat::MathAlpha { .. } => "MathAlpha",
            SubThreat::WidthClass { .. } => "WidthClass",
            SubThreat::DecompositionSwap { .. } => "DecompositionSwap",
            SubThreat::CrossScriptMix { .. } => "CrossScriptMix",
            SubThreat::RestrictionLow { .. } => "RestrictionLow",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Verdict {
    pub kind: ClassificationKind,
    pub sub: Option<SubThreat>,
    pub skeleton: Vec<u32>,
    pub iterated_skeleton: Vec<u32>,
    pub restriction_level: RestrictionLevel,
    pub matched_targets: Vec<String>,
}

fn ascii_codepoints(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

fn find_target_match(
    input: &[u32], iterated: &[u32],
) -> Option<String> {
    for target in known_attack_targets() {
        let t_cps = ascii_codepoints(target);
        if t_cps == input {
            continue;
        }
        let t_skel = iterated_skeleton(&t_cps);
        if t_skel == iterated {
            return Some(target.clone());
        }
    }
    None
}

/// First codepoint position at which `input` and its NFC form
/// `nfc` disagree.  Precondition: `input != nfc` (the detect
/// pipeline only calls this after checking that the sequences
/// differ).  Returns the length of the shorter sequence when the
/// difference is a tail-only extension.
fn first_decomposition_diff_pos(input: &[u32], nfc: &[u32]) -> usize {
    let shorter = input.len().min(nfc.len());
    for i in 0..shorter {
        if input[i] != nfc[i] {
            return i;
        }
    }
    shorter
}

/// The HomoglyphConfusable detection function.  Returns a
/// structured verdict over the codepoint sequence `input`.
pub fn detect(input: &[u32]) -> Verdict {
    let skel = skeleton(input);
    let iskel = iterated_skeleton(input);
    let rl = ucd::restriction_level(input);
    let mut v = Verdict {
        kind: ClassificationKind::Clear,
        sub: None,
        skeleton: skel,
        iterated_skeleton: iskel.clone(),
        restriction_level: rl,
        matched_targets: Vec::new(),
    };

    // Priority 1: target match.
    if let Some(target) = find_target_match(input, &iskel) {
        v.kind = ClassificationKind::Hazard;
        v.matched_targets.push(target.clone());
        v.sub = Some(SubThreat::TargetMatch { target });
        return v;
    }

    // Priority 2: Math Alphanumeric.
    if let Some(first_cp) =
        input.iter().copied().find(|cp_ref| is_math_alphanumeric(*cp_ref))
    {
        let count = input
            .iter()
            .filter(|cp_ref| is_math_alphanumeric(**cp_ref))
            .count();
        v.kind = ClassificationKind::Hazard;
        v.sub = Some(SubThreat::MathAlpha { first_cp, count });
        return v;
    }

    // Priority 3: Fullwidth/Halfwidth.
    if let Some(first_cp) =
        input.iter().copied().find(|cp_ref| is_fullwidth_halfwidth(*cp_ref))
    {
        let count = input
            .iter()
            .filter(|cp_ref| is_fullwidth_halfwidth(**cp_ref))
            .count();
        v.kind = ClassificationKind::Hazard;
        v.sub = Some(SubThreat::WidthClass { first_cp, count });
        return v;
    }

    // Priority 4: DecompositionSwap.
    let nfc = ucd::to_nfc(input);
    if nfc.as_slice() != input {
        let first_diff_pos = first_decomposition_diff_pos(input, &nfc);
        v.kind = ClassificationKind::Hazard;
        v.sub = Some(SubThreat::DecompositionSwap { first_diff_pos });
        return v;
    }

    // Priority 5: CrossScriptMix.
    let union = ucd::string_script_union(input);
    if union.len() >= 2 && !ucd::is_highly_restrictive(input) {
        v.kind = ClassificationKind::Hazard;
        v.sub = Some(SubThreat::CrossScriptMix {
            script_count: union.len(),
        });
        return v;
    }

    // Priority 6: RestrictionLow.
    match rl {
        RestrictionLevel::MinimallyRestrictive
        | RestrictionLevel::Unrestricted => {
            v.kind = ClassificationKind::Hazard;
            v.sub = Some(SubThreat::RestrictionLow { level: rl });
            v
        }
        RestrictionLevel::AsciiOnly
        | RestrictionLevel::SingleScript
        | RestrictionLevel::HighlyRestrictive
        | RestrictionLevel::ModeratelyRestrictive => v,
    }
}
