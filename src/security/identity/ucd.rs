//! UCD-table-backed support modules for the identity-spoofing
//! detector family — NFC normalization, script lookup, UTS #39
//! identifier-status / restriction-level classification.
//!
//! All data is embedded at compile time from the bundled UCD
//! files in the port's `data/` directory.  Parsing happens lazily
//! on first access via `std::sync::OnceLock`.

use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

const UNICODE_DATA_RAW: &str =
    include_str!("../../../data/UnicodeData.txt");
const COMPOSITION_EXCLUSIONS_RAW: &str =
    include_str!("../../../data/CompositionExclusions.txt");
const SCRIPTS_RAW: &str = include_str!("../../../data/Scripts.txt");
const SCRIPT_EXTENSIONS_RAW: &str =
    include_str!("../../../data/ScriptExtensions.txt");
const IDENTIFIER_STATUS_RAW: &str =
    include_str!("../../../data/IdentifierStatus.txt");
const PROPERTY_VALUE_ALIASES_RAW: &str =
    include_str!("../../../data/PropertyValueAliases.txt");
const DERIVED_CORE_PROPERTIES_RAW: &str =
    include_str!("../../../data/DerivedCoreProperties.txt");

fn parse_hex(s: &str) -> Option<u32> {
    u32::from_str_radix(s.trim(), 16).ok()
}

/// Return the portion of `line` before the first `#` comment
/// character (or the whole line if no `#` appears), with leading
/// and trailing ASCII whitespace removed.
fn strip_comment_and_trim(line: &str) -> &str {
    let body = match line.find('#') {
        Some(idx) => &line[..idx],
        None => line,
    };
    body.trim()
}

// ─────────────────────────────────────────────────────────────────────
// UnicodeData.txt — CCC + canonical decomposition
// ─────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub struct UcdEntry {
    pub ccc: u8,
    pub canonical_decomp: Option<Vec<u32>>,
}

fn parse_unicode_data() -> HashMap<u32, UcdEntry> {
    let mut out = HashMap::new();
    for line in UNICODE_DATA_RAW.lines() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split(';').collect();
        if fields.len() < 6 {
            continue;
        }
        let cp = match parse_hex(fields[0]) {
            Some(c) => c,
            None => continue,
        };
        let ccc = match fields[3].trim().parse::<u8>() {
            Ok(value) => value,
            Err(err) => panic!(
                "UnicodeData.txt: CCC field for U+{:04X} is not a u8 \
                 ({:?}): {}",
                cp, fields[3], err
            ),
        };
        let decomp_field = fields[5].trim();
        let canonical_decomp = if decomp_field.is_empty() {
            None
        } else if decomp_field.starts_with('<') {
            // Compatibility decomposition — skip for NFC.
            None
        } else {
            let parts: Vec<u32> =
                decomp_field.split_whitespace().filter_map(parse_hex).collect();
            if parts.is_empty() {
                None
            } else {
                Some(parts)
            }
        };
        out.insert(cp, UcdEntry { ccc, canonical_decomp });
    }
    out
}

pub fn ucd_table() -> &'static HashMap<u32, UcdEntry> {
    static T: OnceLock<HashMap<u32, UcdEntry>> = OnceLock::new();
    T.get_or_init(parse_unicode_data)
}

pub fn ccc(cp: u32) -> u8 {
    // UAX #44 § 5.7.4: codepoints absent from the listed CCC ranges
    // have Canonical_Combining_Class = 0 by definition (Not_Reordered).
    // This is the spec's `@missing` default for the Canonical_Combining_Class
    // property, not a catchall fallback for malformed input.
    match ucd_table().get(&cp) {
        Some(entry) => entry.ccc,
        None => 0,
    }
}

// ─────────────────────────────────────────────────────────────────────
// CompositionExclusions.txt — codepoints that must not recompose
// ─────────────────────────────────────────────────────────────────────

fn parse_composition_exclusions() -> HashSet<u32> {
    let mut out = HashSet::new();
    for line in COMPOSITION_EXCLUSIONS_RAW.lines() {
        let stripped = strip_comment_and_trim(line);
        if stripped.is_empty() {
            continue;
        }
        if let Some(cp) = parse_hex(stripped) {
            out.insert(cp);
        }
    }
    out
}

pub fn composition_exclusions() -> &'static HashSet<u32> {
    static T: OnceLock<HashSet<u32>> = OnceLock::new();
    T.get_or_init(parse_composition_exclusions)
}

// ─────────────────────────────────────────────────────────────────────
// Composition table — derived from UnicodeData canonical decomps
// minus the exclusion set.  Inverse of the canonical-decomp map for
// pairs (starter, combiner).
// ─────────────────────────────────────────────────────────────────────

fn build_composition_table() -> HashMap<(u32, u32), u32> {
    let table = ucd_table();
    let exclusions = composition_exclusions();
    let mut out = HashMap::new();
    for (&cp, entry) in table {
        if let Some(ref decomp) = entry.canonical_decomp {
            if decomp.len() == 2 && !exclusions.contains(&cp) {
                // Singleton-decomposition exclusions: also skip cases
                // where the first character is a non-starter.
                if ccc(decomp[0]) == 0 {
                    out.insert((decomp[0], decomp[1]), cp);
                }
            }
        }
    }
    out
}

pub fn composition_table() -> &'static HashMap<(u32, u32), u32> {
    static T: OnceLock<HashMap<(u32, u32), u32>> = OnceLock::new();
    T.get_or_init(build_composition_table)
}

// ─────────────────────────────────────────────────────────────────────
// Hangul algorithmic decomposition + composition
// ─────────────────────────────────────────────────────────────────────

const HANGUL_S_BASE: u32 = 0xAC00;
const HANGUL_L_BASE: u32 = 0x1100;
const HANGUL_V_BASE: u32 = 0x1161;
const HANGUL_T_BASE: u32 = 0x11A7;
const HANGUL_L_COUNT: u32 = 19;
const HANGUL_V_COUNT: u32 = 21;
const HANGUL_T_COUNT: u32 = 28;
const HANGUL_N_COUNT: u32 = HANGUL_V_COUNT * HANGUL_T_COUNT;
const HANGUL_S_COUNT: u32 = HANGUL_L_COUNT * HANGUL_N_COUNT;

fn hangul_decompose(cp: u32, out: &mut Vec<u32>) -> bool {
    if cp < HANGUL_S_BASE || cp >= HANGUL_S_BASE + HANGUL_S_COUNT {
        return false;
    }
    let s_index = cp - HANGUL_S_BASE;
    let l = HANGUL_L_BASE + s_index / HANGUL_N_COUNT;
    let v = HANGUL_V_BASE + (s_index % HANGUL_N_COUNT) / HANGUL_T_COUNT;
    let t_index = s_index % HANGUL_T_COUNT;
    out.push(l);
    out.push(v);
    if t_index != 0 {
        out.push(HANGUL_T_BASE + t_index);
    }
    true
}

fn hangul_compose(a: u32, b: u32) -> Option<u32> {
    // L + V
    if (HANGUL_L_BASE..HANGUL_L_BASE + HANGUL_L_COUNT).contains(&a)
        && (HANGUL_V_BASE..HANGUL_V_BASE + HANGUL_V_COUNT).contains(&b)
    {
        let l_index = a - HANGUL_L_BASE;
        let v_index = b - HANGUL_V_BASE;
        return Some(
            HANGUL_S_BASE + (l_index * HANGUL_V_COUNT + v_index) * HANGUL_T_COUNT,
        );
    }
    // LV + T
    if (HANGUL_S_BASE..HANGUL_S_BASE + HANGUL_S_COUNT).contains(&a)
        && (a - HANGUL_S_BASE) % HANGUL_T_COUNT == 0
        && (HANGUL_T_BASE + 1..HANGUL_T_BASE + HANGUL_T_COUNT).contains(&b)
    {
        return Some(a + (b - HANGUL_T_BASE));
    }
    None
}

// ─────────────────────────────────────────────────────────────────────
// Full canonical decomposition
// ─────────────────────────────────────────────────────────────────────

fn decompose_one(cp: u32, out: &mut Vec<u32>) {
    if hangul_decompose(cp, out) {
        return;
    }
    if let Some(entry) = ucd_table().get(&cp) {
        if let Some(ref decomp) = entry.canonical_decomp {
            for &child in decomp {
                decompose_one(child, out);
            }
            return;
        }
    }
    out.push(cp);
}

fn canonical_decompose(input: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(input.len());
    for &cp in input {
        decompose_one(cp, &mut out);
    }
    out
}

// ─────────────────────────────────────────────────────────────────────
// Canonical reordering (stable sort by CCC within non-starter runs)
// ─────────────────────────────────────────────────────────────────────

fn canonical_reorder(seq: &mut [u32]) {
    let n = seq.len();
    let mut i = 0;
    while i < n {
        if ccc(seq[i]) == 0 {
            i += 1;
            continue;
        }
        let mut j = i;
        while j < n && ccc(seq[j]) != 0 {
            j += 1;
        }
        // Stable sort seq[i..j] by CCC.
        let mut run: Vec<u32> = seq[i..j].to_vec();
        run.sort_by_key(|&cp| ccc(cp));
        seq[i..j].copy_from_slice(&run);
        i = j;
    }
}

// ─────────────────────────────────────────────────────────────────────
// Canonical composition
// ─────────────────────────────────────────────────────────────────────

fn canonical_compose(seq: &[u32]) -> Vec<u32> {
    if seq.is_empty() {
        return Vec::new();
    }
    let comp = composition_table();
    let mut out: Vec<u32> = Vec::with_capacity(seq.len());
    let mut starter_idx: Option<usize> = None;
    let mut last_ccc: i32 = -1;

    for &cp in seq {
        let cp_ccc = ccc(cp);

        if let Some(si) = starter_idx {
            let starter = out[si];
            // Try hangul, then composition table.
            let composed = hangul_compose(starter, cp)
                .or_else(|| comp.get(&(starter, cp)).copied());

            // Blocked check: if last_ccc != 0 and last_ccc >= cp_ccc,
            // the candidate is blocked from composition with starter.
            let blocked = cp_ccc != 0
                && last_ccc != 0
                && last_ccc >= cp_ccc as i32;

            if !blocked {
                if let Some(c) = composed {
                    out[si] = c;
                    // last_ccc unchanged — we just merged a combiner
                    // into the starter (its CCC effectively absorbed).
                    continue;
                }
            }
        }

        out.push(cp);
        if cp_ccc == 0 {
            starter_idx = Some(out.len() - 1);
            last_ccc = 0;
        } else {
            last_ccc = cp_ccc as i32;
        }
    }

    out
}

pub fn to_nfc(input: &[u32]) -> Vec<u32> {
    let mut nfd = canonical_decompose(input);
    canonical_reorder(&mut nfd);
    canonical_compose(&nfd)
}

/// UAX #15 NFD — canonical decompose + canonical reorder, without
/// the recomposition pass.  Required by the UTS #39 §4 +§5.4
/// confusable-skeleton bracket.
pub fn to_nfd(input: &[u32]) -> Vec<u32> {
    let mut seq = canonical_decompose(input);
    canonical_reorder(&mut seq);
    seq
}

// ─────────────────────────────────────────────────────────────────────
// CaseFolding.txt — default full case folding (RFC 8265 § 5.2.4)
// ─────────────────────────────────────────────────────────────────────

const CASE_FOLDING_RAW: &str =
    include_str!("../../../data/CaseFolding.txt");

fn parse_case_folding() -> HashMap<u32, Vec<u32>> {
    let mut out = HashMap::new();
    for line in CASE_FOLDING_RAW.lines() {
        let stripped = strip_comment_and_trim(line);
        if stripped.is_empty() {
            continue;
        }
        let parts: Vec<&str> = stripped.split(';').map(str::trim).collect();
        if parts.len() < 3 {
            continue;
        }
        let status = parts[1];
        // UCD CaseFolding.txt: keep only status C (Common) and F (Full)
        // entries — the union RFC 8265 § 5.2.4 calls "default full case
        // folding".  Status S (Simple) is redundant with C/F, status T
        // is Turkic-locale-specific.
        if status != "C" && status != "F" {
            continue;
        }
        let src = match parse_hex(parts[0]) {
            Some(s) => s,
            None => continue,
        };
        let tgt: Vec<u32> =
            parts[2].split_whitespace().filter_map(parse_hex).collect();
        if tgt.is_empty() {
            continue;
        }
        out.insert(src, tgt);
    }
    out
}

fn case_folding_table() -> &'static HashMap<u32, Vec<u32>> {
    static T: OnceLock<HashMap<u32, Vec<u32>>> = OnceLock::new();
    T.get_or_init(parse_case_folding)
}

/// Default full case folding of a codepoint sequence per
/// RFC 8265 § 5.2.4 / UCD CaseFolding.txt status C ∪ F.
/// Codepoints absent from the table fold to themselves.
pub fn case_fold(input: &[u32]) -> Vec<u32> {
    let table = case_folding_table();
    let mut out = Vec::with_capacity(input.len());
    for &cp in input {
        match table.get(&cp) {
            Some(replacement) => out.extend_from_slice(replacement),
            None => out.push(cp),
        }
    }
    out
}

// ─────────────────────────────────────────────────────────────────────
// Scripts.txt — codepoint → primary script
// ─────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
struct RangeEntry<T> {
    start: u32,
    end: u32,
    value: T,
}

fn parse_range_field(s: &str) -> Option<(u32, u32)> {
    let s = s.trim();
    if let Some(idx) = s.find("..") {
        let a = parse_hex(&s[..idx])?;
        let b = parse_hex(&s[idx + 2..])?;
        Some((a, b))
    } else {
        let a = parse_hex(s)?;
        Some((a, a))
    }
}

fn parse_scripts() -> Vec<RangeEntry<String>> {
    let mut out = Vec::new();
    for line in SCRIPTS_RAW.lines() {
        let stripped = strip_comment_and_trim(line);
        if stripped.is_empty() {
            continue;
        }
        let parts: Vec<&str> = stripped.splitn(2, ';').collect();
        if parts.len() < 2 {
            continue;
        }
        let (start, end) = match parse_range_field(parts[0]) {
            Some(r) => r,
            None => continue,
        };
        let value = parts[1].trim().to_string();
        out.push(RangeEntry { start, end, value });
    }
    out.sort_by_key(|r| r.start);
    out
}

fn scripts_table() -> &'static Vec<RangeEntry<String>> {
    static T: OnceLock<Vec<RangeEntry<String>>> = OnceLock::new();
    T.get_or_init(parse_scripts)
}

pub fn script_of(cp: u32) -> &'static str {
    let table = scripts_table();
    let idx = table.partition_point(|r| r.start <= cp);
    if idx > 0 {
        let entry = &table[idx - 1];
        if cp <= entry.end {
            return &entry.value;
        }
    }
    "Unknown"
}

// ─────────────────────────────────────────────────────────────────────
// ScriptExtensions.txt — codepoint → list of scripts (abbrev)
// ─────────────────────────────────────────────────────────────────────

fn parse_script_extensions() -> Vec<RangeEntry<Vec<String>>> {
    let mut out = Vec::new();
    for line in SCRIPT_EXTENSIONS_RAW.lines() {
        let stripped = strip_comment_and_trim(line);
        if stripped.is_empty() {
            continue;
        }
        let parts: Vec<&str> = stripped.splitn(2, ';').collect();
        if parts.len() < 2 {
            continue;
        }
        let (start, end) = match parse_range_field(parts[0]) {
            Some(r) => r,
            None => continue,
        };
        let value: Vec<String> = parts[1]
            .trim()
            .split_whitespace()
            .map(|s| s.to_string())
            .collect();
        if !value.is_empty() {
            out.push(RangeEntry { start, end, value });
        }
    }
    out.sort_by_key(|r| r.start);
    out
}

fn script_extensions_table() -> &'static Vec<RangeEntry<Vec<String>>> {
    static T: OnceLock<Vec<RangeEntry<Vec<String>>>> = OnceLock::new();
    T.get_or_init(parse_script_extensions)
}

/// Resolve scripts for `cp`.  Returns the ScriptExtensions list
/// (which can be multiple abbreviations like "Adlm Arab Mand") if
/// the codepoint has one, otherwise the single primary script
/// from Scripts.txt.
pub fn resolve_scripts(cp: u32) -> Vec<String> {
    let table = script_extensions_table();
    let idx = table.partition_point(|r| r.start <= cp);
    if idx > 0 {
        let entry = &table[idx - 1];
        if cp <= entry.end {
            return entry.value.clone();
        }
    }
    // Map full script name from Scripts.txt to its abbreviation.
    let primary = script_of(cp);
    vec![script_long_to_abbrev(primary).to_string()]
}

/// Authoritative long-name → 4-letter abbreviation table for the
/// Script property.  Parsed once from the bundled
/// `PropertyValueAliases.txt`.  Every long name that appears in
/// `Scripts.txt` for UCD 17.0.0 has a row here; an unknown name
/// surfacing in this function is a data-file integrity failure
/// rather than an expected case, so the lookup panics fail-fast
/// instead of silently falling through.
fn parse_script_name_to_abbrev() -> HashMap<String, String> {
    let mut out = HashMap::new();
    for line in PROPERTY_VALUE_ALIASES_RAW.lines() {
        let stripped = strip_comment_and_trim(line);
        if stripped.is_empty() {
            continue;
        }
        let parts: Vec<&str> = stripped.split(';').map(str::trim).collect();
        if parts.len() < 3 {
            continue;
        }
        if parts[0] != "sc" {
            continue;
        }
        let short = parts[1].to_string();
        let long = parts[2].to_string();
        out.insert(long, short);
    }
    out
}

fn script_name_to_abbrev() -> &'static HashMap<String, String> {
    static T: OnceLock<HashMap<String, String>> = OnceLock::new();
    T.get_or_init(parse_script_name_to_abbrev)
}

fn script_long_to_abbrev(name: &str) -> &str {
    match script_name_to_abbrev().get(name) {
        Some(short) => short.as_str(),
        None => panic!(
            "script_long_to_abbrev: '{}' not in PropertyValueAliases.txt",
            name
        ),
    }
}

pub fn is_common_script(cp: u32) -> bool {
    let s = script_of(cp);
    s == "Common"
}

pub fn is_inherited_script(cp: u32) -> bool {
    let s = script_of(cp);
    s == "Inherited"
}

pub fn is_ignored_for_intersection(cp: u32) -> bool {
    is_common_script(cp) || is_inherited_script(cp)
}

/// The union of all resolved scripts across non-Common, non-Inherited
/// codepoints of `input`.  Counts every distinct script family that
/// appears in at least one codepoint's resolved-script set.
pub fn string_script_union(input: &[u32]) -> Vec<String> {
    let mut acc: Vec<String> = Vec::new();
    for &cp in input {
        if is_ignored_for_intersection(cp) {
            continue;
        }
        for s in resolve_scripts(cp) {
            if !acc.iter().any(|x| x == &s) {
                acc.push(s);
            }
        }
    }
    acc
}

// ─────────────────────────────────────────────────────────────────────
// IdentifierStatus.txt — UTS #39 General-Security-Profile Allowed set
// ─────────────────────────────────────────────────────────────────────

fn parse_identifier_status() -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    for line in IDENTIFIER_STATUS_RAW.lines() {
        let stripped = strip_comment_and_trim(line);
        if stripped.is_empty() {
            continue;
        }
        let parts: Vec<&str> = stripped.splitn(2, ';').collect();
        if parts.len() < 2 {
            continue;
        }
        let status = parts[1].trim();
        if status != "Allowed" {
            continue;
        }
        if let Some((start, end)) = parse_range_field(parts[0]) {
            out.push((start, end));
        }
    }
    out.sort_by_key(|r| r.0);
    out
}

fn identifier_allowed_ranges() -> &'static Vec<(u32, u32)> {
    static T: OnceLock<Vec<(u32, u32)>> = OnceLock::new();
    T.get_or_init(parse_identifier_status)
}

pub fn is_id_allowed(cp: u32) -> bool {
    let table = identifier_allowed_ranges();
    let idx = table.partition_point(|r| r.0 <= cp);
    if idx > 0 {
        let entry = &table[idx - 1];
        if cp <= entry.1 {
            return true;
        }
    }
    false
}

// ─────────────────────────────────────────────────────────────────────
// DerivedCoreProperties.txt — Default_Ignorable_Code_Point ranges
// ─────────────────────────────────────────────────────────────────────

fn parse_default_ignorable() -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    for line in DERIVED_CORE_PROPERTIES_RAW.lines() {
        let stripped = strip_comment_and_trim(line);
        if stripped.is_empty() {
            continue;
        }
        let parts: Vec<&str> = stripped.splitn(2, ';').collect();
        if parts.len() < 2 {
            continue;
        }
        if parts[1].trim() != "Default_Ignorable_Code_Point" {
            continue;
        }
        if let Some((start, end)) = parse_range_field(parts[0]) {
            out.push((start, end));
        }
    }
    out.sort_by_key(|r| r.0);
    out
}

fn default_ignorable_ranges() -> &'static Vec<(u32, u32)> {
    static T: OnceLock<Vec<(u32, u32)>> = OnceLock::new();
    T.get_or_init(parse_default_ignorable)
}

/// True iff `cp` has the `Default_Ignorable_Code_Point` derived
/// property per UAX #44.  Includes the zero-width / format-control
/// characters (ZWSP, ZWNJ, ZWJ, WJ, BOM, soft hyphen, bidi
/// embedding controls, Mongolian / variation selectors, the tag
/// block, etc.) — codepoints that render as nothing and which an
/// attacker can insert into a target name without changing the
/// visible glyph stream.  Used by `letter_skeleton` in
/// homoglyph_confusable to close the invisible-insertion bypass.
pub fn is_default_ignorable(cp: u32) -> bool {
    let table = default_ignorable_ranges();
    let idx = table.partition_point(|r| r.0 <= cp);
    if idx > 0 {
        let entry = &table[idx - 1];
        if cp <= entry.1 {
            return true;
        }
    }
    false
}

/// True iff `cp` is a whitespace codepoint per UCD PropList.txt
/// `White_Space` property.  Includes ASCII tab/newline/space,
/// no-break space (U+00A0), narrow no-break space (U+202F —
/// frequently abused for invisibility-in-fonts), the
/// space-separator block U+2000..U+200A, line/paragraph
/// separators, medium math space (U+205F), and ideographic space
/// (U+3000).  Hardcoded since the table is small and stable.
///
/// Used by `letter_skeleton` to strip whitespace from typosquat
/// comparison — whitespace inside an identifier is universally
/// attacker abuse, never legitimate.
pub fn is_white_space(cp: u32) -> bool {
    matches!(cp,
        0x0009..=0x000D
      | 0x0020
      | 0x0085
      | 0x00A0
      | 0x1680
      | 0x2000..=0x200A
      | 0x2028..=0x2029
      | 0x202F
      | 0x205F
      | 0x3000
    )
}

// ─────────────────────────────────────────────────────────────────────
// UTS #39 § 5.1 Restriction-level classification
// ─────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RestrictionLevel {
    AsciiOnly,
    SingleScript,
    HighlyRestrictive,
    ModeratelyRestrictive,
    MinimallyRestrictive,
    Unrestricted,
}

pub fn is_ascii_only(cps: &[u32]) -> bool {
    cps.iter().all(|&cp| cp < 0x80)
}

fn intersect_many(sets: &[Vec<String>]) -> Vec<String> {
    if sets.is_empty() {
        return Vec::new();
    }
    let mut acc = sets[0].clone();
    for s in &sets[1..] {
        acc.retain(|x| s.contains(x));
    }
    acc
}

pub fn string_resolved_scripts(cps: &[u32]) -> Vec<String> {
    let non_ignored: Vec<u32> = cps
        .iter()
        .copied()
        .filter(|&cp| !is_ignored_for_intersection(cp))
        .collect();
    if non_ignored.is_empty() {
        return Vec::new();
    }
    let sets: Vec<Vec<String>> =
        non_ignored.iter().map(|&cp| resolve_scripts(cp)).collect();
    intersect_many(&sets)
}

pub fn is_single_script(cps: &[u32]) -> bool {
    !is_ascii_only(cps) && !string_resolved_scripts(cps).is_empty()
}

fn covered_japanese() -> Vec<&'static str> {
    vec!["Latn", "Hani", "Hira", "Kana"]
}
fn covered_chinese() -> Vec<&'static str> {
    vec!["Latn", "Hani", "Bopo"]
}
fn covered_korean() -> Vec<&'static str> {
    vec!["Latn", "Hani", "Hang"]
}

fn intersects(a: &[String], b: &[&str]) -> bool {
    a.iter().any(|x| b.contains(&x.as_str()))
}

fn all_within_covered(cps: &[u32], covered: &[&str]) -> bool {
    cps.iter().all(|&cp| {
        if is_ignored_for_intersection(cp) {
            return true;
        }
        let r = resolve_scripts(cp);
        !r.is_empty() && intersects(&r, covered)
    })
}

pub fn is_covered_cjk(cps: &[u32]) -> bool {
    all_within_covered(cps, &covered_japanese())
        || all_within_covered(cps, &covered_chinese())
        || all_within_covered(cps, &covered_korean())
}

pub fn is_highly_restrictive(cps: &[u32]) -> bool {
    is_single_script(cps) || is_covered_cjk(cps)
}

pub fn is_moderately_restrictive_shape(cps: &[u32]) -> bool {
    let mut other: Option<String> = None;
    for &cp in cps {
        if is_ignored_for_intersection(cp) {
            continue;
        }
        let r = resolve_scripts(cp);
        if r.is_empty() {
            return false;
        }
        if r.iter().any(|s| s == "Latn") {
            continue;
        }
        let s = r[0].clone();
        if s == "Cyrl" || s == "Grek" {
            return false;
        }
        match &other {
            None => other = Some(s),
            Some(o) => {
                if &s != o {
                    return false;
                }
            }
        }
    }
    other.is_some()
}

pub fn is_minimally_restrictive(cps: &[u32]) -> bool {
    cps.iter().all(|&cp| is_id_allowed(cp))
}

pub fn restriction_level(cps: &[u32]) -> RestrictionLevel {
    if is_ascii_only(cps) {
        RestrictionLevel::AsciiOnly
    } else if is_single_script(cps) {
        RestrictionLevel::SingleScript
    } else if is_highly_restrictive(cps) {
        RestrictionLevel::HighlyRestrictive
    } else if is_moderately_restrictive_shape(cps) {
        RestrictionLevel::ModeratelyRestrictive
    } else if is_minimally_restrictive(cps) {
        RestrictionLevel::MinimallyRestrictive
    } else {
        RestrictionLevel::Unrestricted
    }
}
