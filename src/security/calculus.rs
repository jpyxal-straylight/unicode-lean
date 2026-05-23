//! Shared verdict vocabulary for the Security Conformance Layer.
//!
//! Per-family modules import this module and refine the shared
//! vocabulary into family-specific verdict structures.

/// The detector modules.  The order is the order in which the
/// aggregator walks them and the priority order callers can rely
/// on when composing verdicts across modules.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Family {
    TagBlockPayload,
    VariationSelectorPayload,
    ZeroWidthPayload,
    SurrogateReassembly,
    BidiControlBalance,
    HomoglyphConfusable,
    MixedScriptAdmissibility,
    EmojiZwjIntegrity,
    SkinToneVariationForgery,
    SourceDisplayDivergence,
    FilenameDisguise,
    RtlInjection,
    RendererDivergence,
    NormalizationBomb,
    StreamSafeViolation,
    LocaleCaseInversion,
    CaseExpansionMismatch,
    WidthClassConfusion,
    NfcIdempotenceWitness,
    IdentifierFormDrift,
    CovertDisplayCompound,
    ConfusableBidiCompound,
    AdmissibilityFormDrift,
    Bip39Canonical,
    HashInputStability,
    AiWatermarkDetectability,
}

/// Ordered severity vocabulary.  Strictly less-than:
/// `Informational < Low < Moderate < High < Critical`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Severity {
    Informational = 0,
    Low = 1,
    Moderate = 2,
    High = 3,
    Critical = 4,
}

/// Five-tier adversary capability hierarchy.
///
///   - `A0` — passive observer
///   - `A1` — local injector (single-input attack)
///   - `A2` — pipeline injector (browser → API → DB → AI)
///   - `A3` — supply-chain injector (registers a package or
///     identifier)
///   - `A4` — model-adaptive (tokenizer-query capable)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AdversaryTier {
    A0 = 0,
    A1 = 1,
    A2 = 2,
    A3 = 3,
    A4 = 4,
}

/// The verdict kind, independent of any family-specific
/// sub-threat payload.  Family modules define their own
/// classification types carrying sub-threat data; this enum is
/// the shape they all share.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClassificationKind {
    Clear,
    Hazard,
    Compound,
    Informational,
}

/// The default severity associated with each classification kind.
/// Families can override at the verdict level.
pub fn default_severity(kind: ClassificationKind) -> Severity {
    match kind {
        ClassificationKind::Clear => Severity::Informational,
        ClassificationKind::Hazard => Severity::Moderate,
        ClassificationKind::Compound => Severity::High,
        ClassificationKind::Informational => Severity::Informational,
    }
}

/// A position within a codepoint sequence, optionally enriched
/// with a line / column when the input is source-code shaped.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HazardPosition {
    pub cp_offset: usize,
    pub line: Option<usize>,
    pub column: Option<usize>,
}

/// A flexible attribution dictionary — string keys to string
/// values.  Each family defines its own attribution schema; this
/// is the shared container.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct KeyValueAttribution {
    entries: Vec<(String, String)>,
}

impl KeyValueAttribution {
    /// An empty attribution.
    pub fn new() -> Self {
        Self::default()
    }

    /// Append a key-value pair.
    pub fn push(&mut self, key: impl Into<String>, value: impl Into<String>) {
        self.entries.push((key.into(), value.into()));
    }

    /// Look up the first value for `key`.
    pub fn get(&self, key: &str) -> Option<&str> {
        self.entries
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.as_str())
    }

    /// Borrow all entries.
    pub fn entries(&self) -> &[(String, String)] {
        &self.entries
    }
}
