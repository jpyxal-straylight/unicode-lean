// Shared verdict vocabulary for the Security Conformance Layer.
//
// Per-family modules under unicode_cpp/security/{covert,identity,
// display,form,boundary,crypto}/ import this header and refine
// the shared vocabulary into family-specific verdict structures.

#ifndef UNICODE_CPP_SECURITY_CALCULUS_HPP
#define UNICODE_CPP_SECURITY_CALCULUS_HPP

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace unicode_cpp::security {

// Enumeration of the detector modules.  The order is the order in
// which the aggregator walks them and the priority order callers
// can rely on when composing verdicts across modules.
enum class Family : std::uint8_t {
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
};

// Ordered severity vocabulary.  Strictly less-than:
// Informational < Low < Moderate < High < Critical.
enum class Severity : std::uint8_t {
    Informational = 0,
    Low = 1,
    Moderate = 2,
    High = 3,
    Critical = 4,
};

// Five-tier adversary capability hierarchy.  A tier-N adversary
// has all capabilities of tier (N-1) plus the tier-N additions.
//
//   A0 — passive observer
//   A1 — local injector (single-input attack)
//   A2 — pipeline injector (browser → API → DB → AI)
//   A3 — supply-chain injector (registers a package or identifier)
//   A4 — model-adaptive (tokenizer-query capable)
enum class AdversaryTier : std::uint8_t {
    A0 = 0,
    A1 = 1,
    A2 = 2,
    A3 = 3,
    A4 = 4,
};

// The verdict kind, independent of any family-specific sub-threat
// payload.  Family modules define their own classification types
// carrying sub-threat data; this enum is the shape they all share.
enum class ClassificationKind : std::uint8_t {
    Clear,
    Hazard,
    Compound,
    Informational,
};

// The default severity associated with each classification kind.
// Families can override at the verdict level.
constexpr Severity default_severity(ClassificationKind kind) {
    switch (kind) {
        case ClassificationKind::Clear:         return Severity::Informational;
        case ClassificationKind::Hazard:        return Severity::Moderate;
        case ClassificationKind::Compound:      return Severity::High;
        case ClassificationKind::Informational: return Severity::Informational;
    }
    return Severity::Informational;
}

// A position within a codepoint sequence, optionally enriched
// with a line / column when the input is source-code shaped.
struct HazardPosition {
    std::size_t cp_offset;
    std::optional<std::size_t> line;
    std::optional<std::size_t> column;
};

// A flexible attribution dictionary — string keys to string
// values.  Each family defines its own attribution schema; this
// is the shared container.
class KeyValueAttribution {
   public:
    void push(std::string key, std::string value) {
        entries_.emplace_back(std::move(key), std::move(value));
    }

    std::optional<std::string_view> get(std::string_view key) const {
        for (const auto& [k, v] : entries_) {
            if (k == key) return std::string_view{v};
        }
        return std::nullopt;
    }

    const std::vector<std::pair<std::string, std::string>>& entries() const {
        return entries_;
    }

   private:
    std::vector<std::pair<std::string, std::string>> entries_;
};

}  // namespace unicode_cpp::security

#endif  // UNICODE_CPP_SECURITY_CALCULUS_HPP
