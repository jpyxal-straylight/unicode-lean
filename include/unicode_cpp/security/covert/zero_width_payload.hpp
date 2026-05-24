// Detection of payloads encoded in zero-width and near-zero-width
// Unicode codepoints.
//
// Threat model.  Tier A1.  Adversary embeds zero-width / no-glyph
// codepoints inside otherwise-normal text to carry a covert binary
// payload, to splice WORD JOINER / byte-order-mark sequences into
// identifiers, or to emit a suspected AI-watermark NNBSP pattern.
//
// Zero-width codepoint inventory:
//
//   U+200B  ZERO WIDTH SPACE                (ZWSP)
//   U+200C  ZERO WIDTH NON-JOINER            (ZWNJ)
//   U+200D  ZERO WIDTH JOINER                (ZWJ)
//   U+200E  LEFT-TO-RIGHT MARK               (LRM)
//   U+200F  RIGHT-TO-LEFT MARK               (RLM)
//   U+2060  WORD JOINER                      (WJ)
//   U+2061..U+2064  invisible math operators
//   U+202F  NARROW NO-BREAK SPACE            (NNBSP)
//   U+FEFF  ZERO WIDTH NO-BREAK SPACE / BOM
//   U+FFF9..U+FFFB  INTERLINEAR ANNOTATION marks
//
// Note: this port treats every zero-width occurrence as
// reportable.  The Lean reference additionally exempts ZWJ
// flanked by emoji codepoints (RGI-context legitimate emoji-ZWJ
// sequence) — that exemption requires the UCD emoji-data table.
// Callers needing emoji-aware ZWJ exemption can pre-filter the
// input before calling this detector.

#ifndef UNICODE_CPP_SECURITY_ZERO_WIDTH_PAYLOAD_HPP
#define UNICODE_CPP_SECURITY_ZERO_WIDTH_PAYLOAD_HPP

#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <variant>
#include <vector>

#include "unicode_cpp/security/calculus.hpp"

namespace unicode_cpp::security::zero_width_payload {

// Sibling-detector codepoint ranges — these ARE
// Default_Ignorable per UAX #44 but are dispatched by their own
// family detector for richer payload-decoding / bidi-stack
// tracking, so we EXCLUDE them from the ZW set to avoid
// double-counting.
//
//   U+FE00..U+FE0F     VariationSelectorPayload
//   U+E0100..U+E01EF   VariationSelectorPayload
//   U+E0000..U+E007F   TagBlockPayload
//   U+202A..U+202E     BidiControlBalance (LRE/RLE/PDF/LRO/RLO)
//   U+2066..U+2069     BidiControlBalance (LRI/RLI/FSI/PDI)
//
// LRM / RLM (U+200E / U+200F) are NOT excluded — they're
// direction markers, not push/pop bidi controls.
constexpr bool is_sibling_handled(std::uint32_t cp) {
    return (cp >= 0xFE00u && cp <= 0xFE0Fu)
        || (cp >= 0xE0100u && cp <= 0xE01EFu)
        || (cp >= 0xE0000u && cp <= 0xE007Fu)
        || (cp >= 0x202Au && cp <= 0x202Eu)
        || (cp >= 0x2066u && cp <= 0x2069u);
}

// UAX #44 Default_Ignorable_Code_Point — hardcoded ranges per
// UCD 17.0.0 DerivedCoreProperties.txt.  Stable across Unicode
// versions; updates require bumping the UCD pin and re-verifying
// this table against the new DerivedCoreProperties.txt.
constexpr bool is_default_ignorable(std::uint32_t cp) {
    return cp == 0x00ADu
        || cp == 0x034Fu
        || cp == 0x061Cu
        || (cp >= 0x115Fu && cp <= 0x1160u)
        || (cp >= 0x17B4u && cp <= 0x17B5u)
        || (cp >= 0x180Bu && cp <= 0x180Fu)
        || (cp >= 0x200Bu && cp <= 0x200Fu)
        || (cp >= 0x202Au && cp <= 0x202Eu)
        || (cp >= 0x2060u && cp <= 0x206Fu)
        || cp == 0x3164u
        || (cp >= 0xFE00u && cp <= 0xFE0Fu)
        || cp == 0xFEFFu
        || cp == 0xFFA0u
        || (cp >= 0xFFF0u && cp <= 0xFFF8u)
        || (cp >= 0x1BCA0u && cp <= 0x1BCA3u)
        || (cp >= 0x1D173u && cp <= 0x1D17Au)
        || (cp >= 0xE0000u && cp <= 0xE0FFFu);
}

constexpr bool is_zero_width(std::uint32_t cp) {
    // Explicit historical set — preserves sub-threat dispatch.
    if (cp == 0x200Bu || cp == 0x200Cu || cp == 0x200Du ||
        cp == 0x200Eu || cp == 0x200Fu) return true;
    if (cp >= 0x2060u && cp <= 0x2064u) return true;
    if (cp == 0x202Fu) return true;
    if (cp == 0xFEFFu) return true;
    if (cp >= 0xFFF9u && cp <= 0xFFFBu) return true;
    // UAX #44 Default_Ignorable — catches every other invisible
    // codepoint, modulo sibling-detector ranges.
    if (is_default_ignorable(cp) && !is_sibling_handled(cp)) return true;
    return false;
}

constexpr bool is_nnbsp(std::uint32_t cp) { return cp == 0x202Fu; }
constexpr bool is_word_joiner(std::uint32_t cp) { return cp == 0x2060u; }
constexpr bool is_annotation(std::uint32_t cp) {
    return cp >= 0xFFF9u && cp <= 0xFFFBu;
}
constexpr bool is_zwj_or_zwsp(std::uint32_t cp) {
    return cp == 0x200Bu || cp == 0x200Du;
}

// Priority-ordered sub-threats:
//   1. AnnotationMisuse    — U+FFF9..U+FFFB present
//   2. WordJoinerInjection — U+2060 present
//   3. AiWatermarkNNBSP    — U+202F count ≥ 2
//   4. BinaryPayload       — ≥ 2 ZWSP/ZWJ occurrences
//   5. BareZeroWidth       — fallback
struct AnnotationMisuse {
    std::size_t count;
};
struct WordJoinerInjection {
    std::size_t count;
};
struct AiWatermarkNNBSP {
    std::size_t count;
};
struct BinaryPayload {
    std::size_t pair_count;
};
struct BareZeroWidth {
    std::uint32_t cp;
};

using SubThreat = std::variant<
    AnnotationMisuse,
    WordJoinerInjection,
    AiWatermarkNNBSP,
    BinaryPayload,
    BareZeroWidth>;

inline std::string sub_threat_tag(const SubThreat& sub) {
    if (std::holds_alternative<AnnotationMisuse>(sub))    return "AnnotationMisuse";
    if (std::holds_alternative<WordJoinerInjection>(sub)) return "WordJoinerInjection";
    if (std::holds_alternative<AiWatermarkNNBSP>(sub))    return "AiWatermarkNNBSP";
    if (std::holds_alternative<BinaryPayload>(sub))       return "BinaryPayload";
    if (std::holds_alternative<BareZeroWidth>(sub))       return "BareZeroWidth";
    return "<unreachable>";
}

struct Verdict {
    ClassificationKind kind;
    std::optional<SubThreat> sub;
    std::vector<std::size_t> zero_width_positions;
};

inline Verdict detect(std::span<const std::uint32_t> input) {
    Verdict v{};
    std::size_t annotation_count = 0;
    std::size_t word_joiner_count = 0;
    std::size_t nnbsp_count = 0;
    std::size_t zwj_zwsp_count = 0;

    for (std::size_t i = 0; i < input.size(); ++i) {
        std::uint32_t cp = input[i];
        if (!is_zero_width(cp)) continue;
        v.zero_width_positions.push_back(i);
        if (is_annotation(cp)) annotation_count += 1;
        else if (is_word_joiner(cp)) word_joiner_count += 1;
        else if (is_nnbsp(cp)) nnbsp_count += 1;
        else if (is_zwj_or_zwsp(cp)) zwj_zwsp_count += 1;
    }

    if (v.zero_width_positions.empty()) {
        v.kind = ClassificationKind::Clear;
        return v;
    }

    v.kind = ClassificationKind::Hazard;
    if (annotation_count > 0) {
        v.sub = AnnotationMisuse{annotation_count};
    } else if (word_joiner_count > 0) {
        v.sub = WordJoinerInjection{word_joiner_count};
    } else if (nnbsp_count >= 2) {
        v.sub = AiWatermarkNNBSP{nnbsp_count};
    } else if (zwj_zwsp_count >= 2) {
        v.sub = BinaryPayload{zwj_zwsp_count / 2};
    } else {
        v.sub = BareZeroWidth{input[v.zero_width_positions[0]]};
    }
    return v;
}

}  // namespace unicode_cpp::security::zero_width_payload

#endif  // UNICODE_CPP_SECURITY_ZERO_WIDTH_PAYLOAD_HPP
