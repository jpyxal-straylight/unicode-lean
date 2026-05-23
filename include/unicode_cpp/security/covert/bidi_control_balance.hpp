// Detection of Trojan-Source-class bidi-control balance hazards
// (CVE-2021-42574 / CVE-2021-42694).
//
// Threat model.  Tier A1.  Adversary embeds Unicode bidi format-
// control characters (LRE / RLE / LRO / RLO / PDF / LRI / RLI /
// FSI / PDI) inside source code or identifier-bearing text to
// reorder the visible glyph stream away from the byte order that
// compilers and runtime tokenizers see.
//
// Detection walks the input with a per-type stack and produces
// four independent sub-threats:
//
//   - DepthExceeded        — nesting > 125 (UAX #9 §3.3.2 cap).
//   - OrphanPop            — PDF or PDI with no matching opener.
//   - UnbalancedEmbedding  — LRE/RLE/LRO opens unclosed at end.
//   - UnbalancedIsolate    — LRI/RLI/FSI opens unclosed at end.
//
// An input that has bidi controls but is properly balanced and
// within depth produces a Clear verdict — this is the case for
// legitimate inline-Arabic or inline-Hebrew text.

#ifndef UNICODE_CPP_SECURITY_BIDI_CONTROL_BALANCE_HPP
#define UNICODE_CPP_SECURITY_BIDI_CONTROL_BALANCE_HPP

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <variant>
#include <vector>

#include "unicode_cpp/security/calculus.hpp"

namespace unicode_cpp::security::bidi_control_balance {

// UAX #9 §3.3.2 depth bound on the stack-of-stacks.
inline constexpr std::size_t uax_depth_limit = 125;

// Bidi format-control predicates.
constexpr bool opens_embedding(std::uint32_t cp) {
    // LRE (202A), RLE (202B), LRO (202D), RLO (202E).
    return cp == 0x202Au || cp == 0x202Bu ||
           cp == 0x202Du || cp == 0x202Eu;
}
constexpr bool is_pdf(std::uint32_t cp) {
    return cp == 0x202Cu;
}
constexpr bool opens_isolate(std::uint32_t cp) {
    // LRI (2066), RLI (2067), FSI (2068).
    return cp == 0x2066u || cp == 0x2067u || cp == 0x2068u;
}
constexpr bool is_pdi(std::uint32_t cp) {
    return cp == 0x2069u;
}
constexpr bool is_bidi_format_control(std::uint32_t cp) {
    return opens_embedding(cp) || is_pdf(cp) ||
           opens_isolate(cp) || is_pdi(cp);
}

struct DepthExceeded {
    std::size_t max_depth;
};
struct OrphanPop {
    std::vector<std::size_t> positions;
};
struct UnbalancedEmbedding {
    std::size_t open_count;
    std::size_t pop_count;
};
struct UnbalancedIsolate {
    std::size_t open_count;
    std::size_t pop_count;
};

using SubThreat = std::variant<
    DepthExceeded,
    OrphanPop,
    UnbalancedEmbedding,
    UnbalancedIsolate>;

inline std::string sub_threat_tag(const SubThreat& sub) {
    if (std::holds_alternative<DepthExceeded>(sub))       return "DepthExceeded";
    if (std::holds_alternative<OrphanPop>(sub))           return "OrphanPop";
    if (std::holds_alternative<UnbalancedEmbedding>(sub)) return "UnbalancedEmbedding";
    if (std::holds_alternative<UnbalancedIsolate>(sub))   return "UnbalancedIsolate";
    return "<unreachable>";
}

struct Verdict {
    ClassificationKind kind;
    std::optional<SubThreat> sub;
    std::vector<std::size_t> bidi_positions;
    std::size_t emb_open_count = 0;
    std::size_t emb_pop_count = 0;
    std::size_t iso_open_count = 0;
    std::size_t iso_pop_count = 0;
    std::size_t max_depth = 0;
};

// The BidiControlBalance detection function.  Returns a
// structured verdict over the codepoint sequence input.
inline Verdict detect(std::span<const std::uint32_t> input) {
    Verdict v{};
    std::size_t emb_stack = 0;
    std::size_t iso_stack = 0;
    std::vector<std::size_t> orphans;

    for (std::size_t i = 0; i < input.size(); ++i) {
        std::uint32_t cp = input[i];
        if (!is_bidi_format_control(cp)) continue;
        v.bidi_positions.push_back(i);
        if (opens_embedding(cp)) {
            emb_stack += 1;
            v.emb_open_count += 1;
            v.max_depth = std::max(v.max_depth, emb_stack + iso_stack);
        } else if (is_pdf(cp)) {
            v.emb_pop_count += 1;
            if (emb_stack > 0) emb_stack -= 1;
            else orphans.push_back(i);
        } else if (opens_isolate(cp)) {
            iso_stack += 1;
            v.iso_open_count += 1;
            v.max_depth = std::max(v.max_depth, emb_stack + iso_stack);
        } else if (is_pdi(cp)) {
            v.iso_pop_count += 1;
            if (iso_stack > 0) iso_stack -= 1;
            else orphans.push_back(i);
        }
    }

    if (v.bidi_positions.empty()) {
        v.kind = ClassificationKind::Clear;
        return v;
    }

    // Priority: depth > orphan > unbalanced embedding > unbalanced isolate.
    if (v.max_depth > uax_depth_limit) {
        v.kind = ClassificationKind::Hazard;
        v.sub = DepthExceeded{v.max_depth};
        return v;
    }
    if (!orphans.empty()) {
        v.kind = ClassificationKind::Hazard;
        v.sub = OrphanPop{std::move(orphans)};
        return v;
    }
    if (emb_stack > 0) {
        v.kind = ClassificationKind::Hazard;
        v.sub = UnbalancedEmbedding{v.emb_open_count, v.emb_pop_count};
        return v;
    }
    if (iso_stack > 0) {
        v.kind = ClassificationKind::Hazard;
        v.sub = UnbalancedIsolate{v.iso_open_count, v.iso_pop_count};
        return v;
    }
    // Bidi controls present and properly balanced.
    v.kind = ClassificationKind::Clear;
    return v;
}

}  // namespace unicode_cpp::security::bidi_control_balance

#endif  // UNICODE_CPP_SECURITY_BIDI_CONTROL_BALANCE_HPP
