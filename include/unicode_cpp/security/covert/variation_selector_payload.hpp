// Detection of GlassWorm-class invisible payloads encoded in
// Unicode variation selectors.
//
// Threat model.  Tier A1.  Adversary crafts an input consisting
// of one visible base codepoint followed by a sequence of
// variation-selector codepoints (U+FE00..U+FE0F union
// U+E0100..U+E01EF) that the receiving renderer treats as a
// no-op glyph variant but that a downstream string-processing
// layer (e.g. an LLM tokenizer or a clipboard pipeline) preserves
// byte-for-byte.  Decoding pairs of VS codepoints back into bytes
// recovers an arbitrary payload.
//
// Note: this port treats every variation-selector occurrence
// after a base codepoint as suspicious.  The Lean reference
// additionally exempts (base, VS) pairs that appear in
// StandardizedVariants.txt and emoji-presentation pairs — those
// exemptions require UCD tables.  The coarser port is more
// conservative: legitimate math / Mongolian / Egyptian / CJK
// Compat / emoji-presentation VS uses will be flagged.  Callers
// who need the exemption should pre-filter against the
// appropriate UCD tables before calling this detector.

#ifndef UNICODE_CPP_SECURITY_VARIATION_SELECTOR_PAYLOAD_HPP
#define UNICODE_CPP_SECURITY_VARIATION_SELECTOR_PAYLOAD_HPP

#include <cstdint>
#include <fstream>
#include <optional>
#include <set>
#include <span>
#include <sstream>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "unicode_cpp/security/calculus.hpp"

namespace unicode_cpp::security::variation_selector_payload {

constexpr bool is_variation_selector(std::uint32_t cp) {
    if (cp >= 0xFE00u && cp <= 0xFE0Fu) return true;
    if (cp >= 0xE0100u && cp <= 0xE01EFu) return true;
    if (cp >= 0x180Bu && cp <= 0x180Du) return true;
    return false;
}

// Decode a single VS codepoint to its nibble value in [0, 255].
// Uses GlassWorm's bit layout: VS1..VS16 = nibbles 0..15,
// VS17..VS256 = nibbles 16..255.  Mongolian FVS codepoints
// (180B..180D) are not part of the GlassWorm-style payload
// alphabet and return std::nullopt.
constexpr std::optional<std::uint32_t> vs_to_nibble(std::uint32_t cp) {
    if (cp >= 0xFE00u && cp <= 0xFE0Fu) return cp - 0xFE00u;
    if (cp >= 0xE0100u && cp <= 0xE01EFu) return cp - 0xE0100u + 16u;
    return std::nullopt;
}

struct DirectPayload {
    std::string decoded;
};
struct IllegalTarget {
    std::uint32_t target_cp;
    std::uint32_t vs_cp;
};
struct RepeatedBase {
    std::uint32_t base_cp;
    std::size_t vs_count;
};

using SubThreat = std::variant<
    DirectPayload,
    IllegalTarget,
    RepeatedBase>;

inline std::string sub_threat_tag(const SubThreat& sub) {
    if (std::holds_alternative<DirectPayload>(sub)) return "DirectPayload";
    if (std::holds_alternative<IllegalTarget>(sub)) return "IllegalTarget";
    if (std::holds_alternative<RepeatedBase>(sub))  return "RepeatedBase";
    return "<unreachable>";
}

struct Verdict {
    ClassificationKind kind;
    std::optional<SubThreat> sub;
    std::vector<std::size_t> vs_positions;
    std::vector<std::uint8_t> recovered_bytes;
};

namespace detail {

inline std::vector<std::uint8_t> decode_vs_run(
    std::span<const std::uint32_t> input,
    std::span<const std::size_t> positions) {
    std::vector<std::uint8_t> out;
    std::optional<std::uint32_t> high;
    for (std::size_t p : positions) {
        auto n = vs_to_nibble(input[p]);
        if (!n) continue;
        if (!high) {
            high = *n;
        } else {
            out.push_back(static_cast<std::uint8_t>((*high << 4) | *n));
            high = std::nullopt;
        }
    }
    return out;
}

inline bool all_same_vs(
    std::span<const std::uint32_t> input,
    std::span<const std::size_t> positions) {
    if (positions.empty()) return true;
    std::uint32_t cp0 = input[positions[0]];
    for (std::size_t p : positions) {
        if (input[p] != cp0) return false;
    }
    return true;
}

inline std::string lossy_ascii(std::span<const std::uint8_t> bytes) {
    std::string s;
    for (std::uint8_t b : bytes) {
        if ((b >= 0x20 && b <= 0x7E) || b == 0x09 || b == 0x0A || b == 0x0D) {
            s.push_back(static_cast<char>(b));
        } else {
            s.push_back('?');
        }
    }
    return s;
}

// Parse StandardizedVariants.txt + emoji-variation-sequences.txt
// at first use from data/ relative to cwd.  Cached for subsequent
// calls.  Falls back to empty set if files missing (legacy
// no-exemption behavior — preserves backwards compat).
inline const std::set<std::pair<std::uint32_t, std::uint32_t>>&
load_legal_variation_pairs() {
    static const auto pairs =
        []() -> std::set<std::pair<std::uint32_t, std::uint32_t>> {
            std::set<std::pair<std::uint32_t, std::uint32_t>> result;
            for (const char* fname : {
                "data/StandardizedVariants.txt",
                "data/emoji-variation-sequences.txt",
            }) {
                std::ifstream f(fname);
                if (!f) continue;
                std::string line;
                while (std::getline(f, line)) {
                    auto hash_pos = line.find('#');
                    if (hash_pos != std::string::npos) {
                        line.erase(hash_pos);
                    }
                    auto semi_pos = line.find(';');
                    if (semi_pos != std::string::npos) {
                        line.erase(semi_pos);
                    }
                    std::istringstream iss(line);
                    std::string base_tok, vs_tok;
                    if (!(iss >> base_tok >> vs_tok)) continue;
                    try {
                        std::uint32_t base = static_cast<std::uint32_t>(
                            std::stoul(base_tok, nullptr, 16));
                        std::uint32_t vs = static_cast<std::uint32_t>(
                            std::stoul(vs_tok, nullptr, 16));
                        result.insert({base, vs});
                    } catch (...) {
                        // ignore malformed lines
                    }
                }
            }
            return result;
        }();
    return pairs;
}

inline bool is_registered_variation_pair(
    std::uint32_t base, std::uint32_t vs) {
    return load_legal_variation_pairs().contains({base, vs});
}

}  // namespace detail

inline Verdict detect(std::span<const std::uint32_t> input) {
    Verdict v{};
    for (std::size_t i = 0; i < input.size(); ++i) {
        if (is_variation_selector(input[i])) {
            v.vs_positions.push_back(i);
        }
    }
    if (v.vs_positions.empty()) {
        v.kind = ClassificationKind::Clear;
        return v;
    }

    v.recovered_bytes = detail::decode_vs_run(input, v.vs_positions);

    // Single-VS exemption: if exactly one VS follows a base AND the
    // (base, VS) pair is registered in StandardizedVariants or
    // emoji-variation-sequences, return Clear (legitimate variant).
    if (v.vs_positions.size() == 1) {
        std::size_t p = v.vs_positions[0];
        if (p > 0 && detail::is_registered_variation_pair(
                         input[p - 1], input[p])) {
            v.kind = ClassificationKind::Clear;
            return v;
        }
    }

    v.kind = ClassificationKind::Hazard;

    // Priority: repeated-VS run > direct payload > illegal target.
    if (v.vs_positions.size() >= 4 &&
        detail::all_same_vs(input, v.vs_positions)) {
        std::size_t p0 = v.vs_positions[0];
        std::uint32_t base = (p0 == 0) ? 0u : input[p0 - 1];
        v.sub = RepeatedBase{base, v.vs_positions.size()};
    } else if (!v.recovered_bytes.empty()) {
        v.sub = DirectPayload{detail::lossy_ascii(v.recovered_bytes)};
    } else {
        std::size_t p = v.vs_positions[0];
        std::uint32_t target = (p == 0) ? 0u : input[p - 1];
        v.sub = IllegalTarget{target, input[p]};
    }
    return v;
}

}  // namespace unicode_cpp::security::variation_selector_payload

#endif  // UNICODE_CPP_SECURITY_VARIATION_SELECTOR_PAYLOAD_HPP
