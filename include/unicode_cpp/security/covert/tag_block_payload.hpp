// Detection of invisible payloads encoded in the Unicode tag
// block U+E0000..U+E007F.
//
// Threat model.  Tier A1 (local injector).  Adversary crafts an
// input containing tag-block codepoints that pass through string
// processing pipelines as zero-width / no-glyph characters but
// carry a recoverable ASCII payload under the decoder
//
//   tag(c) = c + 0xE0000 for c in [0x20, 0x7E].
//
// No tag-block codepoint has a legitimate visible glyph or a
// registered clean use in modern Unicode.  Every occurrence is
// reportable; the detector's job is to attribute the kind of
// use (direct payload, language-tag prefix, mixed-in-with-text,
// or isolated single tag).

#ifndef UNICODE_CPP_SECURITY_TAG_BLOCK_PAYLOAD_HPP
#define UNICODE_CPP_SECURITY_TAG_BLOCK_PAYLOAD_HPP

#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <variant>
#include <vector>

#include "unicode_cpp/security/calculus.hpp"

namespace unicode_cpp::security::tag_block_payload {

// True iff cp is in the Unicode tag block U+E0000..U+E007F.
constexpr bool is_tag_character(std::uint32_t cp) {
    return cp >= 0xE0000u && cp <= 0xE007Fu;
}

// True iff cp is U+E0001 LANGUAGE TAG.
constexpr bool is_language_tag(std::uint32_t cp) {
    return cp == 0xE0001u;
}

// True iff cp is U+E007F CANCEL TAG.
constexpr bool is_cancel_tag(std::uint32_t cp) {
    return cp == 0xE007Fu;
}

// Decode a tag-block codepoint to its ASCII correspondent.
// Returns std::nullopt for tag codepoints outside the printable-
// ASCII range and for any non-tag codepoint.
constexpr std::optional<char> tag_to_ascii(std::uint32_t cp) {
    if (cp >= 0xE0020u && cp <= 0xE007Eu) {
        return static_cast<char>(cp - 0xE0000u);
    }
    return std::nullopt;
}

// Sub-threat variants.  Priority order (highest first):
//   1. LanguageTagRevival  — E0001 followed by ≥ 1 further tag
//   2. DirectAscii         — input is pure tags decoding to ≥ 1 printable byte
//   3. MixedBlock          — tag chars interleaved with non-tag codepoints
//   4. BareTagPresent      — isolated single tag-block codepoint
struct DirectAscii {
    std::string decoded;
};
struct LanguageTagRevival {
    std::size_t lang_tag_pos;
    std::string decoded_tail;
};
struct MixedBlock {
    std::size_t tag_count;
    std::size_t total_cps;
};
struct BareTagPresent {
    std::uint32_t tag_cp;
};

using SubThreat = std::variant<
    DirectAscii,
    LanguageTagRevival,
    MixedBlock,
    BareTagPresent>;

inline std::string sub_threat_tag(const SubThreat& sub) {
    if (std::holds_alternative<DirectAscii>(sub))         return "DirectAscii";
    if (std::holds_alternative<LanguageTagRevival>(sub))  return "LanguageTagRevival";
    if (std::holds_alternative<MixedBlock>(sub))          return "MixedBlock";
    if (std::holds_alternative<BareTagPresent>(sub))      return "BareTagPresent";
    return "<unreachable>";
}

struct Verdict {
    ClassificationKind kind;
    std::optional<SubThreat> sub;
    std::vector<std::size_t> tag_positions;
    std::string recovered_ascii;
};

namespace detail {

inline std::string decode_tag_run(
    std::span<const std::uint32_t> input,
    std::span<const std::size_t> positions) {
    std::string s;
    for (std::size_t p : positions) {
        if (p < input.size()) {
            if (auto c = tag_to_ascii(input[p])) {
                s.push_back(*c);
            }
        }
    }
    return s;
}

inline bool all_tags(std::span<const std::uint32_t> input) {
    for (std::uint32_t cp : input) {
        if (!is_tag_character(cp)) return false;
    }
    return true;
}

inline std::optional<std::size_t> has_language_tag_prefix(
    std::span<const std::uint32_t> input,
    std::span<const std::size_t> tag_positions) {
    if (tag_positions.empty()) return std::nullopt;
    std::size_t lang_pos = tag_positions[0];
    if (lang_pos >= input.size()) return std::nullopt;
    if (is_language_tag(input[lang_pos]) && tag_positions.size() >= 2) {
        return lang_pos;
    }
    return std::nullopt;
}

inline SubThreat pick_sub_threat(
    std::span<const std::uint32_t> input,
    std::span<const std::size_t> tag_positions,
    const std::string& decoded) {
    if (auto lang_pos = has_language_tag_prefix(input, tag_positions)) {
        std::vector<std::size_t> tail;
        tail.reserve(tag_positions.size() - 1);
        for (std::size_t p : tag_positions) {
            if (p != *lang_pos) tail.push_back(p);
        }
        return LanguageTagRevival{
            *lang_pos, decode_tag_run(input, tail),
        };
    }
    if (all_tags(input) && !decoded.empty()) {
        return DirectAscii{decoded};
    }
    if (input.size() > tag_positions.size()) {
        return MixedBlock{tag_positions.size(), input.size()};
    }
    return BareTagPresent{input[tag_positions[0]]};
}

}  // namespace detail

// The TagBlockPayload detection function.  Returns a structured
// verdict over the codepoint sequence input.
inline Verdict detect(std::span<const std::uint32_t> input) {
    std::vector<std::size_t> tag_positions;
    for (std::size_t i = 0; i < input.size(); ++i) {
        if (is_tag_character(input[i])) {
            tag_positions.push_back(i);
        }
    }
    if (tag_positions.empty()) {
        return Verdict{
            ClassificationKind::Clear,
            std::nullopt,
            {},
            "",
        };
    }
    std::string decoded = detail::decode_tag_run(input, tag_positions);
    auto sub = detail::pick_sub_threat(input, tag_positions, decoded);
    return Verdict{
        ClassificationKind::Hazard,
        sub,
        std::move(tag_positions),
        std::move(decoded),
    };
}

}  // namespace unicode_cpp::security::tag_block_payload

#endif  // UNICODE_CPP_SECURITY_TAG_BLOCK_PAYLOAD_HPP
