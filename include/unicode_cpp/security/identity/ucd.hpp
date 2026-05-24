// UCD-table-backed support module for the identity-spoofing
// detector family — NFC normalization, script lookup, UTS #39
// identifier-status / restriction-level classification.
//
// All data is loaded once from the bundled UCD files under the
// caller-provided data directory via Tables::load_from_dir.  No
// catchall fallback: parser failures throw rather than silently
// falling through, and the spec's @missing defaults (e.g. CCC = 0
// for unlisted codepoints, UAX #44 § 5.7.4) are written as explicit
// branch returns rather than ``.value_or(default)`` lookups.

#ifndef UNICODE_CPP_SECURITY_IDENTITY_UCD_HPP
#define UNICODE_CPP_SECURITY_IDENTITY_UCD_HPP

#include <algorithm>
#include <array>
#include <cctype>
#include <charconv>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>
#include <span>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace unicode_cpp::security::ucd {

// ─────────────────────────────────────────────────────────────────────
// Pair-hash for unordered_map<pair<u32,u32>, u32>
// ─────────────────────────────────────────────────────────────────────

struct PairHash {
    std::size_t operator()(
        const std::pair<std::uint32_t, std::uint32_t>& p) const noexcept {
        const std::size_t a = std::hash<std::uint32_t>{}(p.first);
        const std::size_t b = std::hash<std::uint32_t>{}(p.second);
        return a ^ (b + 0x9E3779B97F4A7C15ULL + (a << 6) + (a >> 2));
    }
};

// ─────────────────────────────────────────────────────────────────────
// UcdEntry — one row of UnicodeData.txt
// ─────────────────────────────────────────────────────────────────────

struct UcdEntry {
    std::uint8_t ccc;
    std::vector<std::uint32_t> canonical_decomp;  // empty if none
};

// ─────────────────────────────────────────────────────────────────────
// RangeEntry — one row from Scripts.txt / ScriptExtensions.txt /
// IdentifierStatus.txt
// ─────────────────────────────────────────────────────────────────────

template <typename T>
struct RangeEntry {
    std::uint32_t start;
    std::uint32_t end;
    T value;
};

// ─────────────────────────────────────────────────────────────────────
// RestrictionLevel — UTS #39 § 5.1
// ─────────────────────────────────────────────────────────────────────

enum class RestrictionLevel {
    AsciiOnly,
    SingleScript,
    HighlyRestrictive,
    ModeratelyRestrictive,
    MinimallyRestrictive,
    Unrestricted,
};

inline std::string restriction_level_tag(RestrictionLevel l) {
    switch (l) {
        case RestrictionLevel::AsciiOnly:             return "ASCIIOnly";
        case RestrictionLevel::SingleScript:          return "SingleScript";
        case RestrictionLevel::HighlyRestrictive:     return "HighlyRestrictive";
        case RestrictionLevel::ModeratelyRestrictive: return "ModeratelyRestrictive";
        case RestrictionLevel::MinimallyRestrictive:  return "MinimallyRestrictive";
        case RestrictionLevel::Unrestricted:          return "Unrestricted";
    }
    throw std::logic_error(
        "restriction_level_tag: unhandled RestrictionLevel");
}

// ─────────────────────────────────────────────────────────────────────
// Tables — parsed UCD data
// ─────────────────────────────────────────────────────────────────────

struct Tables {
    std::unordered_map<std::uint32_t, UcdEntry> ucd;
    std::unordered_set<std::uint32_t> composition_exclusions;
    std::unordered_map<
        std::pair<std::uint32_t, std::uint32_t>, std::uint32_t, PairHash>
            composition_table;
    std::vector<RangeEntry<std::string>> scripts;
    std::vector<RangeEntry<std::vector<std::string>>> script_extensions;
    std::vector<std::pair<std::uint32_t, std::uint32_t>> id_allowed_ranges;
    std::unordered_map<std::string, std::string> script_long_to_short;
    std::unordered_map<std::uint32_t, std::vector<std::uint32_t>>
        case_folding;
    std::vector<std::pair<std::uint32_t, std::uint32_t>>
        default_ignorable_ranges;

    static Tables load_from_dir(const std::filesystem::path& dir);
    static Tables parse(
        std::string_view unicode_data_text,
        std::string_view composition_exclusions_text,
        std::string_view scripts_text,
        std::string_view script_extensions_text,
        std::string_view identifier_status_text,
        std::string_view property_value_aliases_text,
        std::string_view case_folding_text,
        std::string_view derived_core_properties_text);
};

// ─────────────────────────────────────────────────────────────────────
// Parsing helpers
// ─────────────────────────────────────────────────────────────────────

namespace detail {

inline std::string_view trim(std::string_view s) {
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front()))) {
        s.remove_prefix(1);
    }
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) {
        s.remove_suffix(1);
    }
    return s;
}

inline std::string_view strip_comment_and_trim(std::string_view line) {
    const std::size_t hash = line.find('#');
    std::string_view body =
        hash == std::string_view::npos ? line : line.substr(0, hash);
    return trim(body);
}

inline std::optional<std::uint32_t> parse_hex_u32(std::string_view s) {
    s = trim(s);
    if (s.empty()) return std::nullopt;
    std::uint32_t out = 0;
    auto* first = s.data();
    auto* last = s.data() + s.size();
    auto [ptr, ec] = std::from_chars(first, last, out, 16);
    if (ec != std::errc() || ptr != last) return std::nullopt;
    return out;
}

inline std::pair<std::uint32_t, std::uint32_t> parse_range_field(
    std::string_view s) {
    s = trim(s);
    std::size_t dots = s.find("..");
    if (dots == std::string_view::npos) {
        auto cp = parse_hex_u32(s);
        if (!cp) {
            throw std::runtime_error(
                std::string("parse_range_field: not a hex codepoint: ")
                + std::string(s));
        }
        return {*cp, *cp};
    }
    auto a = parse_hex_u32(s.substr(0, dots));
    auto b = parse_hex_u32(s.substr(dots + 2));
    if (!a || !b) {
        throw std::runtime_error(
            std::string("parse_range_field: malformed range: ")
            + std::string(s));
    }
    return {*a, *b};
}

inline std::string read_file(const std::filesystem::path& path) {
    std::ifstream f(path);
    if (!f) {
        throw std::runtime_error(
            "ucd::read_file: cannot open " + path.string());
    }
    std::ostringstream ss;
    ss << f.rdbuf();
    return ss.str();
}

template <typename F>
inline void for_each_line(std::string_view text, F&& fn) {
    std::size_t pos = 0;
    while (pos <= text.size()) {
        std::size_t nl = text.find('\n', pos);
        std::string_view line =
            text.substr(
                pos, nl == std::string_view::npos
                         ? std::string_view::npos
                         : nl - pos);
        fn(line);
        if (nl == std::string_view::npos) break;
        pos = nl + 1;
    }
}

inline std::uint8_t ccc_lookup(
    const std::unordered_map<std::uint32_t, UcdEntry>& ucd,
    std::uint32_t cp) {
    auto it = ucd.find(cp);
    if (it == ucd.end()) {
        // UAX #44 § 5.7.4: CCC = 0 by default for unlisted codepoints.
        return 0;
    }
    return it->second.ccc;
}

}  // namespace detail

// ─────────────────────────────────────────────────────────────────────
// Tables construction
// ─────────────────────────────────────────────────────────────────────

namespace detail {

inline void parse_unicode_data(
    std::string_view text,
    std::unordered_map<std::uint32_t, UcdEntry>& out) {
    for_each_line(text, [&](std::string_view line) {
        if (line.empty() || line.front() == '#') return;
        // Split on ';'.
        std::array<std::string_view, 15> fields{};
        std::size_t field_count = 0;
        std::size_t start = 0;
        for (std::size_t i = 0; i <= line.size(); ++i) {
            if (i == line.size() || line[i] == ';') {
                if (field_count < fields.size()) {
                    fields[field_count++] = line.substr(start, i - start);
                }
                start = i + 1;
            }
        }
        if (field_count < 6) return;
        auto cp_opt = parse_hex_u32(fields[0]);
        if (!cp_opt) return;
        std::uint32_t cp = *cp_opt;

        // CCC field.
        std::string ccc_str(trim(fields[3]));
        std::uint16_t ccc_val = 0;
        auto [ptr, ec] = std::from_chars(
            ccc_str.data(), ccc_str.data() + ccc_str.size(), ccc_val);
        if (ec != std::errc()
            || ptr != ccc_str.data() + ccc_str.size()
            || ccc_val > 255) {
            std::ostringstream msg;
            msg << "UnicodeData.txt: CCC field '" << ccc_str
                << "' for U+" << std::hex << cp
                << " is not a 0-255 integer";
            throw std::runtime_error(msg.str());
        }

        // Canonical decomposition (skip compatibility decomps marked with '<…>').
        std::string_view decomp_field = trim(fields[5]);
        std::vector<std::uint32_t> canonical_decomp;
        if (!decomp_field.empty() && decomp_field.front() != '<') {
            std::size_t tok_start = 0;
            for (std::size_t i = 0; i <= decomp_field.size(); ++i) {
                if (i == decomp_field.size()
                    || std::isspace(
                        static_cast<unsigned char>(decomp_field[i]))) {
                    if (i > tok_start) {
                        auto tok =
                            decomp_field.substr(tok_start, i - tok_start);
                        if (auto val = parse_hex_u32(tok)) {
                            canonical_decomp.push_back(*val);
                        }
                    }
                    tok_start = i + 1;
                }
            }
        }
        out.emplace(
            cp,
            UcdEntry{
                static_cast<std::uint8_t>(ccc_val),
                std::move(canonical_decomp),
            });
    });
}

inline void parse_composition_exclusions(
    std::string_view text, std::unordered_set<std::uint32_t>& out) {
    for_each_line(text, [&](std::string_view line) {
        auto stripped = strip_comment_and_trim(line);
        if (stripped.empty()) return;
        if (auto cp = parse_hex_u32(stripped)) {
            out.insert(*cp);
        }
    });
}

inline void build_composition_table(
    const std::unordered_map<std::uint32_t, UcdEntry>& ucd,
    const std::unordered_set<std::uint32_t>& exclusions,
    std::unordered_map<
        std::pair<std::uint32_t, std::uint32_t>, std::uint32_t,
        PairHash>& out) {
    for (const auto& kv : ucd) {
        const std::uint32_t cp = kv.first;
        const auto& entry = kv.second;
        if (entry.canonical_decomp.size() != 2) continue;
        if (exclusions.contains(cp)) continue;
        const std::uint32_t a = entry.canonical_decomp[0];
        const std::uint32_t b = entry.canonical_decomp[1];
        if (ccc_lookup(ucd, a) != 0) continue;
        out.emplace(std::make_pair(a, b), cp);
    }
}

inline void parse_scripts(
    std::string_view text,
    std::vector<RangeEntry<std::string>>& out) {
    for_each_line(text, [&](std::string_view line) {
        auto stripped = strip_comment_and_trim(line);
        if (stripped.empty()) return;
        std::size_t semi = stripped.find(';');
        if (semi == std::string_view::npos) return;
        auto rng = parse_range_field(stripped.substr(0, semi));
        auto value = std::string(trim(stripped.substr(semi + 1)));
        out.push_back(RangeEntry<std::string>{rng.first, rng.second, value});
    });
    std::sort(out.begin(), out.end(),
        [](const auto& a, const auto& b) { return a.start < b.start; });
}

inline void parse_script_extensions(
    std::string_view text,
    std::vector<RangeEntry<std::vector<std::string>>>& out) {
    for_each_line(text, [&](std::string_view line) {
        auto stripped = strip_comment_and_trim(line);
        if (stripped.empty()) return;
        std::size_t semi = stripped.find(';');
        if (semi == std::string_view::npos) return;
        auto rng = parse_range_field(stripped.substr(0, semi));
        std::string_view list_field = trim(stripped.substr(semi + 1));
        std::vector<std::string> scripts;
        std::size_t tok_start = 0;
        for (std::size_t i = 0; i <= list_field.size(); ++i) {
            if (i == list_field.size()
                || std::isspace(
                    static_cast<unsigned char>(list_field[i]))) {
                if (i > tok_start) {
                    scripts.emplace_back(
                        list_field.substr(tok_start, i - tok_start));
                }
                tok_start = i + 1;
            }
        }
        if (!scripts.empty()) {
            out.push_back(RangeEntry<std::vector<std::string>>{
                rng.first, rng.second, std::move(scripts)});
        }
    });
    std::sort(out.begin(), out.end(),
        [](const auto& a, const auto& b) { return a.start < b.start; });
}

inline void parse_identifier_status(
    std::string_view text,
    std::vector<std::pair<std::uint32_t, std::uint32_t>>& out) {
    for_each_line(text, [&](std::string_view line) {
        auto stripped = strip_comment_and_trim(line);
        if (stripped.empty()) return;
        std::size_t semi = stripped.find(';');
        if (semi == std::string_view::npos) return;
        auto status = trim(stripped.substr(semi + 1));
        if (status != "Allowed") return;
        auto rng = parse_range_field(stripped.substr(0, semi));
        out.push_back({rng.first, rng.second});
    });
    std::sort(out.begin(), out.end(),
        [](const auto& a, const auto& b) { return a.first < b.first; });
}

inline void parse_property_value_aliases(
    std::string_view text,
    std::unordered_map<std::string, std::string>& out) {
    for_each_line(text, [&](std::string_view line) {
        auto stripped = strip_comment_and_trim(line);
        if (stripped.empty()) return;
        std::array<std::string_view, 4> fields{};
        std::size_t field_count = 0;
        std::size_t start = 0;
        for (std::size_t i = 0; i <= stripped.size(); ++i) {
            if (i == stripped.size() || stripped[i] == ';') {
                if (field_count < fields.size()) {
                    fields[field_count++] =
                        stripped.substr(start, i - start);
                }
                start = i + 1;
            }
        }
        if (field_count < 3) return;
        if (trim(fields[0]) != "sc") return;
        std::string short_name(trim(fields[1]));
        std::string long_name(trim(fields[2]));
        out.emplace(std::move(long_name), std::move(short_name));
    });
}

inline void parse_default_ignorable(
    std::string_view text,
    std::vector<std::pair<std::uint32_t, std::uint32_t>>& out) {
    for_each_line(text, [&](std::string_view line) {
        auto stripped = strip_comment_and_trim(line);
        if (stripped.empty()) return;
        std::size_t semi = stripped.find(';');
        if (semi == std::string_view::npos) return;
        auto prop = trim(stripped.substr(semi + 1));
        if (prop != "Default_Ignorable_Code_Point") return;
        auto rng = parse_range_field(stripped.substr(0, semi));
        out.push_back({rng.first, rng.second});
    });
    std::sort(out.begin(), out.end(),
        [](const auto& a, const auto& b) { return a.first < b.first; });
}

inline void parse_case_folding(
    std::string_view text,
    std::unordered_map<std::uint32_t, std::vector<std::uint32_t>>& out) {
    for_each_line(text, [&](std::string_view line) {
        auto stripped = strip_comment_and_trim(line);
        if (stripped.empty()) return;
        // Up to 4 fields: codepoint ; status ; mapping ; name
        std::array<std::string_view, 4> fields{};
        std::size_t field_count = 0;
        std::size_t start = 0;
        for (std::size_t i = 0; i <= stripped.size(); ++i) {
            if (i == stripped.size() || stripped[i] == ';') {
                if (field_count < fields.size()) {
                    fields[field_count++] =
                        stripped.substr(start, i - start);
                }
                start = i + 1;
            }
        }
        if (field_count < 3) return;
        auto status = trim(fields[1]);
        // UCD CaseFolding.txt — keep only status C (Common) and F
        // (Full) entries.  S is redundant with C/F; T is Turkic-
        // locale-specific.  Together C ∪ F is RFC 8265 § 5.2.4
        // "default full case folding".
        if (status != "C" && status != "F") return;
        auto src = parse_hex_u32(trim(fields[0]));
        if (!src) return;
        std::vector<std::uint32_t> tgt;
        std::string_view mapping = trim(fields[2]);
        std::size_t tok_start = 0;
        for (std::size_t i = 0; i <= mapping.size(); ++i) {
            if (i == mapping.size()
                || std::isspace(
                    static_cast<unsigned char>(mapping[i]))) {
                if (i > tok_start) {
                    auto tok = mapping.substr(tok_start, i - tok_start);
                    if (auto v = parse_hex_u32(tok)) tgt.push_back(*v);
                }
                tok_start = i + 1;
            }
        }
        if (!tgt.empty()) {
            out.emplace(*src, std::move(tgt));
        }
    });
}

}  // namespace detail

inline Tables Tables::parse(
    std::string_view unicode_data_text,
    std::string_view composition_exclusions_text,
    std::string_view scripts_text,
    std::string_view script_extensions_text,
    std::string_view identifier_status_text,
    std::string_view property_value_aliases_text,
    std::string_view case_folding_text,
    std::string_view derived_core_properties_text) {
    Tables t;
    detail::parse_unicode_data(unicode_data_text, t.ucd);
    detail::parse_composition_exclusions(
        composition_exclusions_text, t.composition_exclusions);
    detail::build_composition_table(
        t.ucd, t.composition_exclusions, t.composition_table);
    detail::parse_scripts(scripts_text, t.scripts);
    detail::parse_script_extensions(
        script_extensions_text, t.script_extensions);
    detail::parse_identifier_status(
        identifier_status_text, t.id_allowed_ranges);
    detail::parse_property_value_aliases(
        property_value_aliases_text, t.script_long_to_short);
    detail::parse_case_folding(case_folding_text, t.case_folding);
    detail::parse_default_ignorable(
        derived_core_properties_text, t.default_ignorable_ranges);
    return t;
}

inline Tables Tables::load_from_dir(const std::filesystem::path& dir) {
    return parse(
        detail::read_file(dir / "UnicodeData.txt"),
        detail::read_file(dir / "CompositionExclusions.txt"),
        detail::read_file(dir / "Scripts.txt"),
        detail::read_file(dir / "ScriptExtensions.txt"),
        detail::read_file(dir / "IdentifierStatus.txt"),
        detail::read_file(dir / "PropertyValueAliases.txt"),
        detail::read_file(dir / "CaseFolding.txt"),
        detail::read_file(dir / "DerivedCoreProperties.txt"));
}

// ─────────────────────────────────────────────────────────────────────
// Public accessors
// ─────────────────────────────────────────────────────────────────────

inline std::uint8_t ccc(const Tables& t, std::uint32_t cp) {
    return detail::ccc_lookup(t.ucd, cp);
}

// Hangul algorithmic decomposition + composition (UAX #15 § 1.3).
inline constexpr std::uint32_t HANGUL_S_BASE = 0xAC00;
inline constexpr std::uint32_t HANGUL_L_BASE = 0x1100;
inline constexpr std::uint32_t HANGUL_V_BASE = 0x1161;
inline constexpr std::uint32_t HANGUL_T_BASE = 0x11A7;
inline constexpr std::uint32_t HANGUL_L_COUNT = 19;
inline constexpr std::uint32_t HANGUL_V_COUNT = 21;
inline constexpr std::uint32_t HANGUL_T_COUNT = 28;
inline constexpr std::uint32_t HANGUL_N_COUNT =
    HANGUL_V_COUNT * HANGUL_T_COUNT;
inline constexpr std::uint32_t HANGUL_S_COUNT =
    HANGUL_L_COUNT * HANGUL_N_COUNT;

inline bool hangul_decompose(
    std::uint32_t cp, std::vector<std::uint32_t>& out) {
    if (cp < HANGUL_S_BASE || cp >= HANGUL_S_BASE + HANGUL_S_COUNT) {
        return false;
    }
    const std::uint32_t s_index = cp - HANGUL_S_BASE;
    const std::uint32_t l = HANGUL_L_BASE + s_index / HANGUL_N_COUNT;
    const std::uint32_t v =
        HANGUL_V_BASE + (s_index % HANGUL_N_COUNT) / HANGUL_T_COUNT;
    const std::uint32_t t_index = s_index % HANGUL_T_COUNT;
    out.push_back(l);
    out.push_back(v);
    if (t_index != 0) out.push_back(HANGUL_T_BASE + t_index);
    return true;
}

inline std::optional<std::uint32_t> hangul_compose(
    std::uint32_t a, std::uint32_t b) {
    if (a >= HANGUL_L_BASE && a < HANGUL_L_BASE + HANGUL_L_COUNT
        && b >= HANGUL_V_BASE && b < HANGUL_V_BASE + HANGUL_V_COUNT) {
        const std::uint32_t l_index = a - HANGUL_L_BASE;
        const std::uint32_t v_index = b - HANGUL_V_BASE;
        return HANGUL_S_BASE
             + (l_index * HANGUL_V_COUNT + v_index) * HANGUL_T_COUNT;
    }
    if (a >= HANGUL_S_BASE && a < HANGUL_S_BASE + HANGUL_S_COUNT
        && (a - HANGUL_S_BASE) % HANGUL_T_COUNT == 0
        && b > HANGUL_T_BASE && b < HANGUL_T_BASE + HANGUL_T_COUNT) {
        return a + (b - HANGUL_T_BASE);
    }
    return std::nullopt;
}

inline void decompose_one(
    const Tables& t, std::uint32_t cp,
    std::vector<std::uint32_t>& out) {
    if (hangul_decompose(cp, out)) return;
    auto it = t.ucd.find(cp);
    if (it != t.ucd.end() && !it->second.canonical_decomp.empty()) {
        for (std::uint32_t child : it->second.canonical_decomp) {
            decompose_one(t, child, out);
        }
        return;
    }
    out.push_back(cp);
}

inline std::vector<std::uint32_t> canonical_decompose(
    const Tables& t, std::span<const std::uint32_t> input) {
    std::vector<std::uint32_t> out;
    out.reserve(input.size());
    for (std::uint32_t cp : input) {
        decompose_one(t, cp, out);
    }
    return out;
}

inline void canonical_reorder(
    const Tables& t, std::vector<std::uint32_t>& seq) {
    const std::size_t n = seq.size();
    std::size_t i = 0;
    while (i < n) {
        if (ccc(t, seq[i]) == 0) {
            ++i;
            continue;
        }
        std::size_t j = i;
        while (j < n && ccc(t, seq[j]) != 0) ++j;
        std::stable_sort(
            seq.begin() + static_cast<std::ptrdiff_t>(i),
            seq.begin() + static_cast<std::ptrdiff_t>(j),
            [&](std::uint32_t a, std::uint32_t b) {
                return ccc(t, a) < ccc(t, b);
            });
        i = j;
    }
}

inline std::vector<std::uint32_t> canonical_compose(
    const Tables& t, std::span<const std::uint32_t> seq) {
    std::vector<std::uint32_t> out;
    if (seq.empty()) return out;
    out.reserve(seq.size());
    std::optional<std::size_t> starter_idx;
    int last_ccc = -1;
    for (std::uint32_t cp : seq) {
        const std::uint8_t cp_ccc = ccc(t, cp);
        if (starter_idx) {
            const std::uint32_t starter = out[*starter_idx];
            auto composed = hangul_compose(starter, cp);
            if (!composed) {
                auto it = t.composition_table.find(
                    std::make_pair(starter, cp));
                if (it != t.composition_table.end()) composed = it->second;
            }
            const bool blocked =
                cp_ccc != 0 && last_ccc != 0
                && last_ccc >= static_cast<int>(cp_ccc);
            if (!blocked && composed) {
                out[*starter_idx] = *composed;
                continue;
            }
        }
        out.push_back(cp);
        if (cp_ccc == 0) {
            starter_idx = out.size() - 1;
            last_ccc = 0;
        } else {
            last_ccc = static_cast<int>(cp_ccc);
        }
    }
    return out;
}

inline std::vector<std::uint32_t> to_nfc(
    const Tables& t, std::span<const std::uint32_t> input) {
    auto seq = canonical_decompose(t, input);
    canonical_reorder(t, seq);
    return canonical_compose(t, seq);
}

/// UAX #15 NFD — canonical decompose + canonical reorder, without
/// the recomposition pass.  Required by the UTS #39 §4 + §5.4
/// confusable-skeleton bracket.
inline std::vector<std::uint32_t> to_nfd(
    const Tables& t, std::span<const std::uint32_t> input) {
    auto seq = canonical_decompose(t, input);
    canonical_reorder(t, seq);
    return seq;
}

/// UAX #44 Default_Ignorable_Code_Point predicate.  True for
/// zero-width / format-control / soft-hyphen / bidi-control /
/// Mongolian-variation-selector / standard-variation-selector /
/// tag-block codepoints that render as nothing.  Used by
/// letter_skeleton in homoglyph_confusable to strip invisible
/// insertions from typosquat comparison.
inline bool is_default_ignorable(
    const Tables& t, std::uint32_t cp) {
    auto it = std::upper_bound(
        t.default_ignorable_ranges.begin(),
        t.default_ignorable_ranges.end(), cp,
        [](std::uint32_t value,
           const std::pair<std::uint32_t, std::uint32_t>& r) {
            return value < r.first;
        });
    if (it != t.default_ignorable_ranges.begin()) {
        const auto& prev = *(it - 1);
        if (cp <= prev.second) return true;
    }
    return false;
}

/// UCD PropList.txt White_Space predicate.  Hardcoded match
/// since the table is small and stable.  Includes ASCII tab /
/// newline / space, NBSP, NNBSP (U+202F — often abused for
/// invisibility in fonts), space-separator U+2000..U+200A,
/// line / paragraph separators, medium math space, ideographic
/// space.  Used by letter_skeleton to strip whitespace from
/// typosquat comparison.
inline constexpr bool is_white_space(std::uint32_t cp) {
    return (cp >= 0x0009 && cp <= 0x000D)
        || cp == 0x0020
        || cp == 0x0085
        || cp == 0x00A0
        || cp == 0x1680
        || (cp >= 0x2000 && cp <= 0x200A)
        || (cp >= 0x2028 && cp <= 0x2029)
        || cp == 0x202F
        || cp == 0x205F
        || cp == 0x3000;
}

/// Default full case folding (RFC 8265 § 5.2.4 / UCD CaseFolding.txt
/// status C ∪ F) of a codepoint sequence.  Codepoints absent from
/// the table fold to themselves.
inline std::vector<std::uint32_t> case_fold(
    const Tables& t, std::span<const std::uint32_t> input) {
    std::vector<std::uint32_t> out;
    out.reserve(input.size());
    for (std::uint32_t cp : input) {
        auto it = t.case_folding.find(cp);
        if (it == t.case_folding.end()) {
            out.push_back(cp);
        } else {
            for (std::uint32_t r : it->second) out.push_back(r);
        }
    }
    return out;
}

// ─────────────────────────────────────────────────────────────────────
// Scripts / ScriptExtensions / Restriction-level
// ─────────────────────────────────────────────────────────────────────

inline std::string script_of(const Tables& t, std::uint32_t cp) {
    // partition-point upper_bound: first entry with start > cp.
    auto it = std::upper_bound(
        t.scripts.begin(), t.scripts.end(), cp,
        [](std::uint32_t value, const RangeEntry<std::string>& r) {
            return value < r.start;
        });
    if (it != t.scripts.begin()) {
        const auto& prev = *(it - 1);
        if (cp <= prev.end) return prev.value;
    }
    return "Unknown";
}

inline std::string script_long_to_abbrev(
    const Tables& t, const std::string& name) {
    auto it = t.script_long_to_short.find(name);
    if (it == t.script_long_to_short.end()) {
        throw std::runtime_error(
            "script_long_to_abbrev: '" + name
            + "' not in PropertyValueAliases.txt");
    }
    return it->second;
}

inline std::vector<std::string> resolve_scripts(
    const Tables& t, std::uint32_t cp) {
    auto it = std::upper_bound(
        t.script_extensions.begin(), t.script_extensions.end(), cp,
        [](std::uint32_t value,
           const RangeEntry<std::vector<std::string>>& r) {
            return value < r.start;
        });
    if (it != t.script_extensions.begin()) {
        const auto& prev = *(it - 1);
        if (cp <= prev.end) return prev.value;
    }
    return {script_long_to_abbrev(t, script_of(t, cp))};
}

inline bool is_common_script(const Tables& t, std::uint32_t cp) {
    return script_of(t, cp) == "Common";
}
inline bool is_inherited_script(const Tables& t, std::uint32_t cp) {
    return script_of(t, cp) == "Inherited";
}
inline bool is_ignored_for_intersection(const Tables& t, std::uint32_t cp) {
    return is_common_script(t, cp) || is_inherited_script(t, cp);
}

inline std::vector<std::string> string_script_union(
    const Tables& t, std::span<const std::uint32_t> input) {
    std::vector<std::string> acc;
    for (std::uint32_t cp : input) {
        if (is_ignored_for_intersection(t, cp)) continue;
        for (const auto& s : resolve_scripts(t, cp)) {
            if (std::find(acc.begin(), acc.end(), s) == acc.end()) {
                acc.push_back(s);
            }
        }
    }
    return acc;
}

inline bool is_id_allowed(const Tables& t, std::uint32_t cp) {
    auto it = std::upper_bound(
        t.id_allowed_ranges.begin(), t.id_allowed_ranges.end(), cp,
        [](std::uint32_t value,
           const std::pair<std::uint32_t, std::uint32_t>& r) {
            return value < r.first;
        });
    if (it != t.id_allowed_ranges.begin()) {
        const auto& prev = *(it - 1);
        if (cp <= prev.second) return true;
    }
    return false;
}

inline bool is_ascii_only(std::span<const std::uint32_t> cps) {
    for (std::uint32_t cp : cps) {
        if (cp >= 0x80u) return false;
    }
    return true;
}

namespace detail {

inline std::vector<std::string> intersect_many(
    const std::vector<std::vector<std::string>>& sets) {
    if (sets.empty()) return {};
    std::vector<std::string> acc = sets.front();
    for (std::size_t i = 1; i < sets.size(); ++i) {
        std::vector<std::string> next;
        for (const auto& s : acc) {
            if (std::find(sets[i].begin(), sets[i].end(), s)
                != sets[i].end()) {
                next.push_back(s);
            }
        }
        acc = std::move(next);
    }
    return acc;
}

}  // namespace detail

inline std::vector<std::string> string_resolved_scripts(
    const Tables& t, std::span<const std::uint32_t> cps) {
    std::vector<std::vector<std::string>> sets;
    for (std::uint32_t cp : cps) {
        if (is_ignored_for_intersection(t, cp)) continue;
        sets.push_back(resolve_scripts(t, cp));
    }
    if (sets.empty()) return {};
    return detail::intersect_many(sets);
}

inline bool is_single_script(
    const Tables& t, std::span<const std::uint32_t> cps) {
    if (is_ascii_only(cps)) return false;
    return !string_resolved_scripts(t, cps).empty();
}

namespace detail {

inline bool intersects_str(
    const std::vector<std::string>& a,
    const std::vector<std::string>& b) {
    for (const auto& x : a) {
        if (std::find(b.begin(), b.end(), x) != b.end()) return true;
    }
    return false;
}

inline bool all_within_covered(
    const Tables& t, std::span<const std::uint32_t> cps,
    const std::vector<std::string>& covered) {
    for (std::uint32_t cp : cps) {
        if (is_ignored_for_intersection(t, cp)) continue;
        auto r = resolve_scripts(t, cp);
        if (r.empty() || !intersects_str(r, covered)) return false;
    }
    return true;
}

}  // namespace detail

inline bool is_covered_cjk(
    const Tables& t, std::span<const std::uint32_t> cps) {
    static const std::vector<std::string> japanese =
        {"Latn", "Hani", "Hira", "Kana"};
    static const std::vector<std::string> chinese =
        {"Latn", "Hani", "Bopo"};
    static const std::vector<std::string> korean =
        {"Latn", "Hani", "Hang"};
    return detail::all_within_covered(t, cps, japanese)
        || detail::all_within_covered(t, cps, chinese)
        || detail::all_within_covered(t, cps, korean);
}

inline bool is_highly_restrictive(
    const Tables& t, std::span<const std::uint32_t> cps) {
    return is_single_script(t, cps) || is_covered_cjk(t, cps);
}

inline bool is_moderately_restrictive_shape(
    const Tables& t, std::span<const std::uint32_t> cps) {
    std::optional<std::string> other;
    for (std::uint32_t cp : cps) {
        if (is_ignored_for_intersection(t, cp)) continue;
        auto r = resolve_scripts(t, cp);
        if (r.empty()) return false;
        if (std::find(r.begin(), r.end(), std::string("Latn")) != r.end()) {
            continue;
        }
        const std::string s = r.front();
        if (s == "Cyrl" || s == "Grek") return false;
        if (!other) {
            other = s;
        } else if (s != *other) {
            return false;
        }
    }
    return other.has_value();
}

inline bool is_minimally_restrictive(
    const Tables& t, std::span<const std::uint32_t> cps) {
    for (std::uint32_t cp : cps) {
        if (!is_id_allowed(t, cp)) return false;
    }
    return true;
}

inline RestrictionLevel restriction_level(
    const Tables& t, std::span<const std::uint32_t> cps) {
    if (is_ascii_only(cps))                  return RestrictionLevel::AsciiOnly;
    if (is_single_script(t, cps))            return RestrictionLevel::SingleScript;
    if (is_highly_restrictive(t, cps))       return RestrictionLevel::HighlyRestrictive;
    if (is_moderately_restrictive_shape(t, cps))
                                             return RestrictionLevel::ModeratelyRestrictive;
    if (is_minimally_restrictive(t, cps))    return RestrictionLevel::MinimallyRestrictive;
    return RestrictionLevel::Unrestricted;
}

}  // namespace unicode_cpp::security::ucd

#endif  // UNICODE_CPP_SECURITY_IDENTITY_UCD_HPP
