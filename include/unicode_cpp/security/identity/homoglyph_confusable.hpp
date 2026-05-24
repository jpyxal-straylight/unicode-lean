// Detection of homoglyph / confusable identifier substitution
// attacks (Nethereum Oct 2025, IDN homograph, Math-Alpha posing,
// Fullwidth disguise).
//
// Threat model.  Tier A1..A3 (local injector through supply-chain
// injector).  An adversary registers a package, identifier, or
// domain whose visible glyph stream is indistinguishable from a
// canonical target's, but whose byte stream differs at one or
// more positions (Cyrillic 'е' posed as Latin 'e', Mathematical
// Bold 'A' posed as plain 'A', Fullwidth 'Ａ' posed as 'A').  The
// motivating real-world instance is the October 2025 Nethereum
// NuGet supply-chain campaign — twelve packages whose names
// differed from canonical Web3 / Solana toolchain names by a
// single Cyrillic codepoint substitution.
//
// Detection strategy.  Project the input and a curated catalogue
// of canonical targets through the UTS #39 §4 confusable-skeleton
// mapping, iterate to a fixed point, and test equality.  Hazard
// when the input's iterated skeleton matches a target's iterated
// skeleton while the literal codepoint sequences differ.  Layered
// with two range-based predicates:
//
//   - Mathematical Alphanumeric Symbols (U+1D400..U+1D7FF) —
//     Mathematical Bold / Italic / Fraktur / Script / Sans-Serif
//     / Double-Struck Latin letters and digits that render as
//     their plain-ASCII counterparts.
//   - Halfwidth and Fullwidth Forms (U+FF01..U+FFEF) — fullwidth
//     Latin variants that render at full character-cell width.
//
// Six sub-threats are evaluated in fixed priority order
// (highest first):
//
//   - TargetMatch        — input's iterated skeleton matches a
//     canonical target's iterated skeleton.
//   - MathAlpha          — input contains Mathematical
//     Alphanumeric Symbols.
//   - WidthClass         — input contains fullwidth / halfwidth
//     ASCII variants.
//   - DecompositionSwap  — input is not in NFC; to_nfc(input)
//     differs at one or more positions.
//   - CrossScriptMix     — input mixes two or more non-Common,
//     non-Inherited scripts and is not Highly Restrictive.
//   - RestrictionLow     — input's UTS #39 § 5.1 restriction
//     level is Minimally Restrictive or Unrestricted.
//
// Data loading.  The detector consumes a Database that the caller
// constructs once from the bundled data files (confusables.txt,
// KnownAttackTargets.txt, UnicodeData.txt, CompositionExclusions.txt,
// Scripts.txt, ScriptExtensions.txt, IdentifierStatus.txt, and
// PropertyValueAliases.txt) via Database::load_from_dir.  No
// global state, no filesystem access from inside detect.

#ifndef UNICODE_CPP_SECURITY_HOMOGLYPH_CONFUSABLE_HPP
#define UNICODE_CPP_SECURITY_HOMOGLYPH_CONFUSABLE_HPP

#include <cctype>
#include <charconv>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>
#include <span>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <variant>
#include <vector>

#include "unicode_cpp/security/calculus.hpp"
#include "unicode_cpp/security/identity/ucd.hpp"

namespace unicode_cpp::security::homoglyph_confusable {

// True iff cp is in the Mathematical Alphanumeric Symbols
// block (U+1D400..U+1D7FF).
constexpr bool is_math_alphanumeric(std::uint32_t cp) {
    return cp >= 0x1D400u && cp <= 0x1D7FFu;
}

// True iff cp is in the Halfwidth and Fullwidth Forms block
// (U+FF01..U+FFEF).
constexpr bool is_fullwidth_halfwidth(std::uint32_t cp) {
    return cp >= 0xFF01u && cp <= 0xFFEFu;
}

// Sub-threat variants — six total, priority order documented at
// the top of this file.
struct TargetMatch {
    std::string target;
};
struct MathAlpha {
    std::uint32_t first_cp;
    std::size_t count;
};
struct WidthClass {
    std::uint32_t first_cp;
    std::size_t count;
};
struct DecompositionSwap {
    std::size_t first_diff_pos;
};
struct CrossScriptMix {
    std::size_t script_count;
};
struct RestrictionLow {
    ucd::RestrictionLevel level;
};

using SubThreat = std::variant<
    TargetMatch, MathAlpha, WidthClass,
    DecompositionSwap, CrossScriptMix, RestrictionLow>;

inline std::string sub_threat_tag(const SubThreat& sub) {
    if (std::holds_alternative<TargetMatch>(sub))       return "TargetMatch";
    if (std::holds_alternative<MathAlpha>(sub))         return "MathAlpha";
    if (std::holds_alternative<WidthClass>(sub))        return "WidthClass";
    if (std::holds_alternative<DecompositionSwap>(sub)) return "DecompositionSwap";
    if (std::holds_alternative<CrossScriptMix>(sub))    return "CrossScriptMix";
    if (std::holds_alternative<RestrictionLow>(sub))    return "RestrictionLow";
    throw std::logic_error(
        "homoglyph_confusable::sub_threat_tag: variant has no index");
}

struct Verdict {
    ClassificationKind kind;
    std::optional<SubThreat> sub;
    std::vector<std::uint32_t> skeleton;
    std::vector<std::uint32_t> iterated_skeleton;
    ucd::RestrictionLevel restriction_level;
    std::vector<std::string> matched_targets;
};

// Parsed UTS #39 confusable map + curated attack-target list +
// the UCD tables needed for the DecompositionSwap / CrossScriptMix
// / RestrictionLow sub-threats.  Construct once from the bundled
// data files; reuse across calls to detect.
struct Database {
    std::unordered_map<std::uint32_t, std::vector<std::uint32_t>>
        confusables;
    std::vector<std::string> known_attack_targets;
    ucd::Tables tables;

    static Database parse(
        std::string_view confusables_text,
        std::string_view targets_text,
        ucd::Tables tables);

    static Database load_from_dir(
        const std::filesystem::path& dir);
};

namespace detail {

inline std::optional<std::uint32_t> parse_hex_u32(std::string_view s) {
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front()))) {
        s.remove_prefix(1);
    }
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) {
        s.remove_suffix(1);
    }
    if (s.empty()) return std::nullopt;
    std::uint32_t out = 0;
    auto* first = s.data();
    auto* last = s.data() + s.size();
    auto [ptr, ec] = std::from_chars(first, last, out, 16);
    if (ec != std::errc() || ptr != last) return std::nullopt;
    return out;
}

inline std::string read_file(const std::filesystem::path& path) {
    std::ifstream f(path);
    if (!f) {
        throw std::runtime_error(
            "homoglyph_confusable: cannot open " + path.string());
    }
    std::ostringstream ss;
    ss << f.rdbuf();
    return ss.str();
}

inline std::string_view trim(std::string_view s) {
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front()))) {
        s.remove_prefix(1);
    }
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) {
        s.remove_suffix(1);
    }
    return s;
}

inline std::vector<std::uint32_t> parse_codepoints(std::string_view field) {
    std::vector<std::uint32_t> out;
    std::size_t i = 0;
    while (i < field.size()) {
        while (i < field.size() &&
               std::isspace(static_cast<unsigned char>(field[i]))) {
            ++i;
        }
        std::size_t start = i;
        while (i < field.size() &&
               !std::isspace(static_cast<unsigned char>(field[i]))) {
            ++i;
        }
        if (start == i) break;
        auto cp = parse_hex_u32(field.substr(start, i - start));
        if (cp) out.push_back(*cp);
    }
    return out;
}

}  // namespace detail

inline Database Database::parse(
    std::string_view confusables_text,
    std::string_view targets_text,
    ucd::Tables tables) {
    Database db;
    db.tables = std::move(tables);

    std::size_t pos = 0;
    while (pos <= confusables_text.size()) {
        std::size_t nl = confusables_text.find('\n', pos);
        std::string_view line =
            confusables_text.substr(
                pos, nl == std::string_view::npos ? std::string_view::npos
                                                 : nl - pos);
        pos = (nl == std::string_view::npos) ? confusables_text.size() + 1
                                             : nl + 1;

        std::size_t hash = line.find('#');
        std::string_view body =
            hash == std::string_view::npos ? line : line.substr(0, hash);
        body = detail::trim(body);
        if (body.empty()) continue;

        std::size_t semi1 = body.find(';');
        if (semi1 == std::string_view::npos) continue;
        std::size_t semi2 = body.find(';', semi1 + 1);
        std::string_view src_field = body.substr(0, semi1);
        std::string_view tgt_field =
            semi2 == std::string_view::npos
                ? body.substr(semi1 + 1)
                : body.substr(semi1 + 1, semi2 - semi1 - 1);

        auto src = detail::parse_hex_u32(detail::trim(src_field));
        if (!src) continue;
        auto tgt = detail::parse_codepoints(detail::trim(tgt_field));
        if (tgt.empty()) continue;
        db.confusables.emplace(*src, std::move(tgt));
    }

    pos = 0;
    while (pos <= targets_text.size()) {
        std::size_t nl = targets_text.find('\n', pos);
        std::string_view line =
            targets_text.substr(
                pos, nl == std::string_view::npos ? std::string_view::npos
                                                  : nl - pos);
        pos = (nl == std::string_view::npos) ? targets_text.size() + 1
                                             : nl + 1;

        std::string_view trimmed = detail::trim(line);
        if (trimmed.empty()) continue;
        if (trimmed.front() == '#') continue;
        db.known_attack_targets.emplace_back(trimmed);
    }

    return db;
}

inline Database Database::load_from_dir(
    const std::filesystem::path& dir) {
    auto conf = detail::read_file(dir / "confusables.txt");
    auto targ = detail::read_file(dir / "KnownAttackTargets.txt");
    return parse(conf, targ, ucd::Tables::load_from_dir(dir));
}

// Inner substitution step of the UTS #39 skeleton — replaces each
// codepoint by its confusables target sequence (codepoints absent
// from the table are kept).  Not the full skeleton; the case-folded
// NFD bracket is applied by `skeleton`.
inline std::vector<std::uint32_t> substitute(
    std::span<const std::uint32_t> input, const Database& db) {
    std::vector<std::uint32_t> out;
    out.reserve(input.size());
    for (std::uint32_t cp : input) {
        auto it = db.confusables.find(cp);
        if (it == db.confusables.end()) {
            out.push_back(cp);
        } else {
            for (std::uint32_t r : it->second) out.push_back(r);
        }
    }
    return out;
}

// The case-insensitive confusables skeleton per UTS #39 §4 + §5.4:
//
//     skeleton(X) = toNFD(caseFold(substitute(caseFold(toNFD(X)))))
//
// Bracketing case folding inside the NFD passes lets the detector
// collapse case-variant typosquats on case-insensitive registries
// (npm / PyPI / NuGet package IDs, IDN labels) to a single canonical
// representative.  Mirrors the Lean `Unicode.Confusables.skeleton`
// definition.
inline std::vector<std::uint32_t> skeleton(
    std::span<const std::uint32_t> input, const Database& db) {
    auto step1 = ucd::to_nfd(db.tables, input);
    auto step2 = ucd::case_fold(db.tables, step1);
    auto step3 = substitute(step2, db);
    auto step4 = ucd::case_fold(db.tables, step3);
    return ucd::to_nfd(db.tables, step4);
}

// Apply skeleton until a fixed point.  In practice 1–3 iterations
// suffice for every published confusable chain.
inline std::vector<std::uint32_t> iterated_skeleton(
    std::span<const std::uint32_t> input, const Database& db) {
    std::vector<std::uint32_t> current(input.begin(), input.end());
    while (true) {
        auto next = skeleton(current, db);
        if (next == current) return current;
        current = std::move(next);
    }
}

// Stricter "letter" skeleton — iterated_skeleton followed by removal
// of every codepoint with canonicalCombiningClass > 0.
//
// Catches two adjacent classes of typosquat attack that the bare
// §4+§5.4 skeleton misses by strict-equality test:
//
//   (1) base-letter+combining-mark confusables
//       (e.g. U+0247 ɇ → e + ◌̸), and
//   (2) cascading-substitute confusables where one substitute pass
//       isn't enough (e.g. U+2133 ℳ → U+004D → case-fold m →
//       requires a second substitute pass for m → rn).
//
// Iterating skeleton to fixed point handles class (2); filtering
// CCC > 0 codepoints from the result handles class (1).  Used by
// find_target_match for typosquat-style comparison; mirrors the
// Lean Unicode.Confusables.letterSkeleton.
inline std::vector<std::uint32_t> letter_skeleton(
    std::span<const std::uint32_t> input, const Database& db) {
    auto iter = iterated_skeleton(input, db);
    std::vector<std::uint32_t> out;
    out.reserve(iter.size());
    for (std::uint32_t cp : iter) {
        if (ucd::ccc(db.tables, cp) == 0
            && !ucd::is_default_ignorable(db.tables, cp)
            && !ucd::is_white_space(cp)) {
            out.push_back(cp);
        }
    }
    return out;
}

namespace detail {

inline std::vector<std::uint32_t> ascii_codepoints(std::string_view s) {
    std::vector<std::uint32_t> out;
    out.reserve(s.size());
    for (unsigned char c : s) out.push_back(static_cast<std::uint32_t>(c));
    return out;
}

// Constant-time u32-slice equality.  Returns 1 if equal, 0 if
// not, with no early break on first inequality (when lengths
// match).  Length-dependent branch is permitted because target
// names are public and input length is observable from the API.
//
// Used by find_target_match to eliminate the timing side channel
// that would let an attacker fingerprint the curated target list
// by observing detector latency.
inline std::uint32_t ct_u32_slice_eq(
    const std::vector<std::uint32_t>& a,
    std::span<const std::uint32_t> b) {
    if (a.size() != b.size()) return 0;
    std::uint32_t acc = 0;
    for (std::size_t i = 0; i < a.size(); ++i) {
        acc |= a[i] ^ b[i];
    }
    std::uint32_t z = acc;
    z |= z >> 16;
    z |= z >> 8;
    z |= z >> 4;
    z |= z >> 2;
    z |= z >> 1;
    return 1u - (z & 1u);
}

inline std::optional<std::string> find_target_match(
    std::span<const std::uint32_t> input,
    std::span<const std::uint32_t> /*iterated*/,
    const Database& db) {
    // Constant-time discipline (Move 4 of state-level red-team
    // plan): walk the entire curated target list every call.
    // No early break on first match.  Equality via
    // ct_u32_slice_eq.  Per-target work is independent of input.
    //
    // letter_skeleton handles combining-mark + cascading-substitute
    // confusables (Hole 4) and Default_Ignorable + White_Space
    // invisible insertion (Hole 5).  Mirrors Lean letterSkeleton.
    auto input_letters = letter_skeleton(input, db);
    std::optional<std::size_t> first_match;
    for (std::size_t idx = 0; idx < db.known_attack_targets.size(); ++idx) {
        const auto& target = db.known_attack_targets[idx];
        auto t_cps = ascii_codepoints(target);
        // Self-match guard — input is literally the target.
        // Permitted branch (legitimate registration case).
        if (t_cps.size() == input.size() &&
            std::equal(t_cps.begin(), t_cps.end(), input.begin())) {
            continue;
        }
        auto t_letters = letter_skeleton(t_cps, db);
        std::uint32_t letters_eq = ct_u32_slice_eq(
            t_letters,
            std::span<const std::uint32_t>(input_letters));
        // Capture FIRST matching index but do NOT break — keep
        // loop work independent of which target (if any) fires.
        if (letters_eq == 1u && !first_match.has_value()) {
            first_match = idx;
        }
    }
    if (first_match.has_value()) {
        return db.known_attack_targets[*first_match];
    }
    return std::nullopt;
}

}  // namespace detail

namespace detail {

// Precondition: input != nfc.  Returns the first position at
// which the two sequences disagree; falls through to the shorter
// length when the difference is a tail-only extension.
inline std::size_t first_decomposition_diff_pos(
    std::span<const std::uint32_t> input,
    std::span<const std::uint32_t> nfc) {
    const std::size_t shorter = std::min(input.size(), nfc.size());
    for (std::size_t i = 0; i < shorter; ++i) {
        if (input[i] != nfc[i]) return i;
    }
    return shorter;
}

}  // namespace detail

// The HomoglyphConfusable detection function.  Returns a
// structured verdict over the codepoint sequence input,
// projected through the provided database.
inline Verdict detect(
    std::span<const std::uint32_t> input, const Database& db) {
    auto skel = skeleton(input, db);
    auto iskel = iterated_skeleton(input, db);
    const auto rl = ucd::restriction_level(db.tables, input);
    Verdict v{
        ClassificationKind::Clear,
        std::nullopt,
        skel,
        iskel,
        rl,
        {},
    };

    // Priority 1: target match.
    if (auto t = detail::find_target_match(input, iskel, db)) {
        v.kind = ClassificationKind::Hazard;
        v.matched_targets.push_back(*t);
        v.sub = TargetMatch{*t};
        return v;
    }

    // Priority 2: Math Alphanumeric.
    std::size_t math_count = 0;
    std::optional<std::uint32_t> math_first;
    for (std::uint32_t cp : input) {
        if (is_math_alphanumeric(cp)) {
            ++math_count;
            if (!math_first) math_first = cp;
        }
    }
    if (math_count > 0) {
        v.kind = ClassificationKind::Hazard;
        v.sub = MathAlpha{*math_first, math_count};
        return v;
    }

    // Priority 3: Fullwidth/Halfwidth.
    std::size_t fw_count = 0;
    std::optional<std::uint32_t> fw_first;
    for (std::uint32_t cp : input) {
        if (is_fullwidth_halfwidth(cp)) {
            ++fw_count;
            if (!fw_first) fw_first = cp;
        }
    }
    if (fw_count > 0) {
        v.kind = ClassificationKind::Hazard;
        v.sub = WidthClass{*fw_first, fw_count};
        return v;
    }

    // Priority 4: DecompositionSwap.
    auto nfc = ucd::to_nfc(db.tables, input);
    if (nfc.size() != input.size()
        || !std::equal(nfc.begin(), nfc.end(), input.begin())) {
        const std::size_t pos =
            detail::first_decomposition_diff_pos(input, nfc);
        v.kind = ClassificationKind::Hazard;
        v.sub = DecompositionSwap{pos};
        return v;
    }

    // Priority 5: CrossScriptMix.
    const auto script_union = ucd::string_script_union(db.tables, input);
    if (script_union.size() >= 2
        && !ucd::is_highly_restrictive(db.tables, input)) {
        v.kind = ClassificationKind::Hazard;
        v.sub = CrossScriptMix{script_union.size()};
        return v;
    }

    // Priority 6: RestrictionLow.
    if (rl == ucd::RestrictionLevel::MinimallyRestrictive
        || rl == ucd::RestrictionLevel::Unrestricted) {
        v.kind = ClassificationKind::Hazard;
        v.sub = RestrictionLow{rl};
        return v;
    }

    return v;
}

}  // namespace unicode_cpp::security::homoglyph_confusable

#endif  // UNICODE_CPP_SECURITY_HOMOGLYPH_CONFUSABLE_HPP
