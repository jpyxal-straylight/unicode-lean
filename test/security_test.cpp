#include <doctest/doctest.h>

#include <cstdint>
#include <filesystem>
#include <span>
#include <stdexcept>
#include <vector>

#include "unicode_cpp/security/calculus.hpp"
#include "unicode_cpp/security/covert/bidi_control_balance.hpp"
#include "unicode_cpp/security/covert/tag_block_payload.hpp"
#include "unicode_cpp/security/covert/variation_selector_payload.hpp"
#include "unicode_cpp/security/covert/zero_width_payload.hpp"
#include "unicode_cpp/security/identity/homoglyph_confusable.hpp"

using namespace unicode_cpp::security;

static std::span<const std::uint32_t> as_span(
    const std::vector<std::uint32_t>& v) {
    return std::span<const std::uint32_t>(v.data(), v.size());
}

// ─────────────────────────────────────────────────────────────────────
// TagBlockPayload
// ─────────────────────────────────────────────────────────────────────

TEST_CASE("TagBlockPayload — empty input is clear") {
    std::vector<std::uint32_t> empty;
    auto v = tag_block_payload::detect(as_span(empty));
    CHECK(v.kind == ClassificationKind::Clear);
}

TEST_CASE("TagBlockPayload — pure ASCII is clear") {
    std::vector<std::uint32_t> bytes = {'H', 'e', 'l', 'l', 'o'};
    auto v = tag_block_payload::detect(as_span(bytes));
    CHECK(v.kind == ClassificationKind::Clear);
}

TEST_CASE("TagBlockPayload — direct ASCII tag payload \"AB\"") {
    std::vector<std::uint32_t> in = {0xE0041, 0xE0042};
    auto v = tag_block_payload::detect(as_span(in));
    REQUIRE(v.kind == ClassificationKind::Hazard);
    REQUIRE(v.sub.has_value());
    CHECK(tag_block_payload::sub_threat_tag(*v.sub) == "DirectAscii");
    CHECK(v.recovered_ascii == "AB");
}

TEST_CASE("TagBlockPayload — Goodside \"Print 'pwned'\" payload decodes") {
    std::vector<std::uint32_t> in = {
        0xE0050, 0xE0072, 0xE0069, 0xE006E, 0xE0074,
        0xE0020, 0xE0027, 0xE0070, 0xE0077, 0xE006E,
        0xE0065, 0xE0064, 0xE0027,
    };
    auto v = tag_block_payload::detect(as_span(in));
    CHECK(v.recovered_ascii == "Print 'pwned'");
}

TEST_CASE("TagBlockPayload — LANGUAGE TAG + tag char is LanguageTagRevival") {
    std::vector<std::uint32_t> in = {0xE0001, 0xE0065, 0xE006E};
    auto v = tag_block_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(tag_block_payload::sub_threat_tag(*v.sub) == "LanguageTagRevival");
}

TEST_CASE("TagBlockPayload — \"Hi\" + hidden tag payload is MixedBlock") {
    std::vector<std::uint32_t> in = {
        'H', 'i', 0xE0070, 0xE0077, 0xE006E, 0xE0064,
    };
    auto v = tag_block_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(tag_block_payload::sub_threat_tag(*v.sub) == "MixedBlock");
}

TEST_CASE("TagBlockPayload — single CANCEL TAG is BareTagPresent") {
    std::vector<std::uint32_t> in = {0xE007F};
    auto v = tag_block_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(tag_block_payload::sub_threat_tag(*v.sub) == "BareTagPresent");
}

// ─────────────────────────────────────────────────────────────────────
// BidiControlBalance
// ─────────────────────────────────────────────────────────────────────

TEST_CASE("BidiControlBalance — empty input is clear") {
    std::vector<std::uint32_t> empty;
    auto v = bidi_control_balance::detect(as_span(empty));
    CHECK(v.kind == ClassificationKind::Clear);
}

TEST_CASE("BidiControlBalance — balanced LRE + PDF is clear") {
    std::vector<std::uint32_t> in = {0x202A, 'A', 0x202C};
    auto v = bidi_control_balance::detect(as_span(in));
    CHECK(v.kind == ClassificationKind::Clear);
}

TEST_CASE("BidiControlBalance — balanced LRI + PDI is clear") {
    std::vector<std::uint32_t> in = {0x2066, 'A', 0x2069};
    auto v = bidi_control_balance::detect(as_span(in));
    CHECK(v.kind == ClassificationKind::Clear);
}

TEST_CASE("BidiControlBalance — lone RLO is UnbalancedEmbedding") {
    std::vector<std::uint32_t> in = {0x202E, 'A'};
    auto v = bidi_control_balance::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(bidi_control_balance::sub_threat_tag(*v.sub) == "UnbalancedEmbedding");
}

TEST_CASE("BidiControlBalance — lone PDF is OrphanPop") {
    std::vector<std::uint32_t> in = {0x202C};
    auto v = bidi_control_balance::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(bidi_control_balance::sub_threat_tag(*v.sub) == "OrphanPop");
}

TEST_CASE("BidiControlBalance — lone RLI is UnbalancedIsolate") {
    std::vector<std::uint32_t> in = {0x2067, 'A'};
    auto v = bidi_control_balance::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(bidi_control_balance::sub_threat_tag(*v.sub) == "UnbalancedIsolate");
}

TEST_CASE("BidiControlBalance — 126-deep nesting exceeds UAX #9 cap") {
    std::vector<std::uint32_t> in(126, 0x202A);
    in.insert(in.end(), 126, 0x202C);
    auto v = bidi_control_balance::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(bidi_control_balance::sub_threat_tag(*v.sub) == "DepthExceeded");
}

TEST_CASE("BidiControlBalance — Trojan Source shape (unbalanced)") {
    // `if ` + RLO + `)` + `{` — closing PDF elided.
    std::vector<std::uint32_t> in = {
        'i', 'f', ' ', 0x202E, ')', '{',
    };
    auto v = bidi_control_balance::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(bidi_control_balance::sub_threat_tag(*v.sub) == "UnbalancedEmbedding");
}

// ─────────────────────────────────────────────────────────────────────
// ZeroWidthPayload
// ─────────────────────────────────────────────────────────────────────

TEST_CASE("ZeroWidthPayload — empty input is clear") {
    std::vector<std::uint32_t> empty;
    auto v = zero_width_payload::detect(as_span(empty));
    CHECK(v.kind == ClassificationKind::Clear);
}

TEST_CASE("ZeroWidthPayload — ASCII is clear") {
    std::vector<std::uint32_t> in = {'H', 'i'};
    auto v = zero_width_payload::detect(as_span(in));
    CHECK(v.kind == ClassificationKind::Clear);
}

TEST_CASE("ZeroWidthPayload — single ZWSP is BareZeroWidth") {
    std::vector<std::uint32_t> in = {'a', 0x200B, 'b'};
    auto v = zero_width_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(zero_width_payload::sub_threat_tag(*v.sub) == "BareZeroWidth");
}

TEST_CASE("ZeroWidthPayload — WORD JOINER is WordJoinerInjection") {
    std::vector<std::uint32_t> in = {'a', 0x2060, 'b'};
    auto v = zero_width_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(zero_width_payload::sub_threat_tag(*v.sub) == "WordJoinerInjection");
}

TEST_CASE("ZeroWidthPayload — multiple NNBSP is AiWatermarkNNBSP") {
    std::vector<std::uint32_t> in = {'a', 0x202F, 'b', 0x202F, 'c'};
    auto v = zero_width_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(zero_width_payload::sub_threat_tag(*v.sub) == "AiWatermarkNNBSP");
}

TEST_CASE("ZeroWidthPayload — multiple ZWSP is BinaryPayload") {
    std::vector<std::uint32_t> in = {'a', 0x200B, 0x200B, 0x200B, 0x200B};
    auto v = zero_width_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(zero_width_payload::sub_threat_tag(*v.sub) == "BinaryPayload");
}

TEST_CASE("ZeroWidthPayload — annotation mark is AnnotationMisuse") {
    std::vector<std::uint32_t> in = {'a', 0xFFF9, 'b'};
    auto v = zero_width_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(zero_width_payload::sub_threat_tag(*v.sub) == "AnnotationMisuse");
}

// ─────────────────────────────────────────────────────────────────────
// VariationSelectorPayload
// ─────────────────────────────────────────────────────────────────────

TEST_CASE("VariationSelectorPayload — empty input is clear") {
    std::vector<std::uint32_t> empty;
    auto v = variation_selector_payload::detect(as_span(empty));
    CHECK(v.kind == ClassificationKind::Clear);
}

TEST_CASE("VariationSelectorPayload — ASCII is clear") {
    std::vector<std::uint32_t> in = {'H', 'i'};
    auto v = variation_selector_payload::detect(as_span(in));
    CHECK(v.kind == ClassificationKind::Clear);
}

TEST_CASE("VariationSelectorPayload — VS16 on Latin A is IllegalTarget") {
    std::vector<std::uint32_t> in = {0x0041, 0xFE0F};
    auto v = variation_selector_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(variation_selector_payload::sub_threat_tag(*v.sub) == "IllegalTarget");
}

TEST_CASE("VariationSelectorPayload — pair-aligned VS run is DirectPayload") {
    // 'a' + FE04 + FE01 → byte 0x41
    std::vector<std::uint32_t> in = {0x0061, 0xFE04, 0xFE01};
    auto v = variation_selector_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(variation_selector_payload::sub_threat_tag(*v.sub) == "DirectPayload");
    REQUIRE(v.recovered_bytes.size() == 1);
    CHECK(v.recovered_bytes[0] == 0x41);
}

TEST_CASE("VariationSelectorPayload — long single-VS run is RepeatedBase") {
    std::vector<std::uint32_t> in = {
        0x0061, 0xFE04, 0xFE04, 0xFE04, 0xFE04,
        0xFE04, 0xFE04, 0xFE04, 0xFE04,
    };
    auto v = variation_selector_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(variation_selector_payload::sub_threat_tag(*v.sub) == "RepeatedBase");
}

TEST_CASE("VariationSelectorPayload — supplementary VS on Latin is IllegalTarget") {
    std::vector<std::uint32_t> in = {0x0041, 0xE0100};
    auto v = variation_selector_payload::detect(as_span(in));
    REQUIRE(v.sub.has_value());
    CHECK(variation_selector_payload::sub_threat_tag(*v.sub) == "IllegalTarget");
}

// ─────────────────────────────────────────────────────────────────────
// HomoglyphConfusable
// ─────────────────────────────────────────────────────────────────────

// Shared fixture: parse the bundled UCD data once per test program.
// Path resolution: tests run from the build directory; data lives at
// the port root.  Try a few candidate locations.
static const homoglyph_confusable::Database& test_database() {
    static const homoglyph_confusable::Database db = [] {
        const std::filesystem::path candidates[] = {
            "data",
            "../data",
            "../../data",
        };
        for (const auto& p : candidates) {
            if (std::filesystem::exists(p / "confusables.txt") &&
                std::filesystem::exists(p / "KnownAttackTargets.txt")) {
                return homoglyph_confusable::Database::load_from_dir(p);
            }
        }
        throw std::runtime_error(
            "test_database: cannot locate bundled UCD data");
    }();
    return db;
}

TEST_CASE("HomoglyphConfusable — empty input is clear") {
    std::vector<std::uint32_t> empty;
    auto v = homoglyph_confusable::detect(as_span(empty), test_database());
    CHECK(v.kind == ClassificationKind::Clear);
}

TEST_CASE("HomoglyphConfusable — pure ASCII 'hello' is clear") {
    std::vector<std::uint32_t> in = {0x68, 0x65, 0x6C, 0x6C, 0x6F};
    auto v = homoglyph_confusable::detect(as_span(in), test_database());
    CHECK(v.kind == ClassificationKind::Clear);
}

TEST_CASE("HomoglyphConfusable — Nethereum with Cyrillic-e is TargetMatch") {
    // "Nethereum" with the second 'e' (between r and u) replaced by
    // Cyrillic SMALL LETTER IE (U+0435) — the Oct 2025 NuGet
    // supply-chain attack vector.
    std::vector<std::uint32_t> in = {
        0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D,
    };
    auto v = homoglyph_confusable::detect(as_span(in), test_database());
    REQUIRE(v.kind == ClassificationKind::Hazard);
    REQUIRE(v.sub.has_value());
    CHECK(homoglyph_confusable::sub_threat_tag(*v.sub) == "TargetMatch");
    REQUIRE(std::holds_alternative<homoglyph_confusable::TargetMatch>(*v.sub));
    CHECK(std::get<homoglyph_confusable::TargetMatch>(*v.sub).target == "Nethereum");
}

TEST_CASE("HomoglyphConfusable — Mathematical Bold A is MathAlpha") {
    std::vector<std::uint32_t> in = {0x1D400};
    auto v = homoglyph_confusable::detect(as_span(in), test_database());
    REQUIRE(v.kind == ClassificationKind::Hazard);
    REQUIRE(v.sub.has_value());
    CHECK(homoglyph_confusable::sub_threat_tag(*v.sub) == "MathAlpha");
}

TEST_CASE("HomoglyphConfusable — three Math-Bold capitals: count == 3") {
    std::vector<std::uint32_t> in = {0x1D400, 0x1D401, 0x1D402};
    auto v = homoglyph_confusable::detect(as_span(in), test_database());
    REQUIRE(v.sub.has_value());
    REQUIRE(std::holds_alternative<homoglyph_confusable::MathAlpha>(*v.sub));
    CHECK(std::get<homoglyph_confusable::MathAlpha>(*v.sub).count == 3);
}

TEST_CASE("HomoglyphConfusable — Fullwidth A is WidthClass") {
    std::vector<std::uint32_t> in = {0xFF21};
    auto v = homoglyph_confusable::detect(as_span(in), test_database());
    REQUIRE(v.kind == ClassificationKind::Hazard);
    REQUIRE(v.sub.has_value());
    CHECK(homoglyph_confusable::sub_threat_tag(*v.sub) == "WidthClass");
}

TEST_CASE("HomoglyphConfusable — Cyrillic 'е' skeletons to Latin 'e'") {
    std::vector<std::uint32_t> in = {0x0435};
    auto s = homoglyph_confusable::skeleton(as_span(in), test_database());
    REQUIRE(s.size() == 1);
    CHECK(s[0] == 0x0065);
}

TEST_CASE("HomoglyphConfusable — pure ASCII iterated skeleton is fixed point") {
    std::vector<std::uint32_t> in = {0x61};
    auto s =
        homoglyph_confusable::iterated_skeleton(as_span(in), test_database());
    REQUIRE(s.size() == 1);
    CHECK(s[0] == 0x61);
}

TEST_CASE("HomoglyphConfusable — Math Alphanumeric block predicate") {
    CHECK(homoglyph_confusable::is_math_alphanumeric(0x1D400));
    CHECK(homoglyph_confusable::is_math_alphanumeric(0x1D7FF));
    CHECK_FALSE(homoglyph_confusable::is_math_alphanumeric(0x1D3FF));
    CHECK_FALSE(homoglyph_confusable::is_math_alphanumeric(0x1D800));
}

TEST_CASE("HomoglyphConfusable — Fullwidth/Halfwidth block predicate") {
    CHECK(homoglyph_confusable::is_fullwidth_halfwidth(0xFF01));
    CHECK(homoglyph_confusable::is_fullwidth_halfwidth(0xFFEF));
    CHECK_FALSE(homoglyph_confusable::is_fullwidth_halfwidth(0xFF00));
    CHECK_FALSE(homoglyph_confusable::is_fullwidth_halfwidth(0xFFF0));
}

TEST_CASE("HomoglyphConfusable — A + combining grave is DecompositionSwap") {
    // 'A' (U+0041) + COMBINING GRAVE ACCENT (U+0300) is not in NFC;
    // to_nfc composes it into À (U+00C0).
    std::vector<std::uint32_t> in = {0x0041, 0x0300};
    auto v = homoglyph_confusable::detect(as_span(in), test_database());
    REQUIRE(v.kind == ClassificationKind::Hazard);
    REQUIRE(v.sub.has_value());
    CHECK(homoglyph_confusable::sub_threat_tag(*v.sub) == "DecompositionSwap");
}

TEST_CASE("HomoglyphConfusable — Latin a + Hebrew Alef is CrossScriptMix") {
    std::vector<std::uint32_t> in = {0x0061, 0x05D0};
    auto v = homoglyph_confusable::detect(as_span(in), test_database());
    REQUIRE(v.kind == ClassificationKind::Hazard);
    REQUIRE(v.sub.has_value());
    CHECK(homoglyph_confusable::sub_threat_tag(*v.sub) == "CrossScriptMix");
}

TEST_CASE("HomoglyphConfusable — pure Greek 'λόγος' is clear") {
    std::vector<std::uint32_t> in =
        {0x03BB, 0x03CC, 0x03B3, 0x03BF, 0x03C2};
    auto v = homoglyph_confusable::detect(as_span(in), test_database());
    CHECK(v.kind == ClassificationKind::Clear);
}
