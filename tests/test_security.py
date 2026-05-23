"""Security Conformance Layer — detector tests."""

from unicode_python.security import ClassificationKind
from unicode_python.security.covert import (
    bidi_control_balance,
    tag_block_payload,
    variation_selector_payload,
    zero_width_payload,
)
from unicode_python.security.identity import homoglyph_confusable


# ─────────────────────────────────────────────────────────────────────
# TagBlockPayload
# ─────────────────────────────────────────────────────────────────────


def test_tag_block_empty_clear() -> None:
    assert tag_block_payload.detect([]).kind is ClassificationKind.CLEAR


def test_tag_block_ascii_clear() -> None:
    assert tag_block_payload.detect([0x48, 0x65, 0x6C, 0x6C, 0x6F]).kind is ClassificationKind.CLEAR


def test_tag_block_direct_ascii_AB() -> None:
    v = tag_block_payload.detect([0xE0041, 0xE0042])
    assert v.kind is ClassificationKind.HAZARD
    assert tag_block_payload.sub_threat_tag(v.sub) == "DirectAscii"
    assert v.recovered_ascii == "AB"


def test_tag_block_goodside_decodes() -> None:
    v = tag_block_payload.detect([
        0xE0050, 0xE0072, 0xE0069, 0xE006E, 0xE0074,
        0xE0020, 0xE0027, 0xE0070, 0xE0077, 0xE006E,
        0xE0065, 0xE0064, 0xE0027,
    ])
    assert v.recovered_ascii == "Print 'pwned'"


def test_tag_block_language_tag_revival() -> None:
    v = tag_block_payload.detect([0xE0001, 0xE0065, 0xE006E])
    assert tag_block_payload.sub_threat_tag(v.sub) == "LanguageTagRevival"


def test_tag_block_mixed_block() -> None:
    v = tag_block_payload.detect([0x48, 0x69, 0xE0070, 0xE0077, 0xE006E, 0xE0064])
    assert tag_block_payload.sub_threat_tag(v.sub) == "MixedBlock"


def test_tag_block_cancel_bare() -> None:
    v = tag_block_payload.detect([0xE007F])
    assert tag_block_payload.sub_threat_tag(v.sub) == "BareTagPresent"


# ─────────────────────────────────────────────────────────────────────
# BidiControlBalance
# ─────────────────────────────────────────────────────────────────────


def test_bidi_empty_clear() -> None:
    assert bidi_control_balance.detect([]).kind is ClassificationKind.CLEAR


def test_bidi_balanced_embedding_clear() -> None:
    assert bidi_control_balance.detect([0x202A, 0x41, 0x202C]).kind is ClassificationKind.CLEAR


def test_bidi_balanced_isolate_clear() -> None:
    assert bidi_control_balance.detect([0x2066, 0x41, 0x2069]).kind is ClassificationKind.CLEAR


def test_bidi_lone_rlo_unbalanced() -> None:
    v = bidi_control_balance.detect([0x202E, 0x41])
    assert bidi_control_balance.sub_threat_tag(v.sub) == "UnbalancedEmbedding"


def test_bidi_lone_pdf_orphan() -> None:
    v = bidi_control_balance.detect([0x202C])
    assert bidi_control_balance.sub_threat_tag(v.sub) == "OrphanPop"


def test_bidi_lone_lri_unbalanced_isolate() -> None:
    v = bidi_control_balance.detect([0x2067, 0x41])
    assert bidi_control_balance.sub_threat_tag(v.sub) == "UnbalancedIsolate"


def test_bidi_depth_exceeded() -> None:
    v = bidi_control_balance.detect([0x202A] * 126 + [0x202C] * 126)
    assert bidi_control_balance.sub_threat_tag(v.sub) == "DepthExceeded"


def test_bidi_trojan_source_unbalanced() -> None:
    v = bidi_control_balance.detect([0x69, 0x66, 0x20, 0x202E, 0x29, 0x7B])
    assert bidi_control_balance.sub_threat_tag(v.sub) == "UnbalancedEmbedding"


# ─────────────────────────────────────────────────────────────────────
# ZeroWidthPayload
# ─────────────────────────────────────────────────────────────────────


def test_zw_empty_clear() -> None:
    assert zero_width_payload.detect([]).kind is ClassificationKind.CLEAR


def test_zw_ascii_clear() -> None:
    assert zero_width_payload.detect([0x48, 0x69]).kind is ClassificationKind.CLEAR


def test_zw_single_zwsp_bare() -> None:
    v = zero_width_payload.detect([0x61, 0x200B, 0x62])
    assert zero_width_payload.sub_threat_tag(v.sub) == "BareZeroWidth"


def test_zw_word_joiner_injection() -> None:
    v = zero_width_payload.detect([0x61, 0x2060, 0x62])
    assert zero_width_payload.sub_threat_tag(v.sub) == "WordJoinerInjection"


def test_zw_multiple_nnbsp_ai_watermark() -> None:
    v = zero_width_payload.detect([0x61, 0x202F, 0x62, 0x202F, 0x63])
    assert zero_width_payload.sub_threat_tag(v.sub) == "AiWatermarkNNBSP"


def test_zw_multiple_zwsp_binary_payload() -> None:
    v = zero_width_payload.detect([0x61, 0x200B, 0x200B, 0x200B, 0x200B])
    assert zero_width_payload.sub_threat_tag(v.sub) == "BinaryPayload"


def test_zw_annotation_misuse() -> None:
    v = zero_width_payload.detect([0x61, 0xFFF9, 0x62])
    assert zero_width_payload.sub_threat_tag(v.sub) == "AnnotationMisuse"


# ─────────────────────────────────────────────────────────────────────
# VariationSelectorPayload
# ─────────────────────────────────────────────────────────────────────


def test_vs_empty_clear() -> None:
    assert variation_selector_payload.detect([]).kind is ClassificationKind.CLEAR


def test_vs_ascii_clear() -> None:
    assert variation_selector_payload.detect([0x48, 0x69]).kind is ClassificationKind.CLEAR


def test_vs_illegal_target_latin() -> None:
    v = variation_selector_payload.detect([0x0041, 0xFE0F])
    assert variation_selector_payload.sub_threat_tag(v.sub) == "IllegalTarget"


def test_vs_direct_payload_byte() -> None:
    v = variation_selector_payload.detect([0x0061, 0xFE04, 0xFE01])
    assert variation_selector_payload.sub_threat_tag(v.sub) == "DirectPayload"
    assert v.recovered_bytes == bytes([0x41])


def test_vs_repeated_base() -> None:
    v = variation_selector_payload.detect([
        0x0061, 0xFE04, 0xFE04, 0xFE04, 0xFE04,
        0xFE04, 0xFE04, 0xFE04, 0xFE04,
    ])
    assert variation_selector_payload.sub_threat_tag(v.sub) == "RepeatedBase"


def test_vs_supplementary_on_latin() -> None:
    v = variation_selector_payload.detect([0x0041, 0xE0100])
    assert variation_selector_payload.sub_threat_tag(v.sub) == "IllegalTarget"


# ─────────────────────────────────────────────────────────────────────
# HomoglyphConfusable
# ─────────────────────────────────────────────────────────────────────


def test_homoglyph_empty_clear() -> None:
    assert homoglyph_confusable.detect([]).kind is ClassificationKind.CLEAR


def test_homoglyph_pure_ascii_clear() -> None:
    v = homoglyph_confusable.detect([0x68, 0x65, 0x6C, 0x6C, 0x6F])
    assert v.kind is ClassificationKind.CLEAR


def test_homoglyph_nethereum_cyrillic_e_target_match() -> None:
    # "Nethereum" with the second 'e' (between r and u) replaced by
    # Cyrillic SMALL LETTER IE (U+0435) — the Oct 2025 NuGet
    # supply-chain attack vector.
    v = homoglyph_confusable.detect(
        [0x4E, 0x65, 0x74, 0x68, 0x65, 0x72, 0x0435, 0x75, 0x6D]
    )
    assert v.kind is ClassificationKind.HAZARD
    assert homoglyph_confusable.sub_threat_tag(v.sub) == "TargetMatch"
    assert isinstance(v.sub, homoglyph_confusable.TargetMatch)
    assert v.sub.target == "Nethereum"


def test_homoglyph_math_alpha_bold_a() -> None:
    # U+1D400 MATHEMATICAL BOLD CAPITAL A.
    v = homoglyph_confusable.detect([0x1D400])
    assert v.kind is ClassificationKind.HAZARD
    assert homoglyph_confusable.sub_threat_tag(v.sub) == "MathAlpha"


def test_homoglyph_math_alpha_count() -> None:
    v = homoglyph_confusable.detect([0x1D400, 0x1D401, 0x1D402])
    assert isinstance(v.sub, homoglyph_confusable.MathAlpha)
    assert v.sub.count == 3


def test_homoglyph_fullwidth_a() -> None:
    # U+FF21 FULLWIDTH LATIN CAPITAL LETTER A.
    v = homoglyph_confusable.detect([0xFF21])
    assert v.kind is ClassificationKind.HAZARD
    assert homoglyph_confusable.sub_threat_tag(v.sub) == "WidthClass"


def test_homoglyph_skeleton_cyrillic_to_latin() -> None:
    # Cyrillic 'е' (U+0435) skeletons to Latin 'e' (U+0065).
    assert homoglyph_confusable.skeleton([0x0435]) == [0x0065]


def test_homoglyph_iterated_skeleton_fixed_point() -> None:
    assert homoglyph_confusable.iterated_skeleton([0x61]) == [0x61]


def test_homoglyph_math_block_predicate() -> None:
    assert homoglyph_confusable.is_math_alphanumeric(0x1D400)
    assert homoglyph_confusable.is_math_alphanumeric(0x1D7FF)
    assert not homoglyph_confusable.is_math_alphanumeric(0x1D3FF)
    assert not homoglyph_confusable.is_math_alphanumeric(0x1D800)


def test_homoglyph_fullwidth_block_predicate() -> None:
    assert homoglyph_confusable.is_fullwidth_halfwidth(0xFF01)
    assert homoglyph_confusable.is_fullwidth_halfwidth(0xFFEF)
    assert not homoglyph_confusable.is_fullwidth_halfwidth(0xFF00)
    assert not homoglyph_confusable.is_fullwidth_halfwidth(0xFFF0)


def test_homoglyph_decomposition_swap_a_grave() -> None:
    # 'A' (U+0041) + COMBINING GRAVE ACCENT (U+0300) is not in NFC;
    # to_nfc composes it into À (U+00C0).
    v = homoglyph_confusable.detect([0x0041, 0x0300])
    assert v.kind is ClassificationKind.HAZARD
    assert homoglyph_confusable.sub_threat_tag(v.sub) == "DecompositionSwap"


def test_homoglyph_cross_script_latin_hebrew() -> None:
    # Latin 'a' (U+0061) + Hebrew ALEF (U+05D0) — disjoint scripts,
    # neither in confusables.  Fires CrossScriptMix.
    v = homoglyph_confusable.detect([0x0061, 0x05D0])
    assert v.kind is ClassificationKind.HAZARD
    assert homoglyph_confusable.sub_threat_tag(v.sub) == "CrossScriptMix"


def test_homoglyph_pure_greek_clear() -> None:
    # "λόγος" — single-script Greek.
    v = homoglyph_confusable.detect(
        [0x03BB, 0x03CC, 0x03B3, 0x03BF, 0x03C2]
    )
    assert v.kind is ClassificationKind.CLEAR
