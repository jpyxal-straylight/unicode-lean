"""Shared verdict vocabulary for the Security Conformance Layer.

Per-family modules under ``unicode_python.security.{covert,
identity,display,form,boundary,crypto}`` import this module and
refine the shared vocabulary into family-specific verdict
structures.
"""

from dataclasses import dataclass, field
from enum import Enum


class Family(Enum):
    """The detector modules.  The order is the order in which the
    aggregator walks them and the priority order callers can rely on
    when composing verdicts across modules."""

    TAG_BLOCK_PAYLOAD = "TagBlockPayload"
    VARIATION_SELECTOR_PAYLOAD = "VariationSelectorPayload"
    ZERO_WIDTH_PAYLOAD = "ZeroWidthPayload"
    SURROGATE_REASSEMBLY = "SurrogateReassembly"
    BIDI_CONTROL_BALANCE = "BidiControlBalance"
    HOMOGLYPH_CONFUSABLE = "HomoglyphConfusable"
    MIXED_SCRIPT_ADMISSIBILITY = "MixedScriptAdmissibility"
    EMOJI_ZWJ_INTEGRITY = "EmojiZwjIntegrity"
    SKIN_TONE_VARIATION_FORGERY = "SkinToneVariationForgery"
    SOURCE_DISPLAY_DIVERGENCE = "SourceDisplayDivergence"
    FILENAME_DISGUISE = "FilenameDisguise"
    RTL_INJECTION = "RtlInjection"
    RENDERER_DIVERGENCE = "RendererDivergence"
    NORMALIZATION_BOMB = "NormalizationBomb"
    STREAM_SAFE_VIOLATION = "StreamSafeViolation"
    LOCALE_CASE_INVERSION = "LocaleCaseInversion"
    CASE_EXPANSION_MISMATCH = "CaseExpansionMismatch"
    WIDTH_CLASS_CONFUSION = "WidthClassConfusion"
    NFC_IDEMPOTENCE_WITNESS = "NfcIdempotenceWitness"
    IDENTIFIER_FORM_DRIFT = "IdentifierFormDrift"
    COVERT_DISPLAY_COMPOUND = "CovertDisplayCompound"
    CONFUSABLE_BIDI_COMPOUND = "ConfusableBidiCompound"
    ADMISSIBILITY_FORM_DRIFT = "AdmissibilityFormDrift"
    BIP39_CANONICAL = "Bip39Canonical"
    HASH_INPUT_STABILITY = "HashInputStability"
    AI_WATERMARK_DETECTABILITY = "AiWatermarkDetectability"


class Severity(Enum):
    """Ordered severity vocabulary.  Strictly less-than:
    ``INFORMATIONAL < LOW < MODERATE < HIGH < CRITICAL``."""

    INFORMATIONAL = 0
    LOW = 1
    MODERATE = 2
    HIGH = 3
    CRITICAL = 4


class AdversaryTier(Enum):
    """Five-tier adversary capability hierarchy.

    A tier-N adversary has all capabilities of tier (N-1) plus the
    tier-N additions:

      * A0 — passive observer
      * A1 — local injector (single-input attack)
      * A2 — pipeline injector (browser → API → DB → AI)
      * A3 — supply-chain injector (registers a package or
        identifier)
      * A4 — model-adaptive (tokenizer-query capable)
    """

    A0 = 0
    A1 = 1
    A2 = 2
    A3 = 3
    A4 = 4


class ClassificationKind(Enum):
    """The verdict kind, independent of any family-specific
    sub-threat payload."""

    CLEAR = "clear"
    HAZARD = "hazard"
    COMPOUND = "compound"
    INFORMATIONAL = "informational"


def default_severity(kind: ClassificationKind) -> Severity:
    """The default severity associated with each classification
    kind.  Families can override at the verdict level."""
    if kind is ClassificationKind.CLEAR:
        return Severity.INFORMATIONAL
    if kind is ClassificationKind.HAZARD:
        return Severity.MODERATE
    if kind is ClassificationKind.COMPOUND:
        return Severity.HIGH
    return Severity.INFORMATIONAL


@dataclass(frozen=True, slots=True)
class HazardPosition:
    """A position within a codepoint sequence, optionally enriched
    with a line / column when the input is source-code shaped."""

    cp_offset: int
    line: int | None = None
    column: int | None = None


@dataclass(slots=True)
class KeyValueAttribution:
    """A flexible attribution dictionary — string keys to string
    values.  Each family defines its own attribution schema; this
    is the shared container."""

    entries: list[tuple[str, str]] = field(default_factory=list)

    def push(self, key: str, value: str) -> None:
        self.entries.append((key, value))

    def get(self, key: str) -> str | None:
        for k, v in self.entries:
            if k == key:
                return v
        return None


__all__ = [
    "AdversaryTier",
    "ClassificationKind",
    "Family",
    "HazardPosition",
    "KeyValueAttribution",
    "Severity",
    "default_severity",
]
