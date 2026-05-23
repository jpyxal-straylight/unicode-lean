"""Security Conformance Layer — detector families and shared vocabulary.

The package's public surface re-exports the per-family detectors
along with the shared verdict vocabulary (``Family``, ``Severity``,
``AdversaryTier``, ``ClassificationKind``, ``HazardPosition``,
``KeyValueAttribution``).
"""

from . import covert, identity
from .calculus import (
    AdversaryTier,
    ClassificationKind,
    Family,
    HazardPosition,
    KeyValueAttribution,
    Severity,
    default_severity,
)

__all__ = [
    "AdversaryTier",
    "ClassificationKind",
    "Family",
    "HazardPosition",
    "KeyValueAttribution",
    "Severity",
    "covert",
    "default_severity",
    "identity",
]
