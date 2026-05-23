//! Security Conformance Layer.
//!
//! Per-family modules under `unicode_rust::security::{covert,
//! identity, display, form, boundary, crypto}` import the shared
//! vocabulary from [`calculus`] and refine it into family-specific
//! verdict structures.

pub mod calculus;
pub mod covert;
pub mod identity;

pub use calculus::{
    default_severity, AdversaryTier, ClassificationKind, Family,
    HazardPosition, KeyValueAttribution, Severity,
};
