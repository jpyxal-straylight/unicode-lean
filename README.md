# unicode-rust

Strict Unicode-as-attack-surface conformance for Rust — covert-
channel detection, identity-spoofing detection, display-integrity
checks, form-stability checks, cross-detector boundary checks,
and cryptographic-stability detection.

The crate will ship strict RFC 3629 UTF-8 codec primitives, the
26 detector families documented at the repo root, and the
admissibility predicate that lifts the per-family verdicts into
a totally-ordered strictness gate.

This branch is currently a placeholder; the crate will ship to
`crates.io` once an algorithmic re-implementation has been
validated against the shared UCD 17.0.0 / UCA 16.0.0 conformance
fixtures.
