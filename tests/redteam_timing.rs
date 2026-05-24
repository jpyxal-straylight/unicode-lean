//! Timing side-channel — empirical verification of constant-time
//! `find_target_match` discipline.
//!
//! Threat model.  An attacker invokes the detector with
//! attacker-controlled inputs and measures response time.  In a
//! variable-time implementation, matching the FIRST target in the
//! curated list is faster than matching the LAST (the early-break
//! short-circuit halves the work for early matches).  Over many
//! samples this leak is exploitable: the attacker can fingerprint
//! curated-list membership without ever seeing the verdict.
//!
//! Mitigation (Move 4 of state-level red-team plan).
//! `find_target_match` now walks the entire curated target list
//! every call.  Equality via `ct_u32_slice_eq` accumulates the
//! comparison bit without early-breaking on first inequality.
//! Per-target work is independent of input.
//!
//! This test runs `detect` many times against four inputs that
//! exercise different match positions and asserts the
//! coefficient-of-variation (stddev / mean) is below threshold.

use std::time::Instant;

use unicode_rust::security::identity::homoglyph_confusable as h;

const ITERATIONS_PER_INPUT: u32 = 50_000;
const VARIANCE_THRESHOLD: f64 = 0.20;  // 20% — generous for noisy benchmarks

fn time_ns_per_call(input: &[u32]) -> f64 {
    let start = Instant::now();
    for _ in 0..ITERATIONS_PER_INPUT {
        let v = h::detect(input);
        // Defeat dead-code elimination by reading the verdict.
        std::hint::black_box(&v);
    }
    let elapsed_ns = start.elapsed().as_nanos() as f64;
    elapsed_ns / (ITERATIONS_PER_INPUT as f64)
}

#[test]
fn timing_constant_across_match_positions() {
    // Four inputs exercising different code paths through
    // find_target_match.  All four must take comparable time
    // under the constant-time discipline.

    // 1. First target literally — self-match guard fires on first
    //    iteration in the variable-time version.
    let first_target_self = [0x4E, 0x65, 0x74, 0x68, 0x65, 0x72,
                              0x65, 0x75, 0x6D]; // "Nethereum"
    // 2. First target with Cyrillic — match fires on first
    //    iteration in the variable-time version.
    let first_target_match = [0x4E, 0x65, 0x74, 0x68, 0x65, 0x72,
                               0x0435, 0x75, 0x6D];
    // 3. No match — variable-time walks the full list looking.
    let no_match = [0x78, 0x79, 0x7A, 0x77, 0x76];  // "xyzwv"
    // 4. Random Cyrillic + Latin mix — fires CrossScriptMix.
    let cross_mix = [0x61, 0x0430, 0x62, 0x0431, 0x63, 0x0432];

    // Warm up to stabilize cache + branch predictor.
    for _ in 0..1000 {
        std::hint::black_box(h::detect(&first_target_self));
        std::hint::black_box(h::detect(&first_target_match));
        std::hint::black_box(h::detect(&no_match));
        std::hint::black_box(h::detect(&cross_mix));
    }

    let t1 = time_ns_per_call(&first_target_self);
    let t2 = time_ns_per_call(&first_target_match);
    let t3 = time_ns_per_call(&no_match);
    let t4 = time_ns_per_call(&cross_mix);

    let mean = (t1 + t2 + t3 + t4) / 4.0;
    let variance = ((t1 - mean).powi(2)
        + (t2 - mean).powi(2)
        + (t3 - mean).powi(2)
        + (t4 - mean).powi(2))
        / 4.0;
    let stddev = variance.sqrt();
    let cv = stddev / mean;

    eprintln!(
        "timing per-call (ns):\n  first_target_self   = {:.0}\n  first_target_match  = {:.0}\n  no_match            = {:.0}\n  cross_mix           = {:.0}",
        t1, t2, t3, t4,
    );
    eprintln!(
        "  mean = {:.0} ns | stddev = {:.0} ns | CoV = {:.3}",
        mean, stddev, cv,
    );

    // Constant-time claim: timing variance across input classes
    // is below VARIANCE_THRESHOLD.  Pre-fix variable-time impl
    // had CoV ≈ 0.5 (50% variance between matching first vs no
    // match).  Post-fix should be < 0.20.
    assert!(
        cv < VARIANCE_THRESHOLD,
        "Timing CoV {:.3} exceeds threshold {:.2} — find_target_match has an exploitable timing leak",
        cv, VARIANCE_THRESHOLD,
    );
}
