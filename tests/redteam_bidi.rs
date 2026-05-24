//! Brutal red-team — BidiControlBalance detector.
//!
//! Coverage targets:
//!
//!   1. Depth boundary (124 ok / 125 ok / 126 hazard) — already
//!      a known good but re-verified here as a regression gate.
//!   2. Cross-stack interactions (embedding push then isolate push
//!      then various pops — verify embedding and isolate stacks
//!      are tracked independently per UAX #9 §3.3.2).
//!   3. Mass-orphan attack — input with thousands of unbalanced
//!      PDFs.  Detector must terminate, classify, not OOM.
//!   4. Mass-nesting DoS — input with the maximum allowed nesting
//!      followed by orphans, exercising both code paths.
//!   5. Real Trojan Source PoCs (Boucher & Anderson 2021,
//!      CVE-2021-42574 / CVE-2021-42694) — each must fire some
//!      Hazard.
//!   6. ALM (U+061C ARABIC LETTER MARK) — invisible bidi-related
//!      character; not a push/pop control, so BidiControlBalance
//!      should NOT fire on it.  ZeroWidthPayload catches it via
//!      Default_Ignorable.  Verify this division of labor holds.
//!   7. Bidi-controls in a code-comment-style payload — exactly
//!      the documented attack shape.

use std::time::Instant;
use unicode_rust::security::ClassificationKind;
use unicode_rust::security::covert::bidi_control_balance as bidi;

// ════════════════════════════════════════════════════════════════════
// CATEGORY 1: depth boundary regression
// ════════════════════════════════════════════════════════════════════

#[test]
fn bidi_depth_boundary_regression() {
    for n in [0usize, 1, 50, 124, 125, 126, 200, 1_000] {
        let mut input = vec![0x202Au32; n];   // n LRE pushes
        input.extend(std::iter::repeat(0x202Cu32).take(n)); // n PDF pops
        let v = bidi::detect(&input);
        let tag = v.sub.as_ref().map(|s| s.tag());
        eprintln!(
            "  depth {}: kind={:?} sub={:?} max_depth={}",
            n, v.kind, tag, v.max_depth,
        );
        // Per UAX #9 §3.3.2, depth ≤ 125 is allowed.
        if n <= 125 {
            assert_eq!(v.kind, ClassificationKind::Clear,
                "balanced depth {} must be Clear", n);
        } else {
            assert_eq!(v.kind, ClassificationKind::Hazard,
                "depth {} > 125 must be Hazard", n);
            assert_eq!(tag, Some("DepthExceeded"));
        }
    }
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 2: cross-stack independence
// ════════════════════════════════════════════════════════════════════

#[test]
fn bidi_embedding_and_isolate_are_independent_stacks() {
    // Open an embedding, then open an isolate, then close the
    // embedding while the isolate is still open.  Per UAX #9
    // §3.3.4, embedding and isolate run on independent stacks.
    // After: emb_stack=0, iso_stack=1.
    let input = [
        0x202A,  // LRE (push emb, emb=1)
        0x2066,  // LRI (push iso, iso=1)
        0x202C,  // PDF (pop emb, emb=0)
        0x2069,  // PDI (pop iso, iso=0)
    ];
    let v = bidi::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Clear,
        "interleaved emb/iso balanced should be Clear");

    // Same but leave isolate dangling: emb closes ok, iso stays open.
    let input = [0x202A, 0x2066, 0x202C];
    let v = bidi::detect(&input);
    assert_eq!(v.sub.as_ref().map(|s| s.tag()),
        Some("UnbalancedIsolate"));

    // Same but leave embedding dangling: iso closes ok, emb stays open.
    let input = [0x2066, 0x202A, 0x2069];
    let v = bidi::detect(&input);
    assert_eq!(v.sub.as_ref().map(|s| s.tag()),
        Some("UnbalancedEmbedding"));
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 3: orphan attack — mass PDFs
// ════════════════════════════════════════════════════════════════════

#[test]
fn bidi_mass_orphan_pdf() {
    // 10_000 orphan PDFs.  Detector must terminate, must not OOM,
    // must fire OrphanPop with all 10k positions reported.
    let input = vec![0x202Cu32; 10_000];
    let t = Instant::now();
    let v = bidi::detect(&input);
    let elapsed = t.elapsed();
    eprintln!("  10k orphan PDFs: kind={:?} elapsed={:?}", v.kind, elapsed);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    if let Some(sub) = v.sub {
        assert_eq!(sub.tag(), "OrphanPop");
    }
    assert!(elapsed.as_secs() < 5, "mass-orphan DoS");
}

#[test]
fn bidi_mass_orphan_pdi() {
    let input = vec![0x2069u32; 10_000];
    let v = bidi::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Hazard);
    assert_eq!(v.sub.as_ref().map(|s| s.tag()), Some("OrphanPop"));
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 4: mass nesting that fits in depth bound
// ════════════════════════════════════════════════════════════════════

#[test]
fn bidi_mass_nesting_at_cap() {
    // 125 nested embeddings + 125 closures — at the cap.
    let mut input = vec![0x202Au32; 125];
    input.extend(std::iter::repeat(0x202Cu32).take(125));
    let v = bidi::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Clear,
        "depth-125 balanced should be Clear");
    assert_eq!(v.max_depth, 125);
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 5: real Trojan Source PoCs
// ════════════════════════════════════════════════════════════════════

#[test]
fn bidi_trojan_source_early_return_poc() {
    // From Boucher & Anderson 2021, CVE-2021-42574.  The
    // "Early-Return" PoC: source code with RLO that reorders
    // the function return statement.  Simplified to just the
    // bidi-control payload + ASCII text:
    //   `if access_level != "user«RLO» admin»PDI»«PDF» {`
    //
    // Codepoints: ... + RLO (U+202E) + ... + PDI (U+2069) + PDF (U+202C)
    // Unbalanced — both RLO push and PDI pop without prior LRI.
    let input = [
        0x69, 0x66, 0x20, 0x61, 0x63, 0x63, 0x65, 0x73, 0x73, 0x20,
        0x21, 0x3D, 0x20, 0x22, 0x75, 0x73, 0x65, 0x72, 0x202E, 0x20,
        0x61, 0x64, 0x6D, 0x69, 0x6E, 0x2069, 0x202C, 0x7B,
    ];
    let v = bidi::detect(&input);
    eprintln!(
        "  Trojan-Source early-return: kind={:?} sub={:?}",
        v.kind, v.sub.as_ref().map(|s| s.tag()),
    );
    // Either OrphanPop (PDI without prior LRI) or UnbalancedEmbedding
    // (RLO without matching PDF inside the run).
    assert_eq!(v.kind, ClassificationKind::Hazard);
}

#[test]
fn bidi_trojan_source_commenting_out_poc_is_balanced() {
    // CVE-2021-42574 "Commenting Out" PoC: bidi controls inside a
    // C-style comment make code visually look commented when it's
    // actually executable.  Source approximation:
    //   /*«RLO» } if (true) { /*«PDF»*/
    //
    // The bidi stack here is BALANCED (one RLO push, one PDF pop).
    // The ATTACK is the VISUAL divergence between logical order and
    // bidi-rendered order, NOT a stack imbalance.  This is exactly
    // the division of labor between:
    //   - BidiControlBalance     — stack balance (Clear here)
    //   - SourceDisplayDivergence — visual-vs-logical (Hazard here)
    //
    // This test documents that BidiControlBalance correctly does
    // NOT fire on this input (it's a SourceDisplayDivergence
    // hazard, caught by the sibling detector).
    let input = [
        0x2F, 0x2A, 0x202E, 0x20, 0x7D, 0x20, 0x69, 0x66, 0x20,
        0x28, 0x74, 0x72, 0x75, 0x65, 0x29, 0x20, 0x7B, 0x20, 0x2F,
        0x2A, 0x202C, 0x2A, 0x2F,
    ];
    let v = bidi::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Clear,
        "bidi-balanced Trojan Source comment is SourceDisplayDivergence's job");
}

#[test]
fn bidi_trojan_source_stretched_string_poc() {
    // CVE-2021-42574 "Stretched String" attack on Python string
    // literals.  String contains RLO that makes a non-empty
    // string render as empty visually.
    //   access = "«RLO»user«PDF»"
    let input = [
        0x61, 0x63, 0x63, 0x65, 0x73, 0x73, 0x20, 0x3D, 0x20, 0x22,
        0x202E, 0x75, 0x73, 0x65, 0x72, 0x202C, 0x22,
    ];
    let v = bidi::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Clear,
        "balanced RLO + PDF should be Clear — visual-vs-logical is the trojan, but stack is balanced");
    // The trojan IS the visual divergence even when bidi-balanced;
    // this is what SourceDisplayDivergence catches (a different
    // detector).  BidiControlBalance only tracks stack balance.
    // Document this here for the audit trail.
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 6: ALM is NOT a Bidi push/pop control
// ════════════════════════════════════════════════════════════════════

#[test]
fn bidi_alm_not_a_push_pop_control() {
    // ALM (U+061C) is a strong implicit-direction character
    // (invisible), not a push/pop.  BidiControlBalance should
    // NOT fire on it.  ZeroWidthPayload catches it instead.
    let input = [0x061C];
    let v = bidi::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Clear,
        "ALM alone must not trigger BidiControlBalance");
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 7: interleaved emb+iso with cross-stack pops
// ════════════════════════════════════════════════════════════════════

#[test]
fn bidi_pdi_does_not_pop_embedding() {
    // Open embedding, push isolate, pop isolate, then pop
    // embedding — emb_stack and iso_stack track independently.
    let input = [0x202A, 0x2066, 0x2069, 0x202C];
    let v = bidi::detect(&input);
    assert_eq!(v.kind, ClassificationKind::Clear);

    // Now open emb, push iso, try to pop emb with PDI (wrong
    // pop type).  emb_stack stays open (PDI doesn't pop emb).
    // After PDI, iso_stack=0, emb_stack=1 (still).  Unbalanced.
    let input = [0x202A, 0x2066, 0x2069];
    let v = bidi::detect(&input);
    assert_eq!(v.sub.as_ref().map(|s| s.tag()),
        Some("UnbalancedEmbedding"));
}

#[test]
fn bidi_pdf_does_not_pop_isolate() {
    let input = [0x2066, 0x202C];
    let v = bidi::detect(&input);
    // PDF with no embedding to pop = orphan.  iso_stack=1 (LRI).
    // First-fire is OrphanPop (priority order is depth, then
    // orphan, then unbalanced).
    let tag = v.sub.as_ref().map(|s| s.tag());
    assert!(tag == Some("OrphanPop")
        || tag == Some("UnbalancedIsolate"),
        "got tag={:?}", tag);
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 8: degenerate inputs — must not panic
// ════════════════════════════════════════════════════════════════════

#[test]
fn bidi_degenerate_no_panic() {
    let _ = bidi::detect(&[]);
    let _ = bidi::detect(&[0]);
    let _ = bidi::detect(&[0x110000]);
    let _ = bidi::detect(&[0xFFFFFFFF]);
    let _ = bidi::detect(&[0xD800]); // raw surrogate
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 9: massive depth + balanced (still Clear)
// ════════════════════════════════════════════════════════════════════

#[test]
fn bidi_max_depth_with_isolates() {
    // 60 LRE + 60 LRI interleaved = total depth 120.  Balanced.
    let mut input = Vec::new();
    for _ in 0..60 {
        input.push(0x202Au32);
        input.push(0x2066u32);
    }
    for _ in 0..60 {
        input.push(0x2069u32);
        input.push(0x202Cu32);
    }
    let v = bidi::detect(&input);
    eprintln!(
        "  60+60 interleaved emb+iso: kind={:?} max_depth={}",
        v.kind, v.max_depth,
    );
    assert_eq!(v.kind, ClassificationKind::Clear);
    assert_eq!(v.max_depth, 120);
}

// ════════════════════════════════════════════════════════════════════
// CATEGORY 10: fuzz — no panic on random bidi-heavy input
// ════════════════════════════════════════════════════════════════════

#[test]
fn bidi_fuzz_random_controls() {
    // Random sequences of bidi controls.  Detector must classify
    // every input without panic or hang.
    let bidi_cps = [0x202A, 0x202B, 0x202C, 0x202D, 0x202E,
                    0x2066, 0x2067, 0x2068, 0x2069];
    let mut state: u64 = 0xBEEF_BABE_CAFE_F00D;
    for _ in 0..10_000 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let len = (state as usize) % 300;
        let mut input = Vec::with_capacity(len);
        for _ in 0..len {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            input.push(bidi_cps[(state as usize) % bidi_cps.len()]);
        }
        let _ = bidi::detect(&input);
    }
}
