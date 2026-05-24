//! Cross-port differential runner — Rust side.
//!
//! Two modes:
//!
//!   1. Generate corpus.  Writes /tmp/diff_corpus.jsonl with N
//!      input sequences as `{"id":<n>,"cps":[<u32>,…]}` JSONL.
//!      The corpus file is the SHARED artifact every port reads.
//!
//!   2. Run detect on corpus.  Reads /tmp/diff_corpus.jsonl,
//!      runs `homoglyph_confusable::detect` on each input, emits
//!      one JSONL line to stdout per input:
//!
//!        {"id":<n>,"cps":[…],"kind":"…","sub":"…","target":"…"}
//!
//! The Python and C++ ports run identical mode-2 runners against
//! the same corpus.  A bash orchestrator diffs the three outputs.
//! Any byte-level divergence is a port-drift bug.
//!
//! Generate corpus:
//!     cargo test --test diff_runner --release diff_gen_corpus -- --nocapture
//! Run against corpus (capture verdicts):
//!     cargo test --test diff_runner --release diff_run_against_corpus -- --nocapture > /tmp/rust_diff.jsonl

use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use unicode_rust::security::ClassificationKind;
use unicode_rust::security::identity::homoglyph_confusable as h;
use unicode_rust::security::identity::homoglyph_confusable::SubThreat;

const CORPUS_PATH: &str = "/tmp/diff_corpus.jsonl";

// ──────────────────────────────────────────────────────────────────────
// Shared cross-port PRNG.  xorshift64 with seed 0xC0FFEE_1234_5678.
// Same constants in python_runner.py and cpp diff_runner.cpp.
// ──────────────────────────────────────────────────────────────────────

const SEED: u64 = 0xC0FFEE_1234_5678;
const N_INPUTS: usize = 10_000;
const MAX_LEN: usize = 32;

struct Xorshift(u64);

impl Xorshift {
    fn new() -> Self {
        Self(SEED)
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

// Generate one input.  Mix of:
//   - pure ASCII (40%)
//   - Latin + Cyrillic look-alikes biased (20%)
//   - Math-alpha + fullwidth (10%)
//   - With combining marks / NFC drift (10%)
//   - With default-ignorable / whitespace (10%)
//   - Pure random valid scalar (10%)
fn gen_input(rng: &mut Xorshift, idx: usize) -> Vec<u32> {
    let len = (rng.next_u64() as usize) % (MAX_LEN + 1); // 0..=MAX_LEN
    let class = (rng.next_u64() % 10) as u8;
    let mut input = Vec::with_capacity(len);
    for _ in 0..len {
        let cp: u32 = match class {
            0..=3 => {
                // ASCII letters + digits
                let r = (rng.next_u64() % 62) as u32;
                if r < 26 {
                    0x61 + r // a..z
                } else if r < 52 {
                    0x41 + (r - 26) // A..Z
                } else {
                    0x30 + (r - 52) // 0..9
                }
            }
            4..=5 => {
                // Latin + Cyrillic look-alikes
                let r = (rng.next_u64() % 14) as u32;
                match r {
                    0 => 0x61, // a
                    1 => 0x65, // e
                    2 => 0x6F, // o
                    3 => 0x70, // p
                    4 => 0x63, // c
                    5 => 0x79, // y
                    6 => 0x78, // x
                    7 => 0x0430, // Cyrillic a
                    8 => 0x0435, // Cyrillic e
                    9 => 0x043E, // Cyrillic o
                    10 => 0x0440, // Cyrillic r
                    11 => 0x0441, // Cyrillic c
                    12 => 0x0443, // Cyrillic u
                    _ => 0x0445, // Cyrillic x
                }
            }
            6 => {
                // Math-alpha + fullwidth
                let r = rng.next_u64() % 2;
                if r == 0 {
                    0x1D400 + (rng.next_u64() % 0x400) as u32
                } else {
                    0xFF21 + (rng.next_u64() % 0x5A) as u32
                }
            }
            7 => {
                // Combining marks + NFC drift
                let r = rng.next_u64() % 4;
                match r {
                    0 => 0x0300, // combining grave
                    1 => 0x0301, // combining acute
                    2 => 0x0308, // combining diaeresis
                    _ => 0x0061 + (rng.next_u64() % 26) as u32, // Latin to combine with
                }
            }
            8 => {
                // Default-ignorable + whitespace
                let r = rng.next_u64() % 6;
                match r {
                    0 => 0x200B, // ZWSP
                    1 => 0x200C, // ZWNJ
                    2 => 0x200D, // ZWJ
                    3 => 0x2060, // WJ
                    4 => 0xFEFF, // BOM
                    _ => 0x202F, // NNBSP
                }
            }
            _ => {
                // Random valid scalar (skip surrogate range)
                let r = rng.next_u64() as u32 % 0x110000;
                if (0xD800..=0xDFFF).contains(&r) {
                    r + 0x800
                } else {
                    r
                }
            }
        };
        input.push(cp);
    }
    let _ = idx; // shut up rustc unused warning
    input
}

fn verdict_to_jsonl(id: usize, input: &[u32]) -> String {
    let v = h::detect(input);
    let kind = match v.kind {
        ClassificationKind::Clear => "Clear",
        ClassificationKind::Hazard => "Hazard",
        ClassificationKind::Compound => "Compound",
        ClassificationKind::Informational => "Informational",
    };
    let (sub_tag, target) = match &v.sub {
        None => ("null".to_string(), "null".to_string()),
        Some(SubThreat::TargetMatch { target }) => (
            "\"TargetMatch\"".to_string(),
            format!("\"{}\"", target.replace('"', "\\\"")),
        ),
        Some(SubThreat::MathAlpha { .. }) => {
            ("\"MathAlpha\"".to_string(), "null".to_string())
        }
        Some(SubThreat::WidthClass { .. }) => {
            ("\"WidthClass\"".to_string(), "null".to_string())
        }
        Some(SubThreat::DecompositionSwap { .. }) => (
            "\"DecompositionSwap\"".to_string(),
            "null".to_string(),
        ),
        Some(SubThreat::CrossScriptMix { .. }) => (
            "\"CrossScriptMix\"".to_string(),
            "null".to_string(),
        ),
        Some(SubThreat::RestrictionLow { .. }) => (
            "\"RestrictionLow\"".to_string(),
            "null".to_string(),
        ),
    };
    let cps_str: Vec<String> = input.iter().map(|cp| cp.to_string()).collect();
    format!(
        "{{\"id\":{},\"cps\":[{}],\"kind\":\"{}\",\"sub\":{},\"target\":{}}}",
        id,
        cps_str.join(","),
        kind,
        sub_tag,
        target,
    )
}

fn cps_to_json_array(cps: &[u32]) -> String {
    let s: Vec<String> = cps.iter().map(|cp| cp.to_string()).collect();
    format!("[{}]", s.join(","))
}

fn parse_corpus_line(line: &str) -> (usize, Vec<u32>) {
    // Minimal hand parser of `{"id":N,"cps":[a,b,c]}`.  No deps.
    let id_start = line.find("\"id\":").expect("id field") + 5;
    let id_end = line[id_start..].find(',').expect("id end") + id_start;
    let id: usize = line[id_start..id_end].parse().expect("id parse");
    let arr_start = line.find("\"cps\":[").expect("cps field") + 7;
    let arr_end = line[arr_start..].find(']').expect("cps end") + arr_start;
    let cps_str = &line[arr_start..arr_end];
    let cps: Vec<u32> = if cps_str.is_empty() {
        Vec::new()
    } else {
        cps_str
            .split(',')
            .map(|s| s.trim().parse().expect("cp parse"))
            .collect()
    };
    (id, cps)
}

#[test]
fn diff_gen_corpus() {
    // Mode 1 — generate the shared corpus.
    let mut f = File::create(CORPUS_PATH).expect("open corpus");
    let mut rng = Xorshift::new();
    for id in 0..N_INPUTS {
        let input = gen_input(&mut rng, id);
        writeln!(
            f,
            "{{\"id\":{},\"cps\":{}}}",
            id,
            cps_to_json_array(&input),
        )
        .expect("write corpus");
    }
    eprintln!("wrote {} entries to {}", N_INPUTS, CORPUS_PATH);
}

#[test]
fn diff_run_against_corpus() {
    // Mode 2 — read corpus, run detect, emit JSONL to stdout.
    let f = File::open(CORPUS_PATH).expect(
        "/tmp/diff_corpus.jsonl missing — run diff_gen_corpus first",
    );
    let reader = BufReader::new(f);
    let stdout = std::io::stdout();
    let mut lock = stdout.lock();
    for line in reader.lines() {
        let line = line.expect("read");
        let (id, cps) = parse_corpus_line(&line);
        let out_line = verdict_to_jsonl(id, &cps);
        writeln!(lock, "{}", out_line).expect("write");
    }
}
