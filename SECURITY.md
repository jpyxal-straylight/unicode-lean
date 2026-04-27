# Security Policy

## Threat Model

This repository is a machine-checked specification of the Unicode standard.
The artifacts that downstream consumers rely on are:

- The Lean source files under `Unicode/`, which type-check zero `sorry`
  and zero project-local `axiom`s under Lean 4.28.0.
- The UCD source files under `Unicode/Ucd/`, which are pinned by
  SHA-256 in `Unicode/Ucd/SHA256SUMS` and verified in CI.
- The Generated tables under `Unicode/Generated/`, which are derived
  deterministically from the UCD source files at build time.

A security-relevant defect is anything that allows the headline
theorems (NFC quick-check soundness, PRECIS preparation idempotence,
Bidirectional Algorithm pipeline shape, confusable-skeleton
equivalence) to be subverted without the build failing. Examples:

- A proof gap in a load-bearing module not caught by the `sorry` /
  `admit` guards.
- A drift between a UCD `.txt` file and its pinned SHA-256 not
  caught by `scripts/check-ucd-hashes.sh`.
- A project-local `axiom` introduced under a name not recognised
  by `scripts/check-no-axiom.sh`.
- An orphan `.lean` file present on disk but not transitively
  imported from `Unicode.lean`, so it skips the headline build.
- A runtime escape hatch (`unsafe`, `unsafePerformIO`, `unsafeCast`,
  `Lean.ofReduceBool`, `Lean.reduceBool`) introduced under a name
  not recognised by `scripts/check-no-axiom.sh`.

Build reproducibility — two consecutive `lake build` runs producing
byte-identical `.olean` artifacts — is verified by the nightly
reproducibility workflow.

## Reporting a Vulnerability

Security reports should be sent privately, not in a public issue.
Use GitHub's private-vulnerability-reporting form on this repository,
or email the maintainer listed in `.github/CODEOWNERS`.

A report should include:

- The affected file path and line range.
- The class of defect (proof gap, table drift, axiom introduction,
  orphan file, runtime escape, build nondeterminism, or other).
- Where applicable, a minimal reproduction: the Lean expression that
  type-checks against an unsound hypothesis, or the UCD byte
  sequence that bypasses the SHA-256 check.

The maintainer will acknowledge a report within seven days and will
share a remediation plan, including the affected commit range, before
public disclosure.

## Supported Versions

Only the most recent minor release on `main` is supported. The
project follows semantic versioning at the level of the headline
theorem signatures: a major-version bump signals that a theorem name
or statement on the public surface changed.

## Cryptographic Provenance

The UCD source files in `Unicode/Ucd/` are byte-exact copies of the
Unicode 17.0.0 publication. Their SHA-256 hashes are pinned in
`Unicode/Ucd/SHA256SUMS` and verified by `scripts/check-ucd-hashes.sh`
on every push and pull request. Tampering with a UCD `.txt` file
without updating the manifest will fail the `ci / hardening` job.

The nightly reproducibility workflow publishes a manifest of `.olean`
SHA-256 hashes as a build artifact (`oleans-sha256-<commit-sha>`) so
downstream auditors can verify their local build matches the canonical
build. Artefacts are retained for 90 days per the default
`actions/upload-artifact` policy.

Source-of-truth artifacts — the UCD source files under `Unicode/Ucd/`,
the lakefile, the `lean-toolchain` pin, the flake declaration, and
the CI scripts under `scripts/` — are listed individually in
`.github/CODEOWNERS` so that tampering shows up in `git blame` and
requires CODEOWNER review at merge time.
