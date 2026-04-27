# Contributing

This repository ships a machine-checked specification of the Unicode
standard at UCD 17.0.0 under Lean 4.28.0. Contributions are welcome
under the same Apache-2.0 license that covers the existing source.

## Local Workflow

```bash
# Enter the dev shell (installs the pinned Lean toolchain via elan).
nix develop

# Build the full library. First build downloads the toolchain and
# elaborates every `.lean` file under `Unicode/`. Subsequent builds
# are incremental.
lake build

# Run the full set of source-level guards locally before opening a
# pull request. CI runs the same scripts.
bash scripts/check-sorry.sh
bash scripts/check-no-axiom.sh
bash scripts/check-orphan-files.sh
bash scripts/check-ucd-hashes.sh

# Status report (file count, theorem count, sorry count, per-pillar
# progress).
nix run
```

## Pull-Request Checklist

A pull request must satisfy every item below before review. The
hardening job in CI enforces 1 through 4 mechanically.

1. `bash scripts/check-sorry.sh` exits clean. No `sorry`, no `admit`.
2. `bash scripts/check-no-axiom.sh` exits clean. No project-local
   `axiom`, no `unsafe`, no `unsafePerformIO` / `unsafeCast` /
   `Lean.ofReduceBool` / `Lean.reduceBool`.
3. `bash scripts/check-orphan-files.sh` exits clean. Every `.lean`
   file under `Unicode/` is transitively imported from `Unicode.lean`.
4. `bash scripts/check-ucd-hashes.sh` exits clean. Every UCD source
   file under `Unicode/Ucd/` matches its SHA-256 in `SHA256SUMS`.
5. `lake build` succeeds with no warnings. Warnings in Lean are
   guardrails for downstream callers; suppress none of them with
   `set_option linter.* false`.
6. The headline smoke targets succeed:
   - `lake build Unicode.Normalization.QuickCheckSoundnessTheorem`
   - `lake build Unicode.Precis.Preparation`
   - `lake build Unicode.Bidi.Algorithm`
   - `lake build Unicode.Confusables`
7. New theorems carry a docstring stating what they prove. New
   definitions carry a docstring naming the standard section they
   correspond to (e.g. "UAX #15 §3.1", "RFC 8264 §5.2.1").
8. The commit message follows the repository's existing convention:
   one-line subject in imperative mood, optional body explaining the
   why. No marketing language, no emoji.

## UCD Updates

Bumping the bundled UCD version is a coordinated change:

1. Replace the relevant `.txt` files under `Unicode/Ucd/`.
2. Regenerate `Unicode/Ucd/SHA256SUMS`:
   ```bash
   ( cd Unicode/Ucd && sha256sum *.txt > SHA256SUMS )
   ```
3. Re-run the table extractor for every affected `Unicode/Generated/*`
   module. The extractor must emit deterministically — a second run
   must produce byte-identical output.
4. Re-elaborate the `Unicode/Normalization/QuickCheck*` proofs that
   depend on the updated tables.
5. Update the version pin in `README.md` and `flake.nix`.

## Toolchain Updates

The Lean toolchain is pinned in `lean-toolchain`. A toolchain bump:

1. Updates `lean-toolchain` to the new version.
2. Re-runs `nix flake lock` to update `flake.lock`.
3. Verifies `lake build` succeeds with no warnings on the new
   toolchain.
4. Verifies the reproducibility workflow's two-pass build determinism
   check still passes — major Lean releases occasionally change
   `.olean` framing in ways that must be audited.

## Branch Protection

The `main` branch should require, at minimum:

- Pull-request review from a CODEOWNER (`.github/CODEOWNERS`).
- Passing `ci / hardening` and `ci / build` checks (Tier 1).
- Linear history (no merge commits).
- Conversation resolution before merge.

Apply via the GitHub CLI:

```bash
gh api -X PUT repos/:owner/:repo/branches/main/protection \
  -F required_status_checks.strict=true \
  -F 'required_status_checks.contexts[]=ci / hardening' \
  -F 'required_status_checks.contexts[]=ci / build' \
  -F enforce_admins=true \
  -F required_pull_request_reviews.require_code_owner_reviews=true \
  -F required_pull_request_reviews.required_approving_review_count=1 \
  -F required_linear_history=true \
  -F allow_force_pushes=false \
  -F allow_deletions=false \
  -F required_conversation_resolution=true \
  -F restrictions=
```

The Tier 2 `reproducibility` workflow runs nightly and on touches
to `flake.nix` / `flake.lock` / `lakefile.lean` / `lean-toolchain`.
Failures there are tracked as issues; they are not merge-blocking
because the Tier 1 build already verifies that the library
elaborates clean — Tier 2 verifies that the elaboration is
reproducible.

## Reporting Security Issues

See `SECURITY.md`. Do not file security-relevant defects in the
public issue tracker.
