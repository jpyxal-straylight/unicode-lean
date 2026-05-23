#!/usr/bin/env bash
# Verify the bundled UCD source files match the SHA-256 hashes pinned
# in `data/SHA256SUMS`. unicode-hs's table-generation step reads these
# files; tampering would allow the generator to lie. The guard enforces
# byte-exact equality with the publication committed at release time.
#
# Mirrors `scripts/check-ucd-hashes.sh` in the sibling unicode-lean
# repo, where the same hashes guard the Lean validator's
# `native_decide` inputs.

set -euo pipefail

cd "$(dirname "$0")/../data"

if [ ! -f UCD-VERSION ]; then
  echo "FATAL: data/UCD-VERSION missing"
  exit 1
fi

# When the data/ directory is populated with vendored UCD .txt files
# (Phase 3 onwards), SHA256SUMS will exist and this script enforces
# the manifest. Until then it is a no-op that documents the pattern.
if [ -f SHA256SUMS ]; then
  sha256sum -c --strict --quiet SHA256SUMS
  echo "clean: UCD source files match SHA-256 manifest"
else
  echo "skip: no SHA256SUMS yet — data/ is empty in this Phase 1 slice"
fi
