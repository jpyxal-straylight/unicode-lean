#!/usr/bin/env bash
# Verify the bundled UCD source files match the SHA-256 hashes pinned
# in `Unicode/Ucd/SHA256SUMS`. Tampering with a UCD `.txt` file would
# allow a `native_decide` over those bytes to lie, so the guard
# enforces byte-exact equality with the publication that was committed
# at release time.

set -euo pipefail

cd "$(dirname "$0")/../Unicode/Ucd"

if [ ! -f SHA256SUMS ]; then
  echo "FATAL: SHA256SUMS missing under Unicode/Ucd/"
  exit 1
fi

# `sha256sum -c` succeeds iff every listed file matches its hash.
sha256sum -c --strict --quiet SHA256SUMS

echo "clean: UCD source files match SHA-256 manifest"
