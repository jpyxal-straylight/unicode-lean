#!/usr/bin/env bash
# Verify the bundled UCD source files match the SHA-256 hashes
# pinned in data/SHA256SUMS.  Run as a CI gate or after any change
# under data/ — a mismatch indicates either an unintentional edit
# to vendored Unicode data or an attacker-induced table swap.

set -euo pipefail

cd "$(dirname "$0")/../data"

if [ ! -f UCD-VERSION ]; then
    echo "FATAL: data/UCD-VERSION missing" >&2
    exit 1
fi

if [ ! -f SHA256SUMS ]; then
    echo "FATAL: data/SHA256SUMS missing" >&2
    exit 1
fi

sha256sum -c --strict --quiet SHA256SUMS
echo "clean: UCD source files match SHA-256 manifest"
