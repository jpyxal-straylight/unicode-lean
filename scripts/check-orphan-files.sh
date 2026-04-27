#!/usr/bin/env bash
# Fail if any `.lean` file under `Unicode/` is not transitively imported
# from the root `Unicode.lean`. Orphan files compile in isolation but
# are NOT covered by the headline build / sorry / axiom guards, so they
# are a hiding place for unverified material.
#
# Portable to bash 3.x (macOS default) — no associative arrays, no
# bash-4-only features. Uses sorted tempfiles + `comm` for set
# operations.

set -euo pipefail

cd "$(dirname "$0")/.."

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

all_modules="$tmpdir/all"
reached="$tmpdir/reached"
queue="$tmpdir/queue"
seen="$tmpdir/seen"
imports="$tmpdir/imports"

# Collect every Lean module name under `Unicode.lean` and `Unicode/`.
find Unicode.lean Unicode/ -name '*.lean' -type f \
  | sed -e 's|\.lean$||' -e 's|/|.|g' \
  | LC_ALL=C sort -u > "$all_modules"

# BFS over imports starting from the `Unicode` root.
: > "$seen"
echo "Unicode" > "$queue"
while [ -s "$queue" ]; do
  current="$(head -n 1 "$queue")"
  tail -n +2 "$queue" > "$queue.next" && mv "$queue.next" "$queue"

  if grep -qxF "$current" "$seen"; then
    continue
  fi
  echo "$current" >> "$seen"

  module_path="$(echo "$current" | tr '.' '/').lean"
  [ -f "$module_path" ] || continue

  grep -hE '^import[[:space:]]+[A-Za-z_][A-Za-z0-9_.]*' "$module_path" \
    | awk '{print $2}' \
    | grep -E '^(Unicode|Unicode\.)' \
    > "$imports" || true
  while IFS= read -r imp; do
    [ -n "$imp" ] || continue
    if ! grep -qxF "$imp" "$seen"; then
      echo "$imp" >> "$queue"
    fi
  done < "$imports"
done

LC_ALL=C sort -u "$seen" > "$reached"

# Set difference: modules on disk that the import graph never reached.
orphans="$(comm -23 "$all_modules" "$reached")"

if [ -n "$orphans" ]; then
  count="$(printf '%s\n' "$orphans" | wc -l | tr -d ' ')"
  echo "FATAL: $count orphan file(s) — present on disk but not transitively imported from Unicode.lean:"
  printf '  %s\n' "$orphans"
  exit 1
fi

echo "clean: every .lean file under Unicode/ is transitively imported from the root"
