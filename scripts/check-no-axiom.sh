#!/usr/bin/env bash
# Fail if any `.lean` file under `Unicode/` declares a new `axiom`, uses
# the `axiom` keyword, or invokes `unsafe`-marked tactics. Lean 4 core
# has its own axioms (propext, Quot.sound, Classical.choice) that are
# part of the trusted base; this guard prevents callers from adding
# project-local axioms or unsafe escape hatches.

set -euo pipefail

cd "$(dirname "$0")/.."

# `axiom <name> :` declarations.
axiom_hits="$(grep -rnE '^[[:space:]]*axiom[[:space:]]+[A-Za-z_]' \
    --include='*.lean' Unicode/ \
    | grep -v '^[^:]*:[0-9]*:[[:space:]]*--' \
    || true)"
if [ -n "$axiom_hits" ]; then
  echo "FATAL: project-local axiom declared:"
  echo "$axiom_hits"
  exit 1
fi

# `unsafe` keyword (function attributes, blocks, casts).
unsafe_hits="$(grep -rnE '\bunsafe\b' \
    --include='*.lean' Unicode/ \
    | grep -v '^[^:]*:[0-9]*:[[:space:]]*--' \
    | grep -v 'isUnsafeTactic\|unsafeFn' \
    || true)"
if [ -n "$unsafe_hits" ]; then
  echo "FATAL: \`unsafe\` keyword found:"
  echo "$unsafe_hits"
  exit 1
fi

# `unsafePerformIO`, `unsafeCast`, `Lean.ofReduceBool`, `Lean.reduceBool`.
runtime_escape_hits="$(grep -rnE '\b(unsafePerformIO|unsafeCast|Lean\.ofReduceBool|Lean\.reduceBool)\b' \
    --include='*.lean' Unicode/ \
    | grep -v '^[^:]*:[0-9]*:[[:space:]]*--' \
    || true)"
if [ -n "$runtime_escape_hits" ]; then
  echo "FATAL: runtime escape hatch found:"
  echo "$runtime_escape_hits"
  exit 1
fi

echo "clean: zero axiom, zero unsafe, zero runtime escape"
