#!/usr/bin/env bash
# State-level red-team — C++ sanitizer pass.
#
# Rebuilds the C++ port with `-fsanitize=address,undefined` and
# runs the full doctest suite + the 100 000-input differential
# runner.  Any sanitizer finding fails the script.
#
# Coverage:
#   - AddressSanitizer (ASAN)     — buffer overflow, use-after-free,
#                                    use-after-return, stack overflow,
#                                    double-free, leak (LSAN runs at
#                                    exit by default with ASAN on Linux)
#   - UndefinedBehaviorSanitizer  — integer overflow, signed shift,
#                                    null deref, misaligned access,
#                                    div-by-zero, …
#
# Pre-req: rust-port has generated /tmp/diff_corpus.jsonl (run
# `cargo test --test diff_runner --release diff_gen_corpus --
# --nocapture` from the rust-port branch first).

set -euo pipefail

cd "$(dirname "$0")/.."

BUILD_DIR=build-sanitize

echo "===> Configure $BUILD_DIR with ASAN + UBSAN"
cmake -S . -B "$BUILD_DIR" \
    -DCMAKE_CXX_FLAGS='-fsanitize=address,undefined -fno-sanitize-recover=all -g -O1' \
    -DCMAKE_EXE_LINKER_FLAGS='-fsanitize=address,undefined' \
    -DUNICODE_CPP_BUILD_TESTS=ON > /dev/null

echo "===> Build unicode_cpp_tests + diff_runner"
cmake --build "$BUILD_DIR" --target unicode_cpp_tests > /dev/null
g++ -std=c++23 -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all \
    -Iinclude -o "$BUILD_DIR/diff_runner" tools/diff_runner.cpp

echo "===> Run unicode_cpp_tests (124 cases, 517 assertions)"
if "$BUILD_DIR/test/unicode_cpp_tests"; then
    echo "    ASAN+UBSAN clean across the test suite"
else
    echo "    sanitizer findings in the test suite"
    exit 1
fi

echo "===> Run diff_runner over /tmp/diff_corpus.jsonl"
if [ ! -f /tmp/diff_corpus.jsonl ]; then
    echo "    /tmp/diff_corpus.jsonl missing — generate it from the rust-port:"
    echo "      cargo test --test diff_runner --release diff_gen_corpus -- --nocapture"
    exit 1
fi
"$BUILD_DIR/diff_runner" > /tmp/cpp_diff_sanitize.jsonl 2> /tmp/cpp_sanitize.stderr
lines=$(wc -l < /tmp/cpp_diff_sanitize.jsonl)
stderr_lines=$(wc -l < /tmp/cpp_sanitize.stderr)
echo "    diff_runner produced $lines verdict lines, $stderr_lines stderr lines"
if [ "$stderr_lines" -ne 0 ]; then
    echo "    sanitizer findings under diff_runner — see /tmp/cpp_sanitize.stderr"
    head -20 /tmp/cpp_sanitize.stderr
    exit 1
fi

echo
echo "ASAN + UBSAN clean: $lines differential inputs + 124 doctest cases + 517 assertions"
