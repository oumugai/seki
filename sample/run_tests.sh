#!/usr/bin/env bash
# Run every sample's test files (tests*.seki), reporting pass / fail per suite.
# Exits non-zero on any failure.
#
# Usage:
#   ./sample/run_tests.sh
#
# Requires target/release/seki to exist (run `cargo build --release` first).

set -u
cd "$(dirname "$0")/.."

SEKI=./target/release/seki
if [ ! -x "$SEKI" ]; then
    echo "Building seki..." >&2
    cargo build --release || { echo "build failed"; exit 1; }
fi

total_failed=0
total_suites=0
total_passed=0
failed_list=()

# Find all tests*.seki files (tests.seki, tests_property.seki, tests_metadata.seki, ...)
# Sort by sample directory, then by filename so tests.seki runs first.
for suite in $(ls sample/*/tests*.seki 2>/dev/null | sort); do
    total_suites=$((total_suites + 1))
    echo ""
    echo "######################################################################"
    echo "# Running ${suite}"
    echo "######################################################################"
    if "$SEKI" "$suite"; then
        total_passed=$((total_passed + 1))
    else
        total_failed=$((total_failed + 1))
        failed_list+=("$suite")
    fi
done

echo ""
echo "######################################################################"
echo "# OVERALL: ${total_passed}/${total_suites} suites passed"
echo "######################################################################"

if [ "$total_failed" -gt 0 ]; then
    echo ""
    echo "FAILED suites:" >&2
    for f in "${failed_list[@]}"; do
        echo "  - $f" >&2
    done
    exit 1
fi
exit 0
