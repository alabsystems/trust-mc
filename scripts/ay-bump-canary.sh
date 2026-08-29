#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Pre-bump canary for AY dependency updates.
# Part of #3571: catch ay-chc public API drift (ay#3604) before trusting a new pin.

set -euo pipefail

usage() {
    cat <<'EOF'
Usage: ./scripts/ay-bump-canary.sh [--compile-only]

Runs the pre-bump AY checklist:
  1. cargo check -p trust-mc-driver --all-targets --features "ay,ay-chc-native"
  2. cargo check --all-targets
  3. cargo build-dev
  4. Tier 2 DT+BV / TIC compiletest canaries
  5. Tier 3 Spacer loop compiletest canaries
  6. Tier 4 False-proof detection canaries

Options:
  --compile-only  Run only the cargo compile gates (steps 1-3).
  -h, --help      Show this help text.
EOF
}

MODE="full"
case "${1:-}" in
    "")
        ;;
    --compile-only)
        MODE="compile-only"
        ;;
    -h|--help)
        usage
        exit 0
        ;;
    *)
        usage >&2
        exit 2
        ;;
esac

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
source "$SCRIPT_DIR/ay_python.sh"
TRUST_MC_DIR="$(cd "$SCRIPT_DIR/.." >/dev/null 2>&1 && pwd)"
cd "$TRUST_MC_DIR"
TRUST_MC_CARGO="$("$SCRIPT_DIR/resolve-trust-tool.sh" cargo)"

AY_SOLVER="${AY_SOLVER:-auto}"
AY_TEST_TIMEOUT="${AY_TEST_TIMEOUT:-30}"
NATIVE_FEATURES="ay,ay-chc-native"

TIER2_FILES=(
    tests/ay/debug_array_option.rs
    tests/ay/memory_store_load.rs
    tests/ay/multi_struct_debug.rs
    tests/ay/tier2_unbounded.rs
    tests/ay/tier2_loop_for.rs
    tests/ay/test_vec_iter_soundness.rs
    tests/ay/ay_self_verify_bv_bitblast.rs
    tests/ay/btreemap_store_dual_select.rs
)

TIER3_FILES=(
    tests/ay/tier2_loop_while.rs
    tests/ay/tier2_loop_loop.rs
    tests/ay/factorial.rs
    tests/ay/test_enumerate_loop.rs
)

# Tier 4: false-proof detection canaries.
# Expected-CTREX harnesses that are AY-version-sensitive.
# A CTREX→PROOF flip is a false proof regression and blocks the bump.
# AY is the sole solver (Z3 eliminated, #4222).
TIER4_FILES=(
    tests/trust-mc/Panic/prove_safety_only.rs
    tests/ay/realloc_stale_pointer_fail.rs
    tests/ay/ay_self_verify_conflict_analysis.rs
)

extract_ay_pin() {
    "${AY_PYTHON_BIN:-python3}" "$TRUST_MC_DIR/scripts/ay_manifest_pin.py" --locked "$TRUST_MC_DIR"
}

run_compile_gate() {
    local description="$1"
    shift
    echo ""
    echo "=== $description ==="
    "$@"
}

run_compiletest_file() {
    local file="$1"
    local file_timeout="$AY_TEST_TIMEOUT"
    local relative suite filter

    # ay-compiletest takes a suite directory relative to tests/, plus optional
    # test-name filters. Passing the source path as its positional argument
    # instead makes it look for tests/tests/... and the bump gate never reaches
    # a verifier. Derive both pieces explicitly and reject malformed inventory
    # entries rather than silently widening the selected suite.
    relative="${file#tests/}"
    if [[ "$relative" == "$file" || "$relative" != */*.rs ]]; then
        echo "ERROR: canary path must name a Rust file below tests/: $file" >&2
        return 2
    fi
    suite="${relative%/*}"
    filter="${relative##*/}"
    if [[ ! -f "$TRUST_MC_DIR/$file" || ! -d "$TRUST_MC_DIR/tests/$suite" ]]; then
        echo "ERROR: canary source or suite is missing: $file (suite $suite)" >&2
        return 2
    fi

    case "$file" in
        tests/ay/test_vec_iter_soundness.rs)
            if [[ "$file_timeout" -lt 120 ]]; then
                file_timeout=120
            fi
            ;;
        tests/ay/ay_self_verify_bv_bitblast.rs)
            if [[ "$file_timeout" -lt 90 ]]; then
                file_timeout=90
            fi
            ;;
    esac

    echo ""
    echo "=== Canary: $file ==="
    if [[ "$file_timeout" != "$AY_TEST_TIMEOUT" ]]; then
        echo "Timeout override: ${file_timeout}s"
    fi
    # cargo build-dev above produced the exact driver once. Reuse it, force the
    # selected harness to execute even if compiletest has an old input stamp,
    # and bind the run to this file's basename within its exact suite.
    AY_SOLVER="$AY_SOLVER" AY_TEST_TIMEOUT="$file_timeout" \
        AY_EXPECTED_HARNESSES=1 \
        ./scripts/ay-compiletest.sh --skip-build --force-rerun \
        --filter "$filter" "$suite"
}

echo "=== AY Bump Canary (#3571) ==="
echo "trust-mc commit: $(git rev-parse --short HEAD 2>/dev/null || echo 'unknown')"
AY_PIN="$(extract_ay_pin)"
echo "AY pin: ${AY_PIN:0:8}"
echo "Solver: $AY_SOLVER"
echo "Timeout: ${AY_TEST_TIMEOUT}s"
echo "Mode: $MODE"
echo "Cargo wrapper cache: disabled for bump gates (CARGO_SKIP_CACHE=1)"
echo ""
echo "Native CHC compile gate: cargo check -p trust-mc-driver --all-targets --features \"$NATIVE_FEATURES\""

export CARGO_SKIP_CACHE=1

run_compile_gate \
    "Compile gate 1/3: ay-chc-native consumer check" \
    "$TRUST_MC_CARGO" check -p trust-mc-driver --all-targets --features "$NATIVE_FEATURES"

run_compile_gate \
    "Compile gate 2/3: workspace cargo check" \
    "$TRUST_MC_CARGO" check --all-targets

echo ""
echo "Fresh sysroot build: compiletest only checks whether target/trust-mc/lib/libstd.rlib exists."
echo "Run cargo build-dev here so stale artifacts cannot mask a broken clean rebuild."
run_compile_gate \
    "Compile gate 3/3: fresh sysroot build" \
    "$TRUST_MC_CARGO" build-dev

if [[ "$MODE" == "compile-only" ]]; then
    echo ""
    echo "PASS: compile-only AY bump canary complete"
    exit 0
fi

echo ""
echo "=== Tier 2 DT+BV / TIC canaries ==="
for file in "${TIER2_FILES[@]}"; do
    run_compiletest_file "$file"
done

echo ""
echo "=== Tier 3 Spacer loop canaries ==="
for file in "${TIER3_FILES[@]}"; do
    run_compiletest_file "$file"
done

echo ""
echo "=== Tier 4 False-proof detection canaries ==="
echo "Expected-CTREX harnesses: a CTREX->PROOF flip is a false proof regression."
for file in "${TIER4_FILES[@]}"; do
    run_compiletest_file "$file"
done

echo ""
echo "PASS: AY bump canary complete"
