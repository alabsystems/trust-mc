#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0 OR MIT
#
# Soundness gate: runs the false-PROOF regression corpus from the soundness
# ledger one file at a time through ay-compiletest.sh.
#
# Fail-closed: if any ledgered file fails verification (unexpected verdict),
# the gate fails. The file list here is intentionally duplicated from
# tests/ay/soundness_ledger.toml — the cargo test
# `test_soundness_gate_script_covers_all_ledgered_files` enforces that this
# array matches the ledger exactly.
#
# Usage:
#   ./scripts/ay-soundness-gate.sh
#   AY_SOLVER=auto AY_TEST_TIMEOUT=60 ./scripts/ay-soundness-gate.sh
#
# Part of #3765. See also #3764 (ledger integrity).

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"
TRUST_MC_CARGO="$("${ROOT_DIR}/scripts/resolve-trust-tool.sh" cargo)"

# Soundness regression files — must match tests/ay/soundness_ledger.toml.
# The ledger test enforces this list matches the ledger exactly.
SOUNDNESS_FILES=(
    tests/ay/soundness_129_fail_expected.rs
    tests/ay/soundness_155_stale_ssa_fail.rs
    tests/ay/soundness_2055_intermediate_read_fail.rs
    tests/ay/memory_safety_uaf_fail.rs
    tests/ay/memory_safety_size_mismatch_fail.rs
    tests/ay/memory_safety_double_free_fail.rs
    tests/ay/realloc_stale_pointer_fail.rs
    tests/ay/offset_symbolic_count_byte_wrap_fail.rs
)

PASS=0
FAIL=0
ERRORS=()

echo "[soundness-gate] Root: ${ROOT_DIR}"
echo "[soundness-gate] Files: ${#SOUNDNESS_FILES[@]}"
AY_SOLVER="${AY_SOLVER:-auto}"
# 300, not 60: the per-harness budget must clear the slowest LEDGERED solve on
# the slowest host, or the watchdog kills the verifier before ANY verdict and
# this gate reports the kill as VACUOUS. Measured 2026-08-19 on the GB10
# (Grace, debug driver): offset_symbolic_count_byte_wrap_fail.rs completes in
# 120.7s with its expected genuine-CTREX verdict; at 60s it died verdict-less
# right at the boundary. 300s gives the same ~2.5x headroom the measured
# trust-vc BV cap uses. A genuinely hung solve still fails the gate — the
# verdict is required, not just an exit.
AY_TEST_TIMEOUT="${AY_TEST_TIMEOUT:-300}"
export AY_SOLVER AY_TEST_TIMEOUT

echo "[soundness-gate] AY_SOLVER=${AY_SOLVER}"
echo "[soundness-gate] AY_TEST_TIMEOUT=${AY_TEST_TIMEOUT}"

# PRECONDITION: the driver resolves its SMT backend with `which::which("ay")`
# (trust-mc-driver/src/args/solver.rs), so without `ay` on PATH every harness
# exits instantly with "AY solver not found in PATH". compiletest's
# `kani-verify-fail` accepts ANY nonzero exit as the expected failure, so the
# run reports "ok" in 0.01s and this gate then reports all N files VACUOUS —
# technically fail-closed, but indistinguishable from a real regression. Check
# it up front and say so, so a missing PATH is never mistaken for a soundness
# finding. `AY_BIN` does NOT satisfy this: it is read by the kani-domination
# harness, not by the driver's backend resolution.
if ! command -v ay >/dev/null 2>&1; then
    echo "[soundness-gate] ERROR: no \`ay\` on PATH — the driver would exit instantly on"
    echo "[soundness-gate]        every file and this gate would report VACUOUS for all of"
    echo "[soundness-gate]        them. Put the AY binary on PATH, e.g.:"
    echo "[soundness-gate]            PATH=\"\$PWD/../ay/target/release:\$PATH\" $0"
    exit 2
fi
echo "[soundness-gate] ay on PATH: $(command -v ay) ($(ay --version 2>/dev/null | head -1))"
echo ""

# Build the verifier ONCE; per-file runs then use --skip-build. The ledgered
# files live in tests/ay/, so each run is `ay-compiletest.sh <suite=ay>` with a
# --filter on the file name (ay-compiletest.sh takes a SUITE dir, not a file).
echo "[soundness-gate] building trust-mc (cargo build-dev) ..."
"${TRUST_MC_CARGO}" build-dev

for file in "${SOUNDNESS_FILES[@]}"; do
    if [[ ! -f "${file}" ]]; then
        echo "[soundness-gate] ERROR: missing file ${file}"
        FAIL=$((FAIL + 1))
        ERRORS+=("MISSING: ${file}")
        continue
    fi

    echo "[soundness-gate] START ${file}"

    # CHC-lane files declare `--ay-chc-track=...` in their kani-flags header;
    # that flag is rejected by the driver without `--ay-chc`, so they must run
    # under the CHC backend (ay-compiletest.sh --chc) or they never verify.
    declare -a extra_ct_flags=()
    if grep -q '^// kani-flags: .*--ay-chc-track' "${file}"; then
        extra_ct_flags+=( --chc )
    fi

    ct_status=0
    ./scripts/ay-compiletest.sh --skip-build --force-rerun \
        "${extra_ct_flags[@]+"${extra_ct_flags[@]}"}" \
        --filter "$(basename "${file}")" ay 2>&1 || ct_status=$?

    # Ledger semantics, enforced on the captured per-test output (compiletest's
    # `kani-verify-fail` alone accepts ANY nonzero verifier exit — including an
    # instant crash or a bad install — as the expected failure, which is how
    # this gate historically passed vacuously):
    #   1. A `VERIFICATION:- SUCCESSFUL` is a FALSE PROOF -> hard fail.
    #   2. Some `VERIFICATION:-` verdict must exist -> else nothing verified.
    #   3. The declared `// kani-expect:` marker (or an explicitly accepted
    #      `// soundness-accepted-verdict: UNKNOWN` fail-closed INCONCLUSIVE)
    #      must be present.
    outdir="build/tests/ay/$(basename "${file}" .rs)"
    expect_token="$(sed -n 's|^// kani-expect: ||p' "${file}" | head -1)"
    accepts_unknown=0
    grep -q '^// soundness-accepted-verdict: UNKNOWN' "${file}" && accepts_unknown=1

    verdict_fail=""
    if grep -rqF -- 'VERIFICATION:- SUCCESSFUL' "${outdir}" 2>/dev/null; then
        verdict_fail="FALSE-PROOF: VERIFICATION:- SUCCESSFUL on a ledgered fail-expected file"
    elif ! grep -rqF -- 'VERIFICATION:-' "${outdir}" 2>/dev/null; then
        verdict_fail="VACUOUS: no VERIFICATION verdict in ${outdir} (verifier never ran)"
    else
        case "${expect_token}" in
            CTREX) marker='[AY:CTREX_CAT:' ;;
            ERROR) marker='ERROR' ;;
            '') marker='' ;;
            *) marker="${expect_token}" ;;
        esac
        if [[ -n "${marker}" ]] && ! grep -rqF -- "${marker}" "${outdir}" 2>/dev/null; then
            if [[ "${accepts_unknown}" -eq 1 ]] \
                && grep -rqF -- 'VERIFICATION:- INCONCLUSIVE' "${outdir}" 2>/dev/null; then
                : # fail-closed UNKNOWN explicitly accepted by the ledger entry
            else
                verdict_fail="EXPECT-MISS: marker '${marker}' absent from ${outdir}"
            fi
        fi
    fi

    if [[ "${ct_status}" -ne 0 ]]; then
        echo "[soundness-gate] FAIL  ${file} (compiletest exit ${ct_status})"
        FAIL=$((FAIL + 1))
        ERRORS+=("FAIL: ${file}")
    elif [[ -n "${verdict_fail}" ]]; then
        echo "[soundness-gate] FAIL  ${file} (${verdict_fail})"
        FAIL=$((FAIL + 1))
        ERRORS+=("${verdict_fail%%:*}: ${file}")
    else
        echo "[soundness-gate] PASS  ${file}"
        PASS=$((PASS + 1))
    fi
    echo ""
done

echo "[soundness-gate] ========================="
echo "[soundness-gate] Results: ${PASS} passed, ${FAIL} failed out of ${#SOUNDNESS_FILES[@]}"

if [[ ${FAIL} -gt 0 ]]; then
    echo "[soundness-gate] FAILURES:"
    for err in "${ERRORS[@]}"; do
        echo "  - ${err}"
    done
    echo "[soundness-gate] GATE FAILED"
    exit 1
fi

echo "[soundness-gate] GATE PASSED"
exit 0
