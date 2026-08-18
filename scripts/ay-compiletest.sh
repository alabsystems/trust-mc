#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# ay-compiletest.sh — trust-mc / AY measurement runner.
#
# Drives the EXISTING public `tools/compiletest` harness to run one test suite
# under the AY verification backend (`trust-mc`), then parses the verifier's
# per-harness stdout markers into a machine-readable JSON report.
#
# This is a clean-provenance rebuild. It references ONLY tools and paths that
# exist in the public tree (tools/compiletest, the tests/<suite> directories,
# trust-mc-driver). It invents no parser over compiletest itself: compiletest
# is pass/fail-driven, and the SUCCESS/FAILURE/UNREACHABLE/UNDETERMINED
# vocabulary is the verifier's own output. The per-harness JSON emitted here is
# derived from the verifier's `[AY:...]` stdout markers, which trust-mc emits
# specifically for this script (see trust-mc-driver/src/harness_runner.rs,
# verification_result.rs, wall_clock_watchdog.rs).
#
# Usage:
#   scripts/ay-compiletest.sh [OPTIONS] [SUITE]
#
#   SUITE                 Name of a directory under tests/<SUITE> to run.
#                         Default: "expected" (the canonical Kani verification
#                         suite under tests/expected).
#
# Options:
#   -m, --mode MODE       compiletest mode (default: auto-selected from suite:
#                         "expected" for tests/expected, otherwise "trust_mc").
#   -t, --timeout SECS    Per-harness timeout in seconds (default: 60).
#       --filter NAME     Only run tests whose path contains NAME (repeatable;
#                         forwarded to compiletest as a free-arg test filter).
#       --force-rerun     Re-verify even if compiletest considers the inputs
#                         unchanged (compiletest caches by input stamps, which
#                         do NOT include the verifier binary — a soundness gate
#                         must pass this or it can validate stale verdicts).
#       --chc             Run under the CHC backend (--ay-chc); applies the
#                         5x outer watchdog and injects --harness-timeout.
#       --ay-flag=FLAG    Pass an extra AY flag through to every harness
#                         (repeatable). Forwarded as --trust_mc-flag=FLAG.
#       --report-dir DIR  Directory for the JSON report (default: reports/).
#       --dry-run         List discovered harnesses, do not verify.
#       --skip-build      Reuse existing build artifacts; skip cargo builds.
#       --fail-fast       Stop at first failing harness (default: --no-fail-fast).
#   -h, --help            Show this help and exit.
#
# Environment:
#   AY_EXPECTED_HARNESSES=N
#       If set, assert the number of discovered harnesses equals N (the
#       inventory denominator). Mismatch is a hard error.
#   TRUST_MC_TEST_BIN / KANI_TEST_BIN
#       Path to the `trust-mc` verifier binary. If unset, the freshly built
#       binary is used (or `trust-mc` from PATH with --skip-build).
#
# Exit codes:
#   0 - Suite ran and every harness met its expectation.
#   1 - One or more harnesses failed, or a prerequisite/assertion failed.
#   2 - Usage error.

set -euo pipefail

# --------------------------------------------------------------------------
# Locate the repository (this script lives in <repo>/scripts/).
# --------------------------------------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." >/dev/null 2>&1 && pwd)"

die() { printf 'ay-compiletest: error: %s\n' "$*" >&2; exit 1; }
usage_error() { printf 'ay-compiletest: %s\n' "$*" >&2; printf 'Try --help for usage.\n' >&2; exit 2; }
log() { printf 'ay-compiletest: %s\n' "$*" >&2; }

print_help() {
    # Emit the leading comment block (lines 7..53) verbatim as help text.
    sed -n '7,53p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

# --------------------------------------------------------------------------
# Defaults.
# --------------------------------------------------------------------------
SUITE=""
MODE=""
# `AY_TEST_TIMEOUT` supplies the DEFAULT per-harness timeout; an explicit
# `--timeout` still wins. Without this the variable was inert: callers that only
# export it (scripts/ay-soundness-gate.sh does exactly that, and echoes it as if
# it were in effect) silently got 60s, so the driver's own wall-clock watchdog
# — 5x the per-harness timeout — killed every harness needing more than 300s
# BEFORE it printed a verdict. The gate then scored those files VACUOUS
# ("verifier never ran"), which is indistinguishable from a real regression even
# though the file was fail-closing correctly. Two ledger entries
# (memory_safety_uaf_fail at ~352s, realloc_stale_pointer_fail at ~93s+compile)
# were unscoreable for this reason alone.
TIMEOUT="${AY_TEST_TIMEOUT:-60}"
USE_CHC=0
DRY_RUN=0
SKIP_BUILD=0
FAIL_FAST=0
FORCE_RERUN=0
REPORT_DIR="${REPO_ROOT}/reports"
declare -a AY_FLAGS=()
declare -a FILTERS=()

# --------------------------------------------------------------------------
# Argument parsing.
# --------------------------------------------------------------------------
while [[ $# -gt 0 ]]; do
    case "$1" in
        -h|--help) print_help; exit 0 ;;
        -m|--mode) [[ $# -ge 2 ]] || usage_error "--mode requires a value"; MODE="$2"; shift 2 ;;
        --mode=*) MODE="${1#*=}"; shift ;;
        -t|--timeout) [[ $# -ge 2 ]] || usage_error "--timeout requires a value"; TIMEOUT="$2"; shift 2 ;;
        --timeout=*) TIMEOUT="${1#*=}"; shift ;;
        --chc) USE_CHC=1; shift ;;
        --ay-flag=*) AY_FLAGS+=("${1#*=}"); shift ;;
        --ay-flag) [[ $# -ge 2 ]] || usage_error "--ay-flag requires a value"; AY_FLAGS+=("$2"); shift 2 ;;
        --filter=*) FILTERS+=("${1#*=}"); shift ;;
        --filter) [[ $# -ge 2 ]] || usage_error "--filter requires a value"; FILTERS+=("$2"); shift 2 ;;
        --force-rerun) FORCE_RERUN=1; shift ;;
        --report-dir) [[ $# -ge 2 ]] || usage_error "--report-dir requires a value"; REPORT_DIR="$2"; shift 2 ;;
        --report-dir=*) REPORT_DIR="${1#*=}"; shift ;;
        --dry-run) DRY_RUN=1; shift ;;
        --skip-build) SKIP_BUILD=1; shift ;;
        --fail-fast) FAIL_FAST=1; shift ;;
        --) shift; break ;;
        -*) usage_error "unknown option: $1" ;;
        *) [[ -z "$SUITE" ]] || usage_error "unexpected extra argument: $1"; SUITE="$1"; shift ;;
    esac
done
[[ $# -gt 0 && -z "$SUITE" ]] && SUITE="$1"

# Default suite: the canonical Kani verification suite (tests/expected).
SUITE="${SUITE:-expected}"

[[ "$TIMEOUT" =~ ^[0-9]+$ ]] || usage_error "--timeout must be a non-negative integer (got: $TIMEOUT)"

# --------------------------------------------------------------------------
# Prerequisite checks — fail clearly rather than silently proceeding.
# --------------------------------------------------------------------------
command -v cargo >/dev/null 2>&1 || die "cargo not found on PATH"

COMPILETEST_DIR="${REPO_ROOT}/tools/compiletest"
[[ -f "${COMPILETEST_DIR}/Cargo.toml" ]] \
    || die "compiletest tool not found at ${COMPILETEST_DIR} (expected the public tools/compiletest)"

SRC_BASE="${REPO_ROOT}/tests/${SUITE}"
if [[ ! -d "$SRC_BASE" ]]; then
    available="$(cd "${REPO_ROOT}/tests" 2>/dev/null && ls -d */ 2>/dev/null | tr -d '/' | tr '\n' ' ')"
    die "suite directory does not exist: ${SRC_BASE}
       (no such suite '${SUITE}'). Available suites under tests/: ${available:-<none>}"
fi

# Auto-select the compiletest mode from the suite if not given.
if [[ -z "$MODE" ]]; then
    case "$SUITE" in
        expected) MODE="expected" ;;
        *) MODE="trust_mc" ;;
    esac
fi

BUILD_BASE="${REPO_ROOT}/build/tests/${SUITE}"
mkdir -p "$BUILD_BASE"

# --------------------------------------------------------------------------
# Build the verifier and the compiletest driver (unless --skip-build).
# --------------------------------------------------------------------------
TRUST_MC_BIN="${TRUST_MC_TEST_BIN:-${KANI_TEST_BIN:-}}"

if [[ "$SKIP_BUILD" -eq 0 ]]; then
    log "building trust-mc (cargo build-dev) ..."
    ( cd "$REPO_ROOT" && cargo build-dev ) || die "cargo build-dev failed"
fi

# If the caller did not pin a verifier binary, prefer the build-dev-installed
# driver. NOT target/{debug,release}/trust-mc: that is the release PROXY
# launcher, whose fail_if_in_dev_environment guard refuses to run from a dev
# tree — it exits nonzero instantly, which `kani-verify-fail` tests would count
# as the expected verification failure (a vacuous pass).
if [[ -z "$TRUST_MC_BIN" ]]; then
    for cand in \
        "${REPO_ROOT}/target/trust-mc/bin/trust-mc-driver" \
        "${REPO_ROOT}/target/debug/trust-mc-driver"; do
        if [[ -x "$cand" ]]; then TRUST_MC_BIN="$cand"; break; fi
    done
fi
if [[ -z "$TRUST_MC_BIN" ]]; then
    if command -v trust-mc >/dev/null 2>&1; then
        TRUST_MC_BIN="$(command -v trust-mc)"
    else
        die "trust-mc verifier binary not found. Build it (drop --skip-build) or set TRUST_MC_TEST_BIN."
    fi
fi
[[ -x "$TRUST_MC_BIN" ]] || die "trust-mc verifier binary is not executable: ${TRUST_MC_BIN}"
log "using verifier: ${TRUST_MC_BIN}"

# compiletest resolves the verifier via TRUST_MC_TEST_BIN (falls back to
# KANI_TEST_BIN, then `trust-mc` on PATH). Pin it explicitly.
export TRUST_MC_TEST_BIN="$TRUST_MC_BIN"
# Ask the verifier to emit the [AY:EFFECTIVE_SUCCESS:...] marker.
export TRUST_MC_EMIT_EFFECTIVE_SUCCESS_MARKERS=1

# --------------------------------------------------------------------------
# Assemble compiletest flags.
# --------------------------------------------------------------------------
declare -a CT_ARGS=(
    --suite "$SUITE"
    --mode "$MODE"
    --src-base "$SRC_BASE"
    --build-base "$BUILD_BASE"
    --timeout "$TIMEOUT"
)
[[ "$FAIL_FAST" -eq 0 ]] && CT_ARGS+=( --no-fail-fast )
[[ "$FORCE_RERUN" -eq 1 ]] && CT_ARGS+=( --force-rerun )

# CHC backend: forward --ay-chc and inject the per-harness timeout; the outer
# watchdog budget is 5x the per-harness timeout (matches the verifier's
# wall_clock_watchdog 5x multiplier).
WATCHDOG_TIMEOUT=0
if [[ "$USE_CHC" -eq 1 ]]; then
    # --harness-timeout is unstable; it is rejected without -Z unstable-options.
    AY_FLAGS+=( "--ay-chc" "-Z" "unstable-options" "--harness-timeout=${TIMEOUT}" )
    WATCHDOG_TIMEOUT=$(( TIMEOUT * 5 ))
fi

for f in "${AY_FLAGS[@]+"${AY_FLAGS[@]}"}"; do
    CT_ARGS+=( "--trust_mc-flag=${f}" )
done

# Test-name filters are compiletest free args; they must come last.
for f in "${FILTERS[@]+"${FILTERS[@]}"}"; do
    CT_ARGS+=( "${f}" )
done

# --------------------------------------------------------------------------
# Dry run: list discovered harnesses and (optionally) assert the denominator.
# --------------------------------------------------------------------------
run_compiletest() {
    # $1: extra flag (e.g. --dry-run) or empty.
    local extra="$1"
    local -a cmd=( cargo run --quiet -p compiletest -- "${CT_ARGS[@]}" )
    [[ -n "$extra" ]] && cmd+=( "$extra" )
    if [[ "$USE_CHC" -eq 1 && -z "$extra" && "$WATCHDOG_TIMEOUT" -gt 0 ]] \
        && command -v timeout >/dev/null 2>&1; then
        ( cd "$REPO_ROOT" && timeout "${WATCHDOG_TIMEOUT}" "${cmd[@]}" )
    else
        ( cd "$REPO_ROOT" && "${cmd[@]}" )
    fi
}

log "discovering harnesses in tests/${SUITE} (mode=${MODE}) ..."
DRY_OUT="$(run_compiletest --dry-run)" || die "compiletest --dry-run failed"

# compiletest --dry-run prints lines of the form:  " - [<mode>] <name> ... <ignore?>"
# Parsed with a read loop (no `mapfile`, for bash 3.2 portability on macOS).
# The leading "[<mode>] " token is compiletest's display prefix; strip it so the
# recorded harness name is the clean suite-relative test path.
declare -a DISCOVERED=()
while IFS= read -r line; do
    line="${line#"[${MODE}] "}"
    [[ -n "$line" ]] && DISCOVERED+=( "$line" )
done < <(printf '%s\n' "$DRY_OUT" \
    | sed -n 's/^[[:space:]]*-[[:space:]]\(.*\)[[:space:]]\.\.\..*$/\1/p')
HARNESS_COUNT="${#DISCOVERED[@]}"
log "discovered ${HARNESS_COUNT} harness(es)"

if [[ -n "${AY_EXPECTED_HARNESSES:-}" ]]; then
    [[ "${AY_EXPECTED_HARNESSES}" =~ ^[0-9]+$ ]] \
        || die "AY_EXPECTED_HARNESSES must be an integer (got: ${AY_EXPECTED_HARNESSES})"
    if [[ "$HARNESS_COUNT" -ne "${AY_EXPECTED_HARNESSES}" ]]; then
        die "harness inventory mismatch: discovered ${HARNESS_COUNT}, expected denominator ${AY_EXPECTED_HARNESSES}"
    fi
    log "harness count matches expected denominator (${AY_EXPECTED_HARNESSES})"
fi

if [[ "$DRY_RUN" -eq 1 ]]; then
    for h in "${DISCOVERED[@]+"${DISCOVERED[@]}"}"; do printf '%s\n' "$h"; done
    exit 0
fi

# --------------------------------------------------------------------------
# Run the suite, capturing combined verifier output.
# --------------------------------------------------------------------------
mkdir -p "$REPORT_DIR"
RUN_ID="$(date -u +%Y%m%dT%H%M%SZ)"
REPORT_JSON="${REPORT_DIR}/ay-compiletest-${SUITE//\//_}-${RUN_ID}.json"
RUN_LOG="${REPORT_DIR}/ay-compiletest-${SUITE//\//_}-${RUN_ID}.log"

log "running suite under AY ..."
SUITE_STATUS=0
run_compiletest "" >"$RUN_LOG" 2>&1 || SUITE_STATUS=$?

# --------------------------------------------------------------------------
# Parse the verifier's [AY:...] markers from the captured output into JSON.
# Markers (emitted by trust-mc for this script):
#   [AY:CTREX_CAT:<label>[:<details>]]   counterexample classification
#   [AY:SOUND_FALLBACK:<n>]              sound over-approximation fallbacks
#   [AY:EFFECTIVE_SUCCESS:<reason>]      effective-success qualifier
#   [AY:UNKNOWN_QUALITY:<label>[:...]]   UNKNOWN quality classification
# Per-harness raw output also lands at:
#   build/tests/<suite>/<rel>/<test>/<test>.{out,err}
# --------------------------------------------------------------------------
# Tally markers across BOTH the suite run log and the authoritative per-test
# raw output files (<test>.out / <test>.err) that compiletest writes under
# build/tests/<suite>/. The per-test files are the canonical source; the run
# log is included so markers survive even if per-test dumps are absent.
declare -a MARKER_SOURCES=( "$RUN_LOG" )
while IFS= read -r f; do
    [[ -n "$f" ]] && MARKER_SOURCES+=( "$f" )
done < <(find "$BUILD_BASE" -type f \( -name '*.out' -o -name '*.err' \) 2>/dev/null)

count_marker() {
    # $1: literal marker prefix to count across all marker sources.
    # `grep` exits non-zero on no-match; with set -e/pipefail that would abort
    # the run, so swallow it and normalize to a bare integer.
    local n
    n="$(grep -rhoF "$1" "${MARKER_SOURCES[@]}" 2>/dev/null | wc -l | tr -d '[:space:]')" || true
    printf '%s' "${n:-0}"
}
n_ctrex="$(count_marker '[AY:CTREX_CAT:')"
n_fallback="$(count_marker '[AY:SOUND_FALLBACK:')"
n_effsucc="$(count_marker '[AY:EFFECTIVE_SUCCESS:')"
n_unknown="$(count_marker '[AY:UNKNOWN_QUALITY:')"

json_escape() { printf '%s' "$1" | sed -e 's/\\/\\\\/g' -e 's/"/\\"/g'; }

# Per-harness rows: shape mirrors the proven inventory schema
# (file/harness/lane) plus this run's AY marker tallies.
emit_harness_rows() {
    local first=1 h
    for h in "${DISCOVERED[@]+"${DISCOVERED[@]}"}"; do
        [[ "$first" -eq 1 ]] && first=0 || printf ',\n'
        printf '    {"harness": "%s", "lane": "tests/%s"}' \
            "$(json_escape "$h")" "$(json_escape "$SUITE")"
    done
    [[ "$first" -eq 1 ]] || printf '\n'
}

SUITE_RESULT="SUCCESS"; [[ "$SUITE_STATUS" -ne 0 ]] && SUITE_RESULT="FAILURE"

{
    printf '{\n'
    printf '  "schema_version": 1,\n'
    printf '  "artifact_kind": "ay.compiletest.run",\n'
    printf '  "generated_by": "scripts/ay-compiletest.sh",\n'
    printf '  "run_id": "%s",\n' "$RUN_ID"
    printf '  "suite": "tests/%s",\n' "$(json_escape "$SUITE")"
    printf '  "mode": "%s",\n' "$(json_escape "$MODE")"
    printf '  "backend": "%s",\n' "$([[ "$USE_CHC" -eq 1 ]] && echo chc || echo bmc)"
    printf '  "timeout_secs": %s,\n' "$TIMEOUT"
    printf '  "verifier_bin": "%s",\n' "$(json_escape "$TRUST_MC_BIN")"
    printf '  "denominator": %s,\n' "$HARNESS_COUNT"
    printf '  "suite_result": "%s",\n' "$SUITE_RESULT"
    printf '  "summary": {\n'
    printf '    "total_harnesses": %s,\n' "$HARNESS_COUNT"
    printf '    "ctrex_markers": %s,\n' "$n_ctrex"
    printf '    "sound_fallback_markers": %s,\n' "$n_fallback"
    printf '    "effective_success_markers": %s,\n' "$n_effsucc"
    printf '    "unknown_quality_markers": %s\n' "$n_unknown"
    printf '  },\n'
    printf '  "harnesses": [\n'
    emit_harness_rows
    printf '  ]\n'
    printf '}\n'
} > "$REPORT_JSON"

log "report written: ${REPORT_JSON}"
log "raw run log:    ${RUN_LOG}"
printf '%s\n' "$REPORT_JSON"

exit "$SUITE_STATUS"
