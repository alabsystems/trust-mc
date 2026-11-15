#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# The advisory Trust verification lane: the crates that check with ZERO failed
# rows in `targo trust check --allow-l0-gaps`, each group held to a committed
# proved-row floor. This is ADDITIVE to scripts/check-trust-verification.sh
# (the strict, certified, whole-workspace gate) and replaces nothing: that gate
# and publish/config.sh keep their scope.

set -euo pipefail

usage() {
    cat <<'EOF'
Usage: scripts/check-trust-advisory-lane.sh [--list]

Run `targo trust check --allow-l0-gaps --locked` over each lane group below and
hold its report to the group's floor (scripts/advisory_lane_floor.py): no
failed row, at least one row, and at least FLOOR proved rows. Unknown,
runtime-checked and assumed rows never count toward a floor.

This is NOT a proof claim. The advisory lane admits L0 gaps by construction;
the strict gate is scripts/check-trust-verification.sh. A group is added here
only after it measured 0 failed; a floor is 80% of its lowest measured
proved count, so a lane that loses proofs fails instead of drifting silently.

--list prints the groups and exits. CARGO_BUILD_JOBS (default 4) sets -j.
Caller TRUSTFLAGS, rustflags and compiler overrides are refused.
EOF
}

die() { printf 'check-trust-advisory-lane: %s\n' "$*" >&2; exit 2; }

# group label | target selector | proved floor | packages
# (each group's build is also spelled literally in group_build below, so the
# pinned-package lint reads it; scripts/pin-exclusions.toml declares the three)
# Measured 2026-10-02 on targo 1.99.0-dev (321aaeda7), trust-mc 0f58cea9c plus
# the commits that closed each crate (their messages carry before/after counts).
# Two runs each, proved / failed / unknown / total:
#   libs  trust-mc-trust-vc-ingest          24/0/291/321  and  37/0/285/325
#   bins  trust-mc-replay + compile-timer   30/0/220/292* and  24/0/226/292
#   (* the two bins measured in separate invocations: 1/0/23/29 + 29/0/197/263)
#   cov   trust-mc-cov                      59/0/303/385  and  58/0/304/385
#   (trust-mc-cov measured on trust-mc ed02e05c7 plus the commit that closed it)
# The 3000 ms per-function budget makes rows of untouched functions flip between
# proved and timeout under host load (a timeout is unknown, never proved), so a
# floor is 80% of the LOWEST measured proved count.
LANE_GROUPS=(
    "libs|--lib|19|trust-mc-trust-vc-ingest"
    "bins|--bins|19|trust-mc-replay compile-timer"
    "cov|--bins|46|trust-mc-cov"
)

case "${1:-}" in
    -h|--help) usage; exit 0 ;;
    --list) printf '%s\n' "${LANE_GROUPS[@]}"; exit 0 ;;
    "") ;;
    *) die "unsupported argument '$1'; see --help" ;;
esac

for name in TRUSTFLAGS CARGO_ENCODED_TRUSTFLAGS RUSTFLAGS CARGO_ENCODED_RUSTFLAGS \
    RUSTDOCFLAGS CARGO_ENCODED_RUSTDOCFLAGS CARGO_BUILD_RUSTFLAGS \
    RUSTC CARGO_BUILD_RUSTC RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER \
    CARGO_BUILD_RUSTC_WRAPPER CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER RUSTUP_TOOLCHAIN; do
    [[ -z "${!name+x}" ]] || die "$name is set; unset it before running this lane"
done
jobs="${CARGO_BUILD_JOBS:-4}"
[[ "$jobs" =~ ^[1-9][0-9]*$ ]] || die "CARGO_BUILD_JOBS must be a positive integer"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
TARGO="$(scripts/resolve-trust-tool.sh targo)"
# shellcheck source=scripts/lib/python-with-toml.sh
. scripts/lib/python-with-toml.sh

umask 077
mkdir -p target/trust-advisory
run_dir="$(mktemp -d "$ROOT/target/trust-advisory/run.XXXXXX")"
printf 'check-trust-advisory-lane: reports %s (diagnostics only)\n' "$run_dir"

status=0
for group in "${LANE_GROUPS[@]}"; do
    IFS='|' read -r label selector floor packages <<<"$group"
    case "$label" in
        libs) group_build=(--lib -p trust-mc-trust-vc-ingest) ;;
        bins) group_build=(--bins -p trust-mc-replay -p compile-timer) ;;
        cov) group_build=(--bins -p trust-mc-cov) ;;
        *) die "group '$label' has no literal build" ;;
    esac
    spelled=("$selector")
    for package in $packages; do spelled+=(-p "$package"); done
    [[ "${spelled[*]}" == "${group_build[*]}" ]] \
        || die "group '$label': LANE_GROUPS says '${spelled[*]}', group_build '${group_build[*]}'"
    report_dir="$run_dir/$label"
    mkdir -p "$report_dir"
    printf 'check-trust-advisory-lane: %s (%s, floor %s):%s\n' \
        "$label" "$selector" "$floor" "$(printf ' %s' $packages)"
    set +e
    "$TARGO" trust check --allow-l0-gaps --locked -j "$jobs" "${group_build[@]}" \
        --report-dir "$report_dir" >"$report_dir/live.log" 2>&1
    targo_status=$?
    set -e
    grep -E '^\s*Gate:' "$report_dir/live.log" | tail -n 1 || true
    if [[ $targo_status -ne 0 ]]; then
        printf 'check-trust-advisory-lane: %s: targo exited %s; log %s\n' \
            "$label" "$targo_status" "$report_dir/live.log" >&2
        status=1
        continue
    fi
    "$PYTHON" scripts/advisory_lane_floor.py "$report_dir/report.json" \
        --floor "$floor" --label "$label" || status=1
done

if [[ $status -ne 0 ]]; then
    printf 'check-trust-advisory-lane: FAILED; diagnostics: %s\n' "$run_dir" >&2
    exit "$status"
fi
printf 'check-trust-advisory-lane: every group held its floor (advisory; not a proof claim)\n'
