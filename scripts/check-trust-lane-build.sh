#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Build the complete Trust compiler route against the committed measurement
# tuple. Run from an isolated checkout with clean sibling dependencies at their
# pins; this script never changes checkouts or dependency revisions.

set -euo pipefail

usage() {
    cat <<'EOF'
Usage: scripts/check-trust-lane-build.sh

Check tools/tuple.toml and the compiler API spellings, run the engine's
source lints (the constant-pointer rule, Rule A's field-type rule, the
no-tool-by-name rule, T3's sort-name rule, Rule E's fresh-value rule and the
guarded-callee-body rule, eleven
tests of `-p trust-mc-engine --lib`), then build
the driver, backend, front doors and keyed-library builder with
targo --unverified --locked.
This is a development build, with no Trust verification claim.

TRUST_MC_TRUST_TOOLCHAIN selects the exact installed numbered seal directory;
see scripts/resolve-trust-tool.sh --help. CARGO_BUILD_JOBS, when unset, is
sized to the host by scripts/host_room.py: the memory available now (less a
margin) over one rustc job's need, TRUST_MC_BUILD_JOB_NEED_MB (default 4608,
the measured peak of the trust-mc-engine rustc on seal 9192), and the cores
the load leaves free; a set CARGO_BUILD_JOBS is used as given, except the
share build-slot injects, which bounds the plan instead.
TRUST_MC_LANE_LINT_FEATURES=ay,compiler-corpus-tests (the only other value)
runs the lints with the engine suite's features, so a caller that also runs
the suite shares its test binary (the lints are source scans; their count
is still enforced).
The ../ay and ../trust-ir worktrees must be clean at the tuple's revisions.
EOF
}

case "${1:-}" in
    -h|--help) usage; exit 0 ;;
    "") ;;
    *) usage >&2; exit 2 ;;
esac
[[ $# -eq 0 ]] || { usage >&2; exit 2; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Keep the repository's build policy and the selected seal authoritative.
# No ambient flags or compiler wrappers should replace them.
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS CARGO_BUILD_RUSTFLAGS RUSTC RUSTC_WRAPPER \
    RUSTC_WORKSPACE_WRAPPER CARGO_BUILD_RUSTC CARGO_BUILD_RUSTC_WRAPPER \
    CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER RUSTUP_TOOLCHAIN CARGO_BUILD_TARGET

SYSROOT="$(scripts/resolve-trust-tool.sh sysroot)"
TARGO="$(scripts/resolve-trust-tool.sh targo)"
export PATH="$SYSROOT/bin:$PATH"
if [[ "${BUILD_SLOT_HELD:-}" == 1 && -z "${HOST_ROOM_SLOT_JOBS:-}" && -n "${CARGO_BUILD_JOBS:-}" ]]; then
    # Inside `build-slot -- ...` (AGENTS.md): its CARGO_BUILD_JOBS is a CPU
    # share, a ceiling for the plan below, not a job count to use as given.
    export HOST_ROOM_SLOT_JOBS="$CARGO_BUILD_JOBS"
    unset CARGO_BUILD_JOBS
fi
if [[ -z "${CARGO_BUILD_JOBS:-}" ]]; then
    # One rustc job's need is a property of the workspace (its largest crate),
    # not of the host; the job count is the host's, measured now.
    CARGO_BUILD_JOBS="$(python3 scripts/host_room.py plan --label check-trust-lane-build \
        --not-timing-sensitive --need-mb "${TRUST_MC_BUILD_JOB_NEED_MB:-4608}")" || {
        printf 'check-trust-lane-build: host room refused the build (see the line above)\n' >&2
        exit 2
    }
fi
export CARGO_BUILD_JOBS

tools/tuple-check
scripts/check-trust-lane-port.sh

# The engine's source lints: each names the file:line of a forbidden
# spelling (test_const_pointer_single_rule.rs, test_mono_ty_single_rule.rs,
# test_no_tool_by_name.rs, test_sort_name_single_rule.rs,
# test_fresh_var_single_rule.rs, callee_body.rs). Run these before the native
# build, without waiting for the full engine suite to find a source violation.
# A filter that matches nothing passes vacuously, so the run must count every
# lint test: a renamed or deleted lint fails here.
LINT_FILTERS=(
    codegen_ay::test_const_pointer_single_rule::
    codegen_ay::test_mono_ty_single_rule::
    codegen_ay::test_no_tool_by_name::
    codegen_ay::test_sort_name_single_rule::
    codegen_ay::test_fresh_var_single_rule::
    callee_body::tests::codegen_fetches_every_callee_body_through_the_guard
)
LINT_TESTS=11
printf 'check-trust-lane-build: engine source lints\n'
# Both spellings are literal, so every lane this script builds stays a command
# scripts/pinned_package_paths.py can read.
lint_status=0
case "${TRUST_MC_LANE_LINT_FEATURES:-}" in
    "")
        lint_out="$("$TARGO" --unverified test --locked --target-dir target -p trust-mc-engine --lib \
            -- "${LINT_FILTERS[@]}" 2>&1)" || lint_status=$?
        ;;
    ay,compiler-corpus-tests)
        lint_out="$("$TARGO" --unverified test --locked --target-dir target -p trust-mc-engine --lib \
            --features ay,compiler-corpus-tests -- "${LINT_FILTERS[@]}" 2>&1)" || lint_status=$?
        ;;
    *)
        printf 'check-trust-lane-build: TRUST_MC_LANE_LINT_FEATURES must be empty or ay,compiler-corpus-tests\n' >&2
        exit 2
        ;;
esac
if [[ "$lint_status" -ne 0 ]]; then
    printf '%s\n' "$lint_out" >&2
    printf 'check-trust-lane-build: engine source lints FAILED\n' >&2
    exit 1
fi
printf '%s\n' "$lint_out" | grep -E '^test ' || true
if ! printf '%s\n' "$lint_out" | grep -qE "^test result: ok\. $LINT_TESTS passed; 0 failed"; then
    printf 'check-trust-lane-build: expected exactly %s engine lint tests to pass\n' "$LINT_TESTS" >&2
    exit 1
fi

printf 'check-trust-lane-build: unverified development build on %s (jobs=%s)\n' \
    "$SYSROOT" "$CARGO_BUILD_JOBS"
"$TARGO" --unverified build --locked --target-dir target \
    -p trust-mc-driver -p trust-mc-backend -p trust-mc -p build-trust-mc
printf 'check-trust-lane-build: ok: driver, backend, front doors and keyed-library builder built\n'
