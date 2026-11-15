#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Run the live, authenticated Trust verification gate. Saved reports preserve
# diagnostics only: deserializing them does not restore verifier authority.

set -euo pipefail

usage() {
    cat <<'EOF'
Usage: scripts/check-trust-verification.sh [--check|--build] [--tuple FILE] [-p PACKAGE ...]

Default: certify-check the entire workspace and its dependencies, including
the engine and backend. --check and --build select their respective Trust
frontends; the check frontend may also build artifacts for verification.
Scope is default features/targets; test-only code and optional targets are
not included. This does not build the separate keyed Kani sysroot.
Dependency/host scope covers compiler units, not build-script execution itself.
Repeated -p/--package selects an explicitly labelled diagnostic subset.

Select the exact Trust seal with TRUST_MC_TRUST_TOOLCHAIN. The committed
dependency tuple is the default; --tuple FILE explicitly selects an alternate
tuple, including a schema-2 development identity. Every tuple check and the
compiler API spelling checks must pass first. The selected tuple's identity
scope is retained in tuple.json; it grants no compiler verification authority.
CARGO_BUILD_JOBS defaults to 2 and may be reduced to 1.

Caller TRUSTFLAGS, encoded verification flags, compiler overrides and rustflags
are refused. Put verification budgets in the manifest's [trust] table. This
gate always requires full static discharge, the unix_hardened profile and
dependency verification; there is no advisory, unverified or function-skip mode.

Each run writes to a fresh target/trust-verification/run.* directory. The live
Targo exit status is the gate. Saved reports and logs are diagnostic records,
not replayable proof authority. This script never recovers or stops trustd.
EOF
}

die() { printf 'check-trust-verification: %s\n' "$*" >&2; exit 2; }

mode=check
packages=()
tuple_args=()
while [[ $# -gt 0 ]]; do
    case "$1" in
        -h|--help) usage; exit 0 ;;
        --check) mode=check; shift ;;
        --build) mode=build; shift ;;
        --tuple)
            [[ ${#tuple_args[@]} -eq 0 ]] || die "--tuple may be supplied only once"
            [[ $# -ge 2 && -n "$2" && "$2" != -* ]] || die "--tuple needs a file"
            tuple_path="$2"
            # Resolve relative to the caller, before entering the repository.
            [[ "$tuple_path" == /* ]] || tuple_path="$PWD/$tuple_path"
            tuple_args=(--tuple "$tuple_path")
            shift 2
            ;;
        -p|--package)
            [[ $# -ge 2 && -n "$2" && "$2" != -* ]] || die "$1 needs a package name"
            packages+=("$2")
            shift 2
            ;;
        *) die "unsupported argument '$1'; see --help" ;;
    esac
done

# Refuse overrides rather than silently dropping a caller's requested policy.
# Even obsolete flag channels are refused rather than silently ignored.
[[ -z "${TRUSTFLAGS+x}" ]] || die "TRUSTFLAGS is set; unset it before running this gate"
[[ -z "${CARGO_ENCODED_TRUSTFLAGS+x}" ]] \
    || die "CARGO_ENCODED_TRUSTFLAGS is set; unset it before running this gate"
for name in RUSTFLAGS CARGO_ENCODED_RUSTFLAGS \
    RUSTDOCFLAGS CARGO_ENCODED_RUSTDOCFLAGS CARGO_BUILD_RUSTFLAGS \
    RUSTC CARGO_BUILD_RUSTC RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER \
    CARGO_BUILD_RUSTC_WRAPPER CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER RUSTUP_TOOLCHAIN; do
    [[ -z "${!name-}" ]] || die "$name is set; unset it before running this gate"
done
jobs="${CARGO_BUILD_JOBS:-2}"
[[ "$jobs" == 1 || "$jobs" == 2 ]] || die "CARGO_BUILD_JOBS must be 1 or 2"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
SYSROOT="$(scripts/resolve-trust-tool.sh sysroot)"
# Hold this exact directory through tuple admission and Targo invocation, even
# if a rustup channel or package-store link moves after the first resolution.
export TRUST_MC_TRUST_TOOLCHAIN="$SYSROOT"
TARGO="$(scripts/resolve-trust-tool.sh targo)"
export PATH="$SYSROOT/bin:$PATH"

umask 077
mkdir -p target/trust-verification
report_dir="$(mktemp -d "$ROOT/target/trust-verification/run.XXXXXX")"
printf 'check-trust-verification: reports %s (diagnostics only)\n' "$report_dir"
# The JSON contains the exact parsed tuple and its digest, including the
# development identity's limits. Refusal must stop before any compiler work.
# ${a[@]+"${a[@]}"}: macOS /bin/bash 3.2 calls an empty array unbound under set -u.
if tools/tuple-check ${tuple_args[@]+"${tuple_args[@]}"} --json >"$report_dir/tuple.json"; then
    :
else
    status=$?
    printf 'check-trust-verification: tuple refused (exit %s); diagnostics: %s\n' \
        "$status" "$report_dir" >&2
    exit "$status"
fi
scripts/check-trust-lane-port.sh

selection=(--workspace)
if [[ ${#packages[@]} -gt 0 ]]; then
    selection=()
    for package in "${packages[@]}"; do
        selection+=(-p "$package")
    done
    printf 'check-trust-verification: DIAGNOSTIC SUBSET; selected packages:'
    printf ' %s' "${packages[@]}"
    printf '\n'
else
    printf 'check-trust-verification: full workspace, including engine/backend, plus dependencies\n'
fi

# Trust 0.12 ignores TRUSTFLAGS, and --certify alone retains the compiler's
# local-subject dependency scope. Tighten the actual Cargo rustflags channel.
# This workspace already has target.cfg(all()).rustflags; using build.rustflags
# instead would be shadowed by that target table. Cargo merges this array with
# the existing target flags, preserving their unrelated lint policy.
# Activation, unit roles and proof-transport authority remain Targo-owned.
command=("$TARGO" trust "$mode" --certify --hardened --trust-profile unix_hardened
    --config "target.'cfg(all())'.rustflags=['-Ztrust-verify-include-dependencies=yes']"
    --locked -j "$jobs" "${selection[@]}" --report-dir "$report_dir")
printf '%q ' "${command[@]}" >"$report_dir/command.txt"
printf '\n' >>"$report_dir/command.txt"

set +e
"${command[@]}" 2>&1 | tee "$report_dir/live.log"
statuses=("${PIPESTATUS[@]}")
set -e
printf '%s\n' "${statuses[0]}" >"$report_dir/exit.txt"
if [[ "${statuses[0]}" -ne 0 ]]; then
    printf 'check-trust-verification: live gate failed (exit %s); diagnostics: %s\n' \
        "${statuses[0]}" "$report_dir" >&2
    exit "${statuses[0]}"
fi
[[ "${statuses[1]}" -eq 0 ]] || die "could not retain the live diagnostic log in $report_dir"
printf 'check-trust-verification: live gate passed for the stated scope; saved reports carry no proof authority\n'
