#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Build (or reuse) the external `ay` CLI at the AY revision root Cargo.toml
# pins, and print the binary's path on stdout.
#
# A counted run spawns an external `ay` for the BMC lane, and the driver
# refuses one whose build stamp names another commit
# ([AY:SOLVER_PIN_MISMATCH]). The unkeyed ~/Library/Caches/trust-mc-ay-cli
# cache went stale on every pin bump. Key both the pin and compiler identity:
#
#   <cache root>/trust-mc-ay-cli-<rev9>/compiler-<identity>/src          detached ay worktree at the pin
#   <cache root>/trust-mc-ay-cli-<rev9>/compiler-<identity>/lane         cargo cwd: ay's .cargo/config.toml
#                                                    minus every -Ztrust-* token
#   <cache root>/trust-mc-ay-cli-<rev9>/compiler-<identity>/release/ay   the binary (printed on stdout)
#
# <rev9> is the first nine characters of the pin, read through
# scripts/ay_manifest_pin.py. The build runs in the cache worktree, never in
# ../ay: that repository only receives `git worktree add`, so its HEAD and
# files do not move. A missing source pin refuses; first admit its exact object
# through native agh into the selected AY repository. No GitHub Git fetch runs.
# Existing unkeyed caches are never read or written.
#
# Idempotent: a binary whose `--version` already names the full 40-character
# pin and a matching compiler/policy/configuration/binary receipt is reused
# without building. Native distribution CPU policy is keyed; source and resolved
# Cargo policy are rechecked before every reuse and after compilation. A cache worktree that is dirty or at another
# commit is refused, never repaired. After a build the binary must name the
# full pin, or the script fails.
#
# Environment:
#   TRUST_MC_AY_REPO            ay repository the worktree is added from
#                               (default: ../ay beside this checkout)
#   TRUST_MC_AY_CLI_CACHE_ROOT  directory that holds trust-mc-ay-cli-<rev9>
#                               (default: ~/Library/Caches on macOS,
#                               ${XDG_CACHE_HOME:-~/.cache} elsewhere)
#   TRUST_MC_TARGO              targo executable (must match the resolved seal)
#                               (default: scripts/resolve-trust-tool.sh targo)
#   CARGO_BUILD_JOBS            passed through to the build
#
# Usage: scripts/build-pinned-ay-cli.sh [--print-path|--check-path]
#   --print-path   resolve the compiler, print its pin/compiler-derived binary
#                  path, and exit without creating a cache or building
#   --check-path   print only an existing binary with valid builder provenance

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

die() {
    printf 'build-pinned-ay-cli: error: %s\n' "$*" >&2
    exit 1
}

note() {
    printf 'build-pinned-ay-cli: %s\n' "$*" >&2
}

print_only=0
check_only=0
case "${1:-}" in
    "") ;;
    --print-path) print_only=1 ;;
    --check-path) check_only=1 ;;
    -h|--help)
        sed -n '7,40p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
        exit 0
        ;;
    *)
        printf 'usage: scripts/build-pinned-ay-cli.sh [--print-path|--check-path]\n' >&2
        exit 2
        ;;
esac
[[ $# -le 1 ]] || { printf 'usage: scripts/build-pinned-ay-cli.sh [--print-path|--check-path]\n' >&2; exit 2; }

# shellcheck source=scripts/lib/python-with-toml.sh
. "${ROOT_DIR}/scripts/lib/python-with-toml.sh"

pin="$("${PYTHON}" "${ROOT_DIR}/scripts/ay_manifest_pin.py" "${ROOT_DIR}")" \
    || die "cannot read the AY pin from ${ROOT_DIR}/Cargo.toml"
[[ "${pin}" =~ ^[0-9a-f]{40}$ ]] || die "AY pin is not a 40-character lowercase sha: ${pin}"

if [[ -n "${TRUST_MC_AY_CLI_CACHE_ROOT:-}" ]]; then
    cache_root="${TRUST_MC_AY_CLI_CACHE_ROOT}"
elif [[ "$(uname -s)" == "Darwin" ]]; then
    cache_root="${HOME}/Library/Caches"
else
    cache_root="${XDG_CACHE_HOME:-${HOME}/.cache}"
fi
# Resolve the held compiler before even considering a cached binary.
resolver="${ROOT_DIR}/scripts/resolve-trust-tool.sh"
pinned_targo="$("${resolver}" targo)" || die "cannot resolve the pinned Trust targo"
trustc="$("${resolver}" trustc)" || die "cannot resolve the pinned Trust compiler"
sysroot="$("${resolver}" sysroot)" || die "cannot resolve the pinned Trust sysroot"
targo="${TRUST_MC_TARGO:-${pinned_targo}}"
ay_repo="${TRUST_MC_AY_REPO:-${ROOT_DIR}/../ay}"
identity_tool="${ROOT_DIR}/scripts/ay_cli_build_identity.py"
builder="$("${PYTHON}" "${identity_tool}" identify "${sysroot}" "${trustc}" "${targo}" "${pinned_targo}" "${ay_repo}" "${pin}")" \
    || die "cannot identify the pinned compiler for AY"
compiler_key="$("${PYTHON}" "${identity_tool}" key "${builder}")" \
    || die "cannot key the pinned compiler for AY"
cache="${cache_root}/trust-mc-ay-cli-${pin:0:9}/compiler-${compiler_key}"
src="${cache}/src"
binary="${cache}/release/ay"
receipt="${cache}/builder.json"

if [[ "${print_only}" == 1 ]]; then
    printf '%s\n' "${binary}"
    exit 0
fi

names_pin() {
    [[ -x "${binary}" ]] || return 1
    local version
    version="$("${binary}" --version 2>&1)" || return 1
    # The full commit must appear as a whole 40-character token; a shared
    # prefix (rev9) or a longer hex run is not a match.
    [[ "${version}" =~ (^|[^0-9a-f])${pin}([^0-9a-f]|$) ]]
}

if [[ "${check_only}" == 1 && ! -d "${src}" ]]; then
    die "${binary} has no valid compiler-bound AY build receipt"
fi

if [[ -e "${src}" ]]; then
    git -C "${src}" rev-parse --is-inside-work-tree >/dev/null 2>&1 \
        || die "${src} exists but is not a git worktree; move it aside"
    [[ "$(git -C "${src}" rev-parse --show-toplevel)" == "$(cd "${src}" && pwd -P)" ]] \
        || die "${src} is inside another git worktree, not a worktree of its own; move it aside"
    src_head="$(git -C "${src}" rev-parse HEAD)"
    [[ "${src_head}" == "${pin}" ]] \
        || die "${src} is at ${src_head}, not the pin ${pin}; move it aside"
    [[ -z "$(git -C "${src}" status --porcelain --untracked-files=normal)" ]] \
        || die "${src} is dirty; a build from it would not be the pinned source"
else
    git -C "${ay_repo}" rev-parse --git-dir >/dev/null 2>&1 \
        || die "ay repository not found: ${ay_repo} (set TRUST_MC_AY_REPO)"
    if ! git -C "${ay_repo}" cat-file -e "${pin}^{commit}" 2>/dev/null; then
        die "the pin ${pin} is not in ${ay_repo}; admit its exact source through native agh before building"
    fi
    mkdir -p "${cache}"
    git -C "${ay_repo}" worktree add --detach "${src}" "${pin}" >&2 \
        || die "git worktree add ${src} ${pin} failed"
fi

# The CLI is an UNVERIFIED artifact of trust-mc's lane, not a verified build of
# ay's. ay's own .cargo/config.toml states ay's verification posture on every
# unit (-Ztrust-* tokens in rustflags tables; at 4cadc2bf1 that includes
# -Ztrust-ir-lower=strict, which fails libc's build script on seal 8590 even
# under `targo --unverified`, and a --config override cannot clear an array
# cargo concatenates). So the build runs from a lane directory of its own
# whose .cargo/config.toml is ay's with every -Ztrust-* token removed
# (scripts/ay_cli_lane_config.py; profiles, target-cpu and [env] are kept),
# with --manifest-path naming the pinned worktree's manifest. Cargo discovers
# config from the working directory, never from the manifest, so ay's file is
# not read. A worktree without a .cargo/config.toml gets an empty lane config.
# The build-policy helper then appends the native distribution CPU to Cargo's
# resolved target/build/host flag segments without replacing their other policy.
lane="${cache}/lane"
rm -rf "${lane}"
mkdir -p "${lane}/.cargo"
if [[ -f "${src}/.cargo/config.toml" ]]; then
    "${PYTHON}" "${ROOT_DIR}/scripts/ay_cli_lane_config.py" \
        "${src}/.cargo/config.toml" "${lane}/.cargo/config.toml" \
        || die "cannot derive the unverified-lane cargo config from ${src}/.cargo/config.toml"
else
    : > "${lane}/.cargo/config.toml"
fi

builder="$("${PYTHON}" "${identity_tool}" configure "${builder}" "${lane}" "${src}")" \
    || die "cannot bind the resolved native AY build configuration"
if names_pin && "${PYTHON}" "${identity_tool}" matches "${receipt}" "${binary}" "${pin}" "${builder}"; then
    printf '%s\n' "${binary}"
    exit 0
fi
if [[ "${check_only}" == 1 ]]; then
    die "${binary} has no valid compiler-bound AY build receipt"
fi
if [[ -e "${binary}" ]]; then
    note "${binary} lacks matching source/compiler/policy/configuration/binary provenance; rebuilding"
fi
rm -f "${receipt}"

note "building ay at ${pin} in ${src} into ${cache} (lane config ${lane}/.cargo/config.toml)"
"${PYTHON}" "${identity_tool}" build "${builder}" "${lane}" "${src}" "${cache}" \
    >&2 || die "targo --unverified build --release -p ay --features cli failed"

names_pin || die "${binary} built from ${src} does not name the pin ${pin} in --version"
[[ "$(git -C "${src}" rev-parse HEAD)" == "${pin}" ]] \
    || die "${src} changed HEAD during the build; refusing a pinned-source receipt"
[[ -z "$(git -C "${src}" status --porcelain --untracked-files=normal)" ]] \
    || die "${src} changed during the build; refusing a pinned-source receipt"
after="$("${PYTHON}" "${identity_tool}" identify "${sysroot}" "${trustc}" "${targo}" "${pinned_targo}" "${ay_repo}" "${pin}")" \
    || die "cannot recheck the AY builder"
after="$("${PYTHON}" "${identity_tool}" configure "${after}" "${lane}" "${src}")" \
    || die "cannot recheck the resolved AY build configuration"
[[ "${after}" == "${builder}" ]] || die "the compiler or configuration changed during the AY build"
"${PYTHON}" "${identity_tool}" record "${receipt}" "${binary}" "${pin}" "${builder}" \
    || die "cannot record the AY builder identity"
printf '%s\n' "${binary}"
