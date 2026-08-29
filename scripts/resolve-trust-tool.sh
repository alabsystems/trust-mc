#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

# Resolve an executable from the repository-pinned Trust toolchain without
# trusting ambient PATH ordering. Homebrew cargo/rustc can precede rustup's
# proxies on macOS; invoking either bare command would then compile a different
# program despite rust-toolchain.toml declaring channel = "trust".

set -euo pipefail

usage() {
    cat <<'EOF'
Usage: scripts/resolve-trust-tool.sh cargo|targo|rustc|sysroot

Print the exact executable (or sysroot) selected by rust-toolchain.toml.
TRUST_MC_RUSTUP may name an explicit rustup executable for hermetic callers.
EOF
}

case "${1:-}" in
    -h|--help)
        usage
        exit 0
        ;;
    cargo|targo|rustc|sysroot)
        requested="$1"
        ;;
    *)
        usage >&2
        exit 2
        ;;
esac
[[ $# -eq 1 ]] || { usage >&2; exit 2; }

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." >/dev/null 2>&1 && pwd)"

die() {
    printf 'resolve-trust-tool: error: %s\n' "$*" >&2
    exit 2
}

channel="$(
    awk -F'"' '/^[[:space:]]*channel[[:space:]]*=[[:space:]]*"/ { print $2; exit }' \
        "${ROOT_DIR}/rust-toolchain.toml"
)"
[[ -n "${channel}" ]] || die "cannot parse channel from rust-toolchain.toml"

rustup="${TRUST_MC_RUSTUP:-}"
if [[ -n "${rustup}" && "${rustup}" != */* ]]; then
    rustup="$(command -v "${rustup}" 2>/dev/null || true)"
fi
if [[ -z "${rustup}" ]]; then
    rustup="$(command -v rustup 2>/dev/null || true)"
fi
if [[ -z "${rustup}" && -n "${CARGO_HOME:-}" ]]; then
    for candidate in "${CARGO_HOME}/bin/rustup" "${CARGO_HOME}/bin/rustup.exe"; do
        if [[ -x "${candidate}" ]]; then
            rustup="${candidate}"
            break
        fi
    done
fi
if [[ -z "${rustup}" && -n "${HOME:-}" ]]; then
    for candidate in "${HOME}/.cargo/bin/rustup" "${HOME}/.cargo/bin/rustup.exe"; do
        if [[ -x "${candidate}" ]]; then
            rustup="${candidate}"
            break
        fi
    done
fi
[[ -n "${rustup}" && -x "${rustup}" ]] \
    || die "cannot find rustup; install it or set TRUST_MC_RUSTUP"

if ! rustc="$("${rustup}" which rustc --toolchain "${channel}" 2>/dev/null)"; then
    die "rustup cannot resolve rustc for pinned toolchain ${channel}"
fi
[[ -n "${rustc}" && -x "${rustc}" ]] \
    || die "rustup returned a missing rustc for pinned toolchain ${channel}: ${rustc:-<none>}"

if ! sysroot="$("${rustc}" --print sysroot 2>/dev/null)"; then
    die "pinned rustc cannot report its sysroot: ${rustc}"
fi
[[ -n "${sysroot}" && -d "${sysroot}" ]] \
    || die "pinned rustc returned a missing sysroot: ${sysroot:-<none>}"

find_frontend() {
    local name="$1"
    local candidate
    for candidate in "${sysroot}/bin/${name}" "${sysroot}/bin/${name}.exe"; do
        if [[ -x "${candidate}" ]]; then
            printf '%s\n' "${candidate}"
            return 0
        fi
    done
    return 1
}

cargo="$(find_frontend cargo || true)"
targo="$(find_frontend targo || true)"
[[ -n "${cargo}" ]] || die "pinned Trust sysroot has no cargo frontend: ${sysroot}"
[[ -n "${targo}" ]] || die "pinned Trust sysroot has no targo frontend: ${sysroot}"

case "${requested}" in
    cargo) printf '%s\n' "${cargo}" ;;
    targo) printf '%s\n' "${targo}" ;;
    rustc) printf '%s\n' "${rustc}" ;;
    sysroot) printf '%s\n' "${sysroot}" ;;
esac
