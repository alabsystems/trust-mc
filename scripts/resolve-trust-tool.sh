#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

# Resolve an executable from the repository-pinned Trust toolchain without
# trusting ambient PATH ordering. Homebrew cargo/rustc can precede rustup's
# proxies on macOS; invoking either bare command would then compile a different
# program despite rust-toolchain.toml declaring channel = "trust".
#
# It resolves the Trust names only: `targo` (the frontend) and `trustc` (the
# compiler), both from the sysroot the pinned compiler reports. Owner ruling
# 2026-09-23: never a stock `cargo` or `rustc`. The sysroot's `cargo` is the
# upstream-Cargo persona and is refused here. Its `rustc` is the same binary
# as `trustc` under the compatibility name, and is refused too, so no caller
# learns the stock spelling from this script.
#
# rustup's `trust` toolchain follows the host's moving `current` seal, so a long
# measurement run can hold one Trust build with TRUST_MC_TRUST_TOOLCHAIN. It
# replaces rust-toolchain.toml's channel for every tool resolved here, and a
# value that does not resolve is refused, never ignored.

set -euo pipefail

usage() {
    cat <<'EOF_USAGE'
Usage: scripts/resolve-trust-tool.sh targo|trustc|sysroot

Print the exact executable (or sysroot) selected by rust-toolchain.toml:
`targo`, the Trust frontend; `trustc`, the Trust compiler; or the sysroot.
There is no `cargo` or `rustc` mode: the seal's `bin/cargo` is Targo acting
as upstream cargo, which takes no lane (build with `targo --unverified` or
`targo trust`), and the compiler's Trust name is `trustc`.
TRUST_MC_TRUST_TOOLCHAIN, when set, is used in place of rust-toolchain.toml's
channel: either a rustup toolchain name (e.g. trust-8571) or an absolute seal
directory whose bin/rustc reports that same directory as its sysroot. A value
that does not resolve exits 2, and so does an absolute value that is itself a
symbolic link (store/trust/current, ~/.rustup/toolchains/trust), which follows
the moving seal. A rustup name holds a build only if its toolchain is linked to
a numbered seal; a toolchain linked to another link (`trust` ->
store/trust/current) follows the moving seal and exits 2.
TRUST_MC_RUSTUP may name an explicit rustup executable for hermetic callers.
EOF_USAGE
}

case "${1:-}" in
    -h|--help)
        usage
        exit 0
        ;;
    targo|trustc|sysroot)
        requested="$1"
        ;;
    cargo|rustc)
        printf 'resolve-trust-tool: error: `%s` is a stock name and is not resolved; ask for `%s`, the Trust toolchain'"'"'s name for it (owner ruling 2026-09-23)\n' \
            "$1" "$([[ "$1" == cargo ]] && echo targo || echo trustc)" >&2
        exit 2
        ;;
    *)
        usage >&2
        exit 2
        ;;
esac
[[ $# -eq 1 ]] || { usage >&2; exit 2; }

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." >/dev/null 2>&1 && pwd)"
OVERRIDE_ENV="TRUST_MC_TRUST_TOOLCHAIN"

die() {
    printf 'resolve-trust-tool: error: %s\n' "$*" >&2
    exit 2
}

find_rustup() {
    local rustup="${TRUST_MC_RUSTUP:-}"
    local candidate
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
    printf '%s\n' "${rustup}"
}

rustup_rustc() {
    local toolchain="$1" origin="$2"
    local rustup rustc
    rustup="$(find_rustup)"
    # rustup >= 1.28 installs a missing official toolchain on `which` unless told
    # not to; a name that is not installed must be refused, not downloaded.
    if ! rustc="$(RUSTUP_AUTO_INSTALL=0 "${rustup}" which rustc --toolchain "${toolchain}" 2>/dev/null)"; then
        die "rustup cannot resolve rustc for ${origin}"
    fi
    [[ -n "${rustc}" && -x "${rustc}" ]] \
        || die "rustup returned a missing rustc for ${origin}: ${rustc:-<none>}"
    printf '%s\n' "${rustc}"
}

seal_directory=""
if [[ -n "${TRUST_MC_TRUST_TOOLCHAIN+set}" ]]; then
    toolchain="${TRUST_MC_TRUST_TOOLCHAIN}"
    origin="${OVERRIDE_ENV}=${toolchain}"
    [[ -n "${toolchain}" ]] \
        || die "${OVERRIDE_ENV} is set but empty; unset it to use rust-toolchain.toml's channel"
    if [[ "${toolchain}" == /* ]]; then
        [[ -d "${toolchain}" ]] || die "${origin} names no directory"
        link="${toolchain}"
        while [[ "${link}" == */ && "${link}" != / ]]; do
            link="${link%/}"
        done
        # store/trust/current and ~/.rustup/toolchains/trust are links that move
        # with the host's seal; holding one build means naming its directory.
        [[ ! -L "${link}" ]] \
            || die "${origin} is a symbolic link (to $(readlink "${link}")); name the numbered seal directory itself"
        rustc=""
        for candidate in "${toolchain}/bin/rustc" "${toolchain}/bin/rustc.exe"; do
            if [[ -x "${candidate}" ]]; then
                rustc="${candidate}"
                break
            fi
        done
        [[ -n "${rustc}" ]] || die "${origin} is not a seal directory: it has no bin/rustc"
        seal_directory="$(cd "${toolchain}" >/dev/null 2>&1 && pwd -P)" \
            || die "${origin} cannot be entered"
        # Print canonical paths, so every tool names the build that resolved.
        rustc="${seal_directory}/bin/${rustc##*/}"
    elif [[ "${toolchain}" =~ ^[A-Za-z0-9][A-Za-z0-9._+-]*$ ]]; then
        rustc="$(rustup_rustc "${toolchain}" "${origin}")"
        # A linked rustup toolchain holds one build only when its link names a real
        # directory. ~/.rustup/toolchains/trust -> store/trust/current is a link to
        # a link that moves with the host's seal.
        toolchain_dir="$(dirname "$(dirname "${rustc}")")"
        if [[ -L "${toolchain_dir}" ]]; then
            link_target="$(readlink "${toolchain_dir}")"
            [[ "${link_target}" == /* ]] || link_target="$(dirname "${toolchain_dir}")/${link_target}"
            while [[ "${link_target}" == */ && "${link_target}" != / ]]; do
                link_target="${link_target%/}"
            done
            [[ ! -L "${link_target}" ]] \
                || die "${origin} links to ${link_target}, itself a symbolic link (to $(readlink "${link_target}")) that follows the moving seal; link the toolchain to the numbered seal directory itself"
        fi
    else
        die "${origin} is neither a rustup toolchain name nor an absolute seal directory"
    fi
else
    channel="$(
        awk -F'"' '/^[[:space:]]*channel[[:space:]]*=[[:space:]]*"/ { print $2; exit }' \
            "${ROOT_DIR}/rust-toolchain.toml"
    )"
    [[ -n "${channel}" ]] || die "cannot parse channel from rust-toolchain.toml"
    origin="pinned toolchain ${channel}"
    rustc="$(rustup_rustc "${channel}" "${origin}")"
fi

if ! sysroot="$("${rustc}" --print sysroot 2>/dev/null)"; then
    die "pinned rustc cannot report its sysroot: ${rustc} (${origin})"
fi
[[ -n "${sysroot}" && -d "${sysroot}" ]] \
    || die "pinned rustc returned a missing sysroot: ${sysroot:-<none>} (${origin})"

if [[ -n "${seal_directory}" ]]; then
    # A directory whose bin/rustc is a rustup proxy (~/.cargo, say) would
    # resolve rust-toolchain.toml's moving channel behind the override's back.
    reported="$(cd "${sysroot}" >/dev/null 2>&1 && pwd -P)" \
        || die "${origin}: cannot enter the sysroot its bin/rustc reports: ${sysroot}"
    [[ "${reported}" == "${seal_directory}" ]] \
        || die "${origin} is not a seal directory: its bin/rustc reports sysroot ${sysroot}"
    sysroot="${seal_directory}"
fi

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

targo="$(find_frontend targo || true)"
trustc="$(find_frontend trustc || true)"
[[ -n "${targo}" ]] || die "pinned Trust sysroot has no targo frontend: ${sysroot} (${origin})"
[[ -n "${trustc}" ]] || die "pinned Trust sysroot has no trustc compiler: ${sysroot} (${origin})"

case "${requested}" in
    targo) printf '%s\n' "${targo}" ;;
    trustc) printf '%s\n' "${trustc}" ;;
    sysroot) printf '%s\n' "${sysroot}" ;;
esac
