#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Verify the non-AY shared authorities consumed by trust-mc. Cargo's root
# patches deliberately make the local TrustIR checkout authoritative during
# co-development, so a successful build alone cannot detect stale or divergent
# manifest revisions. TrustIR in turn consumes the Clean kernel, whose exact Git
# source must remain visible in Cargo's resolution. Likewise the trust-vc
# adapter has one independently pinned Git dependency whose source must agree
# with the sibling checkout used by the Trust superproject.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TRUST_IR_REPO="${ROOT_DIR}/../trust-ir"
TRUST_VC_REPO="${ROOT_DIR}/../trust-vc"
CLEAN_REPO="${ROOT_DIR}/../clean"
TRUST_MC_CARGO="$("${ROOT_DIR}/scripts/resolve-trust-tool.sh" cargo)"

# shellcheck source=scripts/lib/python-with-toml.sh
. "${ROOT_DIR}/scripts/lib/python-with-toml.sh"

# A tracked Cargo manifest must remain consumable outside the author's host.
# Run this before dependency checkout checks so an absolute-path regression is
# reported even while an intentionally parked downstream pin is stale.
"${PYTHON}" "${ROOT_DIR}/scripts/check_portable_manifests.py" "${ROOT_DIR}"

die() {
    printf 'check-shared-pins: error: %s\n' "$*" >&2
    exit 1
}

require_clean_checkout() {
    local label="$1"
    local checkout="$2"
    local expected="$3"
    local actual

    git -C "${checkout}" rev-parse --is-inside-work-tree >/dev/null 2>&1 \
        || die "${label} checkout is not a git worktree: ${checkout}"
    actual="$(git -C "${checkout}" rev-parse HEAD)"
    [[ "${actual}" == "${expected}" ]] \
        || die "${label} checkout HEAD ${actual} differs from manifest ${expected}"
    [[ -z "$(git -C "${checkout}" status --porcelain --untracked-files=normal)" ]] \
        || die "${label} checkout is dirty: ${checkout}"
}

canonical_remote() {
    local checkout="$1"
    local repository="$2"
    local remote
    local remote_url

    while IFS= read -r remote; do
        remote_url="$(git -C "${checkout}" remote get-url "${remote}" 2>/dev/null)" \
            || continue
        case "${remote_url%/}" in
            "https://github.com/alabsystems/${repository}"|\
            "https://github.com/alabsystems/${repository}.git"|\
            "ssh://git@github.com/alabsystems/${repository}"|\
            "ssh://git@github.com/alabsystems/${repository}.git"|\
            "git@github.com:alabsystems/${repository}"|\
            "git@github.com:alabsystems/${repository}.git")
                printf '%s\n' "${remote}"
                return 0
                ;;
        esac
    done < <(git -C "${checkout}" remote)
    return 1
}

require_private_main_checkout() {
    local label="$1"
    local checkout="$2"
    local expected="$3"
    local repository="$4"
    local remote

    require_clean_checkout "${label}" "${checkout}" "${expected}"
    remote="$(canonical_remote "${checkout}" "${repository}")" \
        || die "${label} checkout has no canonical alabsystems/${repository} remote"
    # Refresh the tracking ref and independently query the live branch. The
    # helper fails closed on stale, missing, or concurrently advanced refs.
    "${PYTHON}" "${ROOT_DIR}/scripts/check_live_main.py" \
        exact "${checkout}" "${remote}" "${expected}" >/dev/null \
        || die "${label} live ${remote}/main verification failed"
}

require_frozen_content_checkout() {
    local label="$1"
    local checkout="$2"
    local expected="$3"
    local repository="$4"
    local remote
    local fetched_main

    git -C "${checkout}" rev-parse --is-inside-work-tree >/dev/null 2>&1 \
        || die "${label} checkout is not a git worktree: ${checkout}"
    [[ -z "$(git -C "${checkout}" status --porcelain --untracked-files=normal)" ]] \
        || die "${label} checkout is dirty: ${checkout}"
    remote="$(canonical_remote "${checkout}" "${repository}")" \
        || die "${label} checkout has no canonical alabsystems/${repository} remote"
    # A frozen content pin need not equal today's branch tip. It must remain in
    # canonical main history, with fetched and independently queried live refs
    # agreeing. The helper regression-tests both acceptance and rejection.
    fetched_main="$("${PYTHON}" "${ROOT_DIR}/scripts/check_live_main.py" \
        frozen "${checkout}" "${remote}" "${expected}")" \
        || die "${label} frozen live ${remote}/main verification failed"

    if [[ "${expected}" != "${fetched_main}" ]]; then
        printf 'check-shared-pins: note: %s frozen content %s intentionally lags descendant live main %s\n' \
            "${label}" "${expected}" "${fetched_main}" >&2
    fi
    printf '%s\n' "${fetched_main}"
}

trust_ir_audit="$("${PYTHON}" "${ROOT_DIR}/scripts/check_first_party_git_pins.py" \
    "${ROOT_DIR}" trust-ir)" || die "semantic TrustIR manifest audit failed"
read -r trust_ir_rev trust_ir_entries <<< "${trust_ir_audit}"

require_private_main_checkout TrustIR "${TRUST_IR_REPO}" "${trust_ir_rev}" trust-ir
for package in trust-ir trust-ir-build; do
    resolved_id="$("${TRUST_MC_CARGO}" pkgid --frozen --manifest-path "${ROOT_DIR}/Cargo.toml" "${package}")" \
        || die "Cargo could not resolve ${package}"
    checkout_id="$("${TRUST_MC_CARGO}" pkgid --frozen --manifest-path \
        "${TRUST_IR_REPO}/crates/${package}/Cargo.toml")" \
        || die "Cargo could not identify ${package} in ${TRUST_IR_REPO}"
    [[ "${resolved_id}" == "${checkout_id}" ]] \
        || die "Cargo resolves ${package} as ${resolved_id}, not checkout ${checkout_id}"
done

# TrustIR's proof-producing builder consumes the Clean kernel. Auditing only
# trust-mc's direct TrustIR revision would allow that transitive trust root to
# drift silently, especially because the local TrustIR path patch masks its Git
# identity in this workspace. Inspect the canonical TrustIR checkout itself,
# require all of its Clean declarations to agree, and then prove that Cargo's
# transitive clean-kernel package resolves to that exact Git authority.
CLEAN_URL='https://github.com/alabsystems/clean.git'
clean_audit="$("${PYTHON}" "${ROOT_DIR}/scripts/check_first_party_git_pins.py" \
    "${TRUST_IR_REPO}" clean)" || die "semantic Clean manifest audit failed"
read -r clean_rev clean_entries <<< "${clean_audit}"
clean_main_rev="$(require_frozen_content_checkout \
    Clean "${CLEAN_REPO}" "${clean_rev}" clean)"
resolved_clean="$("${TRUST_MC_CARGO}" pkgid --frozen --manifest-path "${ROOT_DIR}/Cargo.toml" \
    clean-kernel)" || die 'Cargo could not resolve clean-kernel'
case "${resolved_clean}" in
    "git+${CLEAN_URL}?rev=${clean_rev}"*) ;;
    *) die "Cargo resolves clean-kernel as ${resolved_clean}, not rev ${clean_rev}" ;;
esac

TRUST_VC_URL='https://github.com/alabsystems/trust-vc.git'
trust_vc_audit="$("${PYTHON}" "${ROOT_DIR}/scripts/check_first_party_git_pins.py" \
    "${ROOT_DIR}" trust-vc)" || die "semantic trust-vc manifest audit failed"
read -r trust_vc_rev trust_vc_entries <<< "${trust_vc_audit}"
require_private_main_checkout trust-vc "${TRUST_VC_REPO}" "${trust_vc_rev}" trust-vc
resolved_vc="$("${TRUST_MC_CARGO}" pkgid --frozen --manifest-path "${ROOT_DIR}/Cargo.toml" \
    trust-vc-merge-contract)" \
    || die 'Cargo could not resolve trust-vc-merge-contract'
case "${resolved_vc}" in
    "git+${TRUST_VC_URL}?rev=${trust_vc_rev}"*) ;;
    *) die "Cargo resolves trust-vc-merge-contract as ${resolved_vc}, not rev ${trust_vc_rev}" ;;
esac

printf 'check-shared-pins: ok: %s TrustIR, %s Clean, and %s trust-vc declarations are uniform and clean at %s / %s (live main %s) / %s\n' \
    "${trust_ir_entries}" "${clean_entries}" "${trust_vc_entries}" \
    "${trust_ir_rev}" "${clean_rev}" "${clean_main_rev}" "${trust_vc_rev}"
