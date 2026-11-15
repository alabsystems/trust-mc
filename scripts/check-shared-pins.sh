#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Verify the selected immutable non-AY authorities consumed by trust-mc.
# Newer canonical main may change production source; those changes neither
# qualify nor invalidate this unchanged selected cut. Latest-main source drift
# is an explicit diagnostic in check-shared-pin-drift.sh. This gate requires
# clean physical selected checkouts, canonical main ancestry, uniform manifest
# declarations, the locked resolved graph and the committed measurement tuple.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TRUST_IR_REPO="${ROOT_DIR}/../trust-ir"
TRUST_VC_REPO="${ROOT_DIR}/../trust-vc"
CLEAN_REPO="${ROOT_DIR}/../clean"
TRUST_MC_TARGO="$("${ROOT_DIR}/scripts/resolve-trust-tool.sh" targo)"

# shellcheck source=scripts/lib/python-with-toml.sh
. "${ROOT_DIR}/scripts/lib/python-with-toml.sh"

# Isolate reads of reused sibling repositories, including cached graft files.
git() { "${PYTHON}" "${ROOT_DIR}/scripts/git_authority_environment.py" "$@"; }

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

require_frozen_content_checkout() {
    local label="$1"
    local checkout="$2"
    local expected="$3"
    local repository="$4"
    local remote
    local fetched_main

    require_clean_checkout "${label}" "${checkout}" "${expected}"
    remote="$(canonical_remote "${checkout}" "${repository}")" \
        || die "${label} checkout has no canonical alabsystems/${repository} remote"
    # A frozen content pin need not equal today's branch tip. It must remain in
    # canonical main history. Independently observed main snapshots may advance
    # only along checked ancestry. Forks and rewinds are refused.
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

trust_ir_main_rev="$(require_frozen_content_checkout \
    TrustIR "${TRUST_IR_REPO}" "${trust_ir_rev}" trust-ir)"
# TrustIR's proof-producing builder consumes the Clean kernel. Auditing only
# trust-mc's direct TrustIR revision would allow that transitive trust root to
# drift silently, especially because the local TrustIR path patch masks its Git
# identity in this workspace. Inspect the canonical TrustIR checkout itself,
# require all of its Clean declarations to agree, and then prove that Cargo's
# transitive clean-kernel package resolves to that exact Git authority.
clean_audit="$("${PYTHON}" "${ROOT_DIR}/scripts/check_first_party_git_pins.py" \
    "${TRUST_IR_REPO}" clean)" || die "semantic Clean manifest audit failed"
read -r clean_rev clean_entries <<< "${clean_audit}"
clean_main_rev="$(require_frozen_content_checkout \
    Clean "${CLEAN_REPO}" "${clean_rev}" clean)"
trust_vc_audit="$("${PYTHON}" "${ROOT_DIR}/scripts/check_first_party_git_pins.py" \
    "${ROOT_DIR}" trust-vc)" || die "semantic trust-vc manifest audit failed"
read -r trust_vc_rev trust_vc_entries <<< "${trust_vc_audit}"
trust_vc_main_rev="$(require_frozen_content_checkout \
    trust-vc "${TRUST_VC_REPO}" "${trust_vc_rev}" trust-vc)"
"${PYTHON}" "${ROOT_DIR}/scripts/check_shared_pin_graph.py" \
    "${ROOT_DIR}" "${TRUST_MC_TARGO}" "${trust_ir_rev}" "${trust_vc_rev}" "${clean_rev}" \
    || die 'selected shared authority graph or tuple disagrees'

# Check physical identities again after resolution; no moving branch or dirty
# sibling may stand in for the selected source while its graph is inspected.
require_clean_checkout TrustIR "${TRUST_IR_REPO}" "${trust_ir_rev}"
require_clean_checkout trust-vc "${TRUST_VC_REPO}" "${trust_vc_rev}"
require_clean_checkout Clean "${CLEAN_REPO}" "${clean_rev}"
printf 'check-shared-pins: ok: selected TrustIR %s / Clean %s / trust-vc %s; canonical descendant observations %s / %s / %s; locked graph and tuple agree (later sources unqualified)\n' \
    "${trust_ir_rev}" "${clean_rev}" "${trust_vc_rev}" \
    "${trust_ir_main_rev}" "${clean_main_rev}" "${trust_vc_main_rev}"
