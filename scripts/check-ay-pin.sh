#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Verify the AY authority used by this path-patched workspace. The declared git
# revisions, Cargo's actually resolved entry-package IDs, and the fixed ../ay
# checkout must all name the same clean authority.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="${ROOT_DIR}/Cargo.toml"
AY_REPO="${ROOT_DIR}/../ay"
TRUST_MC_CARGO="$("${ROOT_DIR}/scripts/resolve-trust-tool.sh" cargo)"
AY_PINNED_PACKAGES=(
    ay-dpll
    ay-core
    ay-frontend
    ay-chc
    ay-bindings
    ay
    ay-sys
    ay-encode
)
AY_PATCHED_PACKAGES=(
    ay
    ay-core
    ay-dpll
    ay-frontend
    ay-proof
    ay-translate
    ay-chc
    ay-allsat
    ay-sat
    ay-bindings
    ay-sys
    ay-encode
)

# shellcheck source=scripts/lib/python-with-toml.sh
. "${ROOT_DIR}/scripts/lib/python-with-toml.sh"

die() {
    printf 'check-ay-pin: error: %s\n' "$*" >&2
    exit 1
}

pin_audit="$("${PYTHON}" "${ROOT_DIR}/scripts/check_first_party_git_pins.py" \
    "${ROOT_DIR}" ay)" || die "semantic AY manifest audit failed"
read -r declared_rev manifest_entries <<< "${pin_audit}"

for package in "${AY_PATCHED_PACKAGES[@]}"; do
    checkout_manifest="${AY_REPO}/crates/${package}/Cargo.toml"
    [[ -f "${checkout_manifest}" ]] \
        || die "missing checkout manifest for ${package}: ${checkout_manifest}"
    resolved_id="$("${TRUST_MC_CARGO}" pkgid --frozen --manifest-path "${MANIFEST}" "${package}")" \
        || die "Cargo could not resolve ${package} from ${MANIFEST}"
    checkout_id="$("${TRUST_MC_CARGO}" pkgid --frozen --manifest-path "${checkout_manifest}")" \
        || die "Cargo could not identify checkout package ${checkout_manifest}"
    [[ "${resolved_id}" == "${checkout_id}" ]] \
        || die "Cargo resolves ${package} as ${resolved_id}, not checkout ${checkout_id}"
done
[[ "${manifest_entries}" -ge "${#AY_PINNED_PACKAGES[@]}" ]] \
    || die "repository-wide AY manifest scan found only ${manifest_entries} entries"

git -C "${AY_REPO}" rev-parse --is-inside-work-tree >/dev/null 2>&1 \
    || die "AY_REPO is not a git worktree: ${AY_REPO}"
checkout_rev="$(git -C "${AY_REPO}" rev-parse HEAD)"
[[ "${checkout_rev}" == "${declared_rev}" ]] \
    || die "${AY_REPO} HEAD ${checkout_rev} differs from manifest ${declared_rev}"
[[ -z "$(git -C "${AY_REPO}" status --porcelain --untracked-files=normal)" ]] \
    || die "AY checkout is dirty: ${AY_REPO}"
ay_remote=""
while IFS= read -r candidate_remote; do
    candidate_url="$(git -C "${AY_REPO}" remote get-url "${candidate_remote}" 2>/dev/null)" \
        || continue
    case "${candidate_url%/}" in
        "https://github.com/alabsystems/ay"|\
        "https://github.com/alabsystems/ay.git"|\
        "ssh://git@github.com/alabsystems/ay"|\
        "ssh://git@github.com/alabsystems/ay.git"|\
        "git@github.com:alabsystems/ay"|\
        "git@github.com:alabsystems/ay.git")
            ay_remote="${candidate_remote}"
            break
            ;;
    esac
done < <(git -C "${AY_REPO}" remote)
[[ -n "${ay_remote}" ]] \
    || die "AY checkout has no canonical alabsystems/ay remote"
# The AY pin is a FROZEN CONTENT pin, not a tip mirror: it names the exact
# revision a burndown/soundness gate was measured against, so it necessarily
# lags whatever `alabsystems/ay` main has been pushed to since. Requiring
# equality with the live tip (`exact`) made this check unsatisfiable in
# practice — ay main advanced three times during a single bump gate — and a
# check that can never pass stops being read. `frozen` keeps the property that
# actually matters and that VERSIONING/RELEASE describe: the pin must be
# reachable from canonical main history, which still fail-closes on a dev-only
# or rewritten sha. Same idiom as `require_frozen_content_checkout` in
# scripts/check-shared-pins.sh.
"${PYTHON}" "${ROOT_DIR}/scripts/check_live_main.py" \
    frozen "${AY_REPO}" "${ay_remote}" "${declared_rev}" >/dev/null \
    || die "AY live ${ay_remote}/main verification failed"

printf 'check-ay-pin: ok: %s required / %s total uniform entries and %s patched packages resolve to clean private-main %s HEAD at %s\n' \
    "${#AY_PINNED_PACKAGES[@]}" "${manifest_entries}" \
    "${#AY_PATCHED_PACKAGES[@]}" "${AY_REPO}" "${declared_rev}"
