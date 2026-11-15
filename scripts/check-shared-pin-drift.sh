#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Explicit latest-main equivalence diagnostic, separate from source publication.
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "${ROOT_DIR}/scripts/lib/python-with-toml.sh"
TARGO="$("${ROOT_DIR}/scripts/resolve-trust-tool.sh" targo)"
for repository in trust-ir trust-vc; do
    audit="$("${PYTHON}" "${ROOT_DIR}/scripts/check_first_party_git_pins.py" "${ROOT_DIR}" "${repository}")"
    read -r revision entries <<< "${audit}"
    checkout="${ROOT_DIR}/../${repository}"
    # Require the same canonical family even for this optional diagnostic.
    remote=""
    while IFS= read -r candidate; do
        url="$(git -C "${checkout}" remote get-url "${candidate}")"
        case "${url%/}" in
            "https://github.com/alabsystems/${repository}"|\
            "https://github.com/alabsystems/${repository}.git"|\
            "ssh://git@github.com/alabsystems/${repository}"|\
            "ssh://git@github.com/alabsystems/${repository}.git"|\
            "git@github.com:alabsystems/${repository}"|\
            "git@github.com:alabsystems/${repository}.git") remote="${candidate}"; break ;;
        esac
    done < <(git -C "${checkout}" remote)
    [[ -n "${remote}" ]] || { echo "no canonical ${repository} remote" >&2; exit 1; }
    if [[ "${repository}" == trust-ir ]]; then
        packages=(trust-ir trust-ir-build)
    else
        packages=(trust-vc-merge-contract)
    fi
    observed_main="$("${PYTHON}" "${ROOT_DIR}/scripts/check_live_main.py" frozen "${checkout}" "${remote}" "${revision}")"
    "${PYTHON}" "${ROOT_DIR}/scripts/pinned_package_paths.py" drift \
        --consumer "${ROOT_DIR}/Cargo.toml" --exclusions "${ROOT_DIR}/scripts/pin-exclusions.toml" \
        --repository "${repository}" "${TARGO}" "${checkout}" "${revision}" "${observed_main}" "${packages[@]}"
done
