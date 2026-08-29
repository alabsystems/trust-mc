# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Resolve an interpreter that can actually run this repo's manifest auditors.
#
# `scripts/*.py` parse TOML through `tomllib` (stdlib from 3.11) and fall back
# to the third-party `tomli` below that. Bare `python3` on macOS is the system
# 3.9, which has neither, so every auditor died at import with
# `ModuleNotFoundError: No module named 'tomli'` — and the callers reported it
# as "semantic AY manifest audit failed", which reads like a manifest defect
# rather than a missing interpreter. Probe instead of assuming: pick the first
# candidate that can import a TOML loader, and fail with the real reason if
# none can.
#
# Sets PYTHON. Source this, then call the auditors as "${PYTHON}" ... .

python_with_toml() {
    local candidate
    for candidate in "${TRUST_MC_PYTHON:-}" python3 python3.14 python3.13 python3.12 python3.11; do
        [[ -n "${candidate}" ]] || continue
        command -v "${candidate}" >/dev/null 2>&1 || continue
        if "${candidate}" -c 'import sys
if sys.version_info >= (3, 11):
    import tomllib
else:
    import tomli' >/dev/null 2>&1; then
            printf '%s\n' "${candidate}"
            return 0
        fi
    done
    printf 'error: no python3 on PATH can import tomllib (>=3.11) or tomli.\n' >&2
    printf '       tried, in order: TRUST_MC_PYTHON (=%s), python3, python3.14,\n' \
        "${TRUST_MC_PYTHON:-unset}" >&2
    printf '       python3.13, python3.12, python3.11.\n' >&2
    printf '       install python >= 3.11, or point TRUST_MC_PYTHON at one.\n' >&2
    return 1
}

PYTHON="$(python_with_toml)" || exit 1
export PYTHON
