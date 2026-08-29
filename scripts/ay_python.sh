# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Shared python3 resolver for the measurement scripts.
#
# Several helpers (lane_policy_query.py, ay_manifest_pin.py) parse TOML via
# the stdlib `tomllib`, which needs python >= 3.11. macOS ships
# /usr/bin/python3 as 3.9, so a bare `python3` silently fails the lane-policy
# query and every explicit-BMC lane resolution with it. Resolve a capable
# interpreter once and let every call site use "$AY_PYTHON_BIN".
#
# Override with AY_PYTHON=/path/to/python3 when needed.

ay_resolve_python3() {
    local candidate
    for candidate in "${AY_PYTHON:-}" python3 python3.14 python3.13 python3.12 python3.11; do
        [[ -z "$candidate" ]] && continue
        if command -v "$candidate" >/dev/null 2>&1 \
            && "$candidate" -c 'import tomllib' >/dev/null 2>&1; then
            printf '%s\n' "$candidate"
            return 0
        fi
    done
    echo "ERROR: no python3 with tomllib (>= 3.11) found; set AY_PYTHON" >&2
    return 1
}

if [[ -z "${AY_PYTHON_BIN:-}" ]]; then
    AY_PYTHON_BIN="$(ay_resolve_python3)" || exit 1
fi
export AY_PYTHON_BIN
