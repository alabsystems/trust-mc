#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
set -euo pipefail
[[ $# == 4 ]] || { printf 'usage: stage-bundled-ay.sh BINARY BUNDLE SEAL COMPILER_COMMIT\n' >&2; exit 2; }
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
. "${ROOT_DIR}/scripts/lib/python-with-toml.sh"
pin="$("${PYTHON}" "${ROOT_DIR}/scripts/ay_manifest_pin.py" "${ROOT_DIR}")"
exec "${PYTHON}" "${ROOT_DIR}/scripts/ay_cli_build_identity.py" stage-bundle \
    "$1" "$2" "${pin}" "$3" "$3/bin/trustc" "$3/bin/targo" "$4"
