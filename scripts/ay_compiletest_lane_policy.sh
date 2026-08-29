#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Shared lane-policy helpers for scripts/ay-compiletest.sh (Part of #1037).

LANE_POLICY_QUERY_SCRIPT="${LANE_POLICY_QUERY_SCRIPT:-$SCRIPT_DIR/lane_policy_query.py}"

file_flags_specify_unwind() {
    local file_flags="$1"
    [[ "$file_flags" =~ (^|[[:space:]])--default-unwind([[:space:]]|$) || "$file_flags" =~ (^|[[:space:]])--default-unwind=[^[:space:]]+ || "$file_flags" =~ (^|[[:space:]])--unwind([[:space:]]|$) || "$file_flags" =~ (^|[[:space:]])--unwind=[^[:space:]]+ ]]
}

LANE_POLICY_LAST_KEY=""
CURRENT_LANE="chc"
CURRENT_LANE_UNWIND=""
CURRENT_LANE_REASON=""
CURRENT_LANE_ISSUE=""
LANE_POLICY_EXTRA_FLAGS=()

normalize_lane_policy_path() {
    local file="$1"
    while [[ "$file" == ./* ]]; do
        file="${file#./}"
    done
    if [[ "$file" == "$TRUST_MC_DIR/"* ]]; then
        file="${file#$TRUST_MC_DIR/}"
    fi
    printf '%s\n' "$file"
}

resolve_lane_policy() {
    local file="$1"
    local harness="${2:-}"
    local normalized_file
    normalized_file=$(normalize_lane_policy_path "$file")
    local query_key="${normalized_file}|${harness}"
    if [[ "$LANE_POLICY_LAST_KEY" == "$query_key" ]]; then
        return 0
    fi

    local policy_result
    if ! policy_result=$("${AY_PYTHON_BIN:-python3}" "$LANE_POLICY_QUERY_SCRIPT" "$AY_LANE_POLICY_FILE" "$normalized_file" "$harness"); then
        echo -e "${RED}ERROR: invalid lane policy in ${AY_LANE_POLICY_FILE}${NC}" >&2
        return 1
    fi

    IFS=$'\t' read -r CURRENT_LANE CURRENT_LANE_UNWIND CURRENT_LANE_REASON CURRENT_LANE_ISSUE <<< "$policy_result"
    CURRENT_LANE="${CURRENT_LANE:-chc}"
    if [[ "$CURRENT_LANE" == "chc" ]]; then
        CURRENT_LANE_UNWIND=""
    elif [[ "$CURRENT_LANE" == "bmc" ]]; then
        if [[ ! "$CURRENT_LANE_UNWIND" =~ ^[1-9][0-9]*$ ]]; then
            echo -e "${RED}ERROR: lane policy requires positive unwind for bmc lane: ${normalized_file}${NC}" >&2
            return 1
        fi
    else
        echo -e "${RED}ERROR: unsupported lane '$CURRENT_LANE' for ${normalized_file}${NC}" >&2
        return 1
    fi

    LANE_POLICY_LAST_KEY="$query_key"
    return 0
}

prepare_lane_policy_flags() {
    local file="$1"
    local harness="$2"
    local file_flags="$3"
    if ! resolve_lane_policy "$file" "$harness"; then
        return 1
    fi

    LANE_POLICY_EXTRA_FLAGS=()
    if [[ "$CURRENT_LANE" == "chc" ]]; then
        LANE_POLICY_EXTRA_FLAGS+=("--ay-chc")
    elif [[ -n "$CURRENT_LANE_UNWIND" ]] && ! file_flags_specify_unwind "$file_flags"; then
        LANE_POLICY_EXTRA_FLAGS+=("--default-unwind" "$CURRENT_LANE_UNWIND")
    fi
    return 0
}

lane_policy_default_expectation() {
    local file="$1"
    local harness="${2:-}"
    if ! resolve_lane_policy "$file" "$harness"; then
        return 1
    fi
    if [[ "$CURRENT_LANE" == "chc" ]]; then
        echo "PROOF"
    else
        echo "BMC_SAFE"
    fi
}

lane_policy_verbose_note() {
    local file="$1"
    if [[ "$CURRENT_LANE" == "bmc" ]]; then
        echo "lane-policy: bmc (unwind=${CURRENT_LANE_UNWIND}) path=$(normalize_lane_policy_path "$file") issue=${CURRENT_LANE_ISSUE:-n/a}"
    else
        echo "lane-policy: chc path=$(normalize_lane_policy_path "$file") issue=${CURRENT_LANE_ISSUE:-n/a}"
    fi
}

run_lane_policy_self_tests() {
    local failures=0
    if ! file_flags_specify_unwind "--default-unwind 5"; then
        echo "self-test FAIL: did not detect --default-unwind"
        failures=1
    fi
    if ! file_flags_specify_unwind "--unwind=7"; then
        echo "self-test FAIL: did not detect --unwind=VALUE"
        failures=1
    fi
    if file_flags_specify_unwind "--harness-timeout=30"; then
        echo "self-test FAIL: false positive on --harness-timeout as unwind"
        failures=1
    fi

    local lane_policy_tmp
    lane_policy_tmp=$(mktemp "${TMPDIR:-/tmp}/lane_policy.XXXXXX")
    cat > "$lane_policy_tmp" <<'EOF'
version = 1

[[entry]]
path = "tests/ay/lane_probe.rs"
lane = "chc"
reason = "default lane"
issue = 1037

[[entry]]
path = "tests/ay/lane_probe.rs"
harness = "bounded_harness"
lane = "bmc"
unwind = 9
reason = "bounded candidate"
issue = 1037
EOF

    local saved_lane_policy_file="$AY_LANE_POLICY_FILE"
    AY_LANE_POLICY_FILE="$lane_policy_tmp"
    LANE_POLICY_LAST_KEY=""
    CURRENT_LANE=""
    CURRENT_LANE_UNWIND=""

    if ! resolve_lane_policy "$TRUST_MC_DIR/tests/ay/lane_probe.rs" "bounded_harness"; then
        echo "self-test FAIL: lane policy parse failed for bounded_harness"
        failures=1
    elif [[ "$CURRENT_LANE" != "bmc" ]]; then
        echo "self-test FAIL: lane policy should route bounded_harness to BMC (got $CURRENT_LANE)"
        failures=1
    fi
    if [[ "$CURRENT_LANE_UNWIND" != "9" ]]; then
        echo "self-test FAIL: lane policy unwind expected 9, got '$CURRENT_LANE_UNWIND'"
        failures=1
    fi
    if ! resolve_lane_policy "$TRUST_MC_DIR/tests/ay/lane_probe.rs" "unbounded_harness"; then
        echo "self-test FAIL: lane policy parse failed for unbounded_harness"
        failures=1
    elif [[ "$CURRENT_LANE" != "chc" ]]; then
        echo "self-test FAIL: lane policy should keep unbounded_harness on CHC (got $CURRENT_LANE)"
        failures=1
    fi

    rm -f "$lane_policy_tmp"
    AY_LANE_POLICY_FILE="$saved_lane_policy_file"
    LANE_POLICY_LAST_KEY=""
    CURRENT_LANE=""
    CURRENT_LANE_UNWIND=""
    return $failures
}
