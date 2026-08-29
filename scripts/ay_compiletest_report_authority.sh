#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Authority metadata helpers for ay_compiletest_reports.sh.

detect_report_tree_state() {
    local status_output
    if ! status_output="$(git -C "$TRUST_MC_DIR" status --porcelain=v1 --untracked-files=all 2>/dev/null)"; then
        echo "dirty"
        return 0
    fi

    if awk '
        {
            path = substr($0, 4)
            if (path ~ /^reports\//) {
                next
            }
            if (path ~ /\.rs$/ || path ~ /(^|\/)Cargo\.toml$/ || path ~ /(^|\/)Cargo\.lock$/ || path ~ /(^|\/)rust-toolchain\.toml$/) {
                found = 1
                exit 0
            }
            if (path ~ /^(scripts\/compiletest_report_contract\.py|scripts\/compiletest_report_paths\.py|scripts\/compiletest_proof_accounting\.py|scripts\/driver_binary_attestation\.py|scripts\/direct_driver_proof_core\.py|scripts\/direct_driver_proof_report\.py|scripts\/extract_proof_harnesses\.py|scripts\/extract_replacement_proof_report\.py|scripts\/generate_non_proof_closure\.py|scripts\/replacement_harness_dispositions\.py|scripts\/replacement_public_runner\.py|scripts\/lane_policy_query\.py|scripts\/ay-bump-canary\.sh|scripts\/ay-compiletest\.sh|scripts\/ay-replacement-proof\.sh|scripts\/ay-soundness-gate\.sh|scripts\/ay_compiletest_expectations\.sh|scripts\/ay_compiletest_lane_policy\.sh|scripts\/ay_compiletest_report_authority\.sh|scripts\/ay_compiletest_reports\.sh|scripts\/ay_compiletest_runner\.sh|scripts\/ay_manifest_pin\.py|scripts\/zero_fallback_canary\.sh|scripts\/zero_fallback_proof_gate\.py|tools\/replacement-inventory\/generate_inventory\.py|tools\/replacement-inventory\/public-corpus\.json|tests\/ay\/lane_policy\.toml|tests\/trust-mc\/non-proof-closure\.json|tests\/trust-mc\/replacement-harness-inventory\.json|tests\/trust-mc\/replacement-harness-inventory\.proof\.json|tests\/trust-mc\/replacement-harness-dispositions\.json)$/) {
                found = 1
                exit 0
            }
        }
        END {
            exit(found ? 0 : 1)
        }
    ' <<< "$status_output"; then
        echo "dirty"
    else
        echo "clean"
    fi
}

detect_report_tree_fingerprint() {
    local fingerprint
    fingerprint="$(
        git -C "$TRUST_MC_DIR" diff --no-ext-diff --binary HEAD -- \
            ':(glob)**/*.rs' \
            'Cargo.toml' \
            'Cargo.lock' \
            'rust-toolchain.toml' \
            ':(glob)**/Cargo.toml' \
            ':(glob)**/Cargo.lock' \
            ':(glob)**/rust-toolchain.toml' \
            'scripts/compiletest_report_contract.py' \
            'scripts/compiletest_report_paths.py' \
            'scripts/compiletest_proof_accounting.py' \
            'scripts/driver_binary_attestation.py' \
            'scripts/direct_driver_proof_core.py' \
            'scripts/direct_driver_proof_report.py' \
            'scripts/extract_proof_harnesses.py' \
            'scripts/extract_replacement_proof_report.py' \
            'scripts/generate_non_proof_closure.py' \
            'scripts/replacement_harness_dispositions.py' \
            'scripts/replacement_public_runner.py' \
            'scripts/lane_policy_query.py' \
            'scripts/ay-bump-canary.sh' \
            'scripts/ay-compiletest.sh' \
            'scripts/ay-replacement-proof.sh' \
            'scripts/ay-soundness-gate.sh' \
            'scripts/ay_compiletest_expectations.sh' \
            'scripts/ay_compiletest_lane_policy.sh' \
            'scripts/ay_compiletest_report_authority.sh' \
            'scripts/ay_compiletest_reports.sh' \
            'scripts/ay_compiletest_runner.sh' \
            'scripts/ay_manifest_pin.py' \
            'scripts/zero_fallback_canary.sh' \
            'scripts/zero_fallback_proof_gate.py' \
            'tools/replacement-inventory/generate_inventory.py' \
            'tools/replacement-inventory/public-corpus.json' \
            'tests/ay/lane_policy.toml' \
            'tests/trust-mc/non-proof-closure.json' \
            'tests/trust-mc/replacement-harness-inventory.json' \
            'tests/trust-mc/replacement-harness-inventory.proof.json' \
            'tests/trust-mc/replacement-harness-dispositions.json' \
            | shasum -a 256 | awk '{print $1}'
    )"
    printf '%s\n' "$fingerprint"
}

extract_solver_binary_commit_from_version() {
    local version_output="${1:-}"
    local commit
    commit=$(printf '%s\n' "$version_output" | sed -n 's/^build\.commit=\([0-9a-fA-F]\{7,40\}\).*$/\1/p' | head -n 1)
    if [[ -n "$commit" ]]; then
        printf '%s\n' "$commit"
        return 0
    fi
    printf '%s\n' "$version_output" | sed -n 's/.*[.+]\([0-9a-fA-F]\{7,40\}\)@.*/\1/p' | head -n 1
}

build_solver_binary_attestation_json() {
    local solver="$1"
    local solver_path="" solver_version="" solver_commit=""
    solver_path=$(command -v "$solver" 2>/dev/null || true)
    if [[ -n "$solver_path" && -x "$solver_path" ]]; then
        solver_version=$("$solver_path" --version 2>&1 || true)
        solver_commit=$(extract_solver_binary_commit_from_version "$solver_version")
    fi

    jq -cn \
        --arg name "$solver" \
        --arg path "$solver_path" \
        --arg version "$solver_version" \
        --arg commit "$solver_commit" '
        {name: $name}
        + (if $path != "" then {path: $path} else {} end)
        + (if $version != "" then {version: $version} else {} end)
        + (if $commit != "" then {commit: $commit} else {} end)
    '
}
