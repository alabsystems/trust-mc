# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

REPORT_TOOL_PATHS = (
    "scripts/compiletest_report_contract.py",
    "scripts/compiletest_report_paths.py",
    "scripts/compiletest_proof_accounting.py",
    "scripts/driver_binary_attestation.py",
    "scripts/direct_driver_proof_core.py",
    "scripts/direct_driver_proof_report.py",
    "scripts/extract_proof_harnesses.py",
    "scripts/extract_replacement_proof_report.py",
    "scripts/generate_non_proof_closure.py",
    "scripts/replacement_harness_dispositions.py",
    "scripts/replacement_public_runner.py",
    "scripts/lane_policy_query.py",
    "scripts/ay-bump-canary.sh",
    "scripts/ay-compiletest.sh",
    "scripts/ay-replacement-proof.sh",
    "scripts/ay-soundness-gate.sh",
    "scripts/ay_compiletest_expectations.sh",
    "scripts/ay_compiletest_lane_policy.sh",
    "scripts/ay_compiletest_report_authority.sh",
    "scripts/ay_compiletest_reports.sh",
    "scripts/ay_compiletest_runner.sh",
    "scripts/ay_manifest_pin.py",
    "scripts/zero_fallback_canary.sh",
    "scripts/zero_fallback_proof_gate.py",
    "tools/replacement-inventory/generate_inventory.py",
    "tools/replacement-inventory/public-corpus.json",
    "tests/ay/lane_policy.toml",
    "tests/trust-mc/non-proof-closure.json",
    "tests/trust-mc/replacement-harness-inventory.json",
    "tests/trust-mc/replacement-harness-inventory.proof.json",
    "tests/trust-mc/replacement-harness-dispositions.json",
)
MEASUREMENT_FINGERPRINT_PATHS = (
    ":(glob)**/*.rs",
    "Cargo.toml",
    "Cargo.lock",
    "rust-toolchain.toml",
    ":(glob)**/Cargo.toml",
    ":(glob)**/Cargo.lock",
    ":(glob)**/rust-toolchain.toml",
    *REPORT_TOOL_PATHS,
)
