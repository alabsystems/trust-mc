// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::integration_bmc_tests::BMC_E2E_CASES;
use super::integration_chc_tests::CHC_E2E_CASES;

// Canonical smoke baseline (clean-tree reference in reports/compiletest-prover-p612-20260211.log):
// 201 PROOF out of 330 harnesses.
const SMOKE_PROOF_BASELINE_NUMERATOR: usize = 201;
const SMOKE_PROOF_BASELINE_DENOMINATOR: usize = 330;

#[test]
fn test_e2e_verdict_baseline_guard_matches_smoke_proof_floor() {
    let chc_proofs = CHC_E2E_CASES.iter().filter(|(_, _, expected)| *expected == "unsat").count();
    let bmc_proofs = BMC_E2E_CASES.iter().filter(|(_, _, expected)| *expected == "unsat").count();
    let proof_cases = chc_proofs + bmc_proofs;
    let total_cases = CHC_E2E_CASES.len() + BMC_E2E_CASES.len();

    assert_eq!(proof_cases, 14, "unexpected e2e proof-case count drift");
    assert_eq!(total_cases, 22, "unexpected e2e case-count drift");
    assert!(
        proof_cases * SMOKE_PROOF_BASELINE_DENOMINATOR
            >= total_cases * SMOKE_PROOF_BASELINE_NUMERATOR,
        "e2e proof floor regressed below smoke baseline ratio {}/{} (proof_cases={proof_cases}, total_cases={total_cases})",
        SMOKE_PROOF_BASELINE_NUMERATOR,
        SMOKE_PROOF_BASELINE_DENOMINATOR
    );
}
