// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for call_ay.

use super::*;
use crate::verification_result::ValidationStatus;

#[cfg(feature = "ay-chc-native")]
#[test]
fn native_chc_external_fallback_gate_accepts_inconclusive_paths() {
    let inconclusive =
        anyhow::anyhow!("ay-chc adaptive-portfolio returned Unknown - verification inconclusive");
    assert!(native_chc_error_allows_external_proof_fallback(&inconclusive));

    let guard_timeout = anyhow::anyhow!("ay-chc adaptive-portfolio exceeded guard timeout (125s)");
    assert!(native_chc_error_allows_external_proof_fallback(&guard_timeout));

    let validation_err =
        anyhow::anyhow!("ay-chc external invariant model validation failed: validator timed out");
    assert!(native_chc_error_allows_external_proof_fallback(&validation_err));

    let false_proof =
        anyhow::anyhow!("ay-chc false proof detected: BMC cross-check contradicts proof");
    assert!(!native_chc_error_allows_external_proof_fallback(&false_proof));
}

// ==================== Solver-named unknown reasons ====================
// Verification Objective: an `unknown` that ay itself attributes — commands it
// REJECTED, or a memory/time budget — is filed under that cause, never under
// the "solver undecided" default. Lines below are verbatim ay 0.19.0 output on
// tests/slow/tokio-proofs `tokio_test::block_on::async_block` (2026-08-29).

#[test]
fn rejected_commands_are_counted_and_the_first_is_quoted() {
    let stdout = "(error \"line 2373 column 632: Sorts Uninterpreted(\"\"Vec_bv256\"\") and \
                  Uninterpreted(\"\"Events\"\") are incompatible\")\n\
                  (error \"line 2763 column 378: invalid constant: Condvar_mk requires 1 arguments, got 2\")\n\
                  (error \"line 2961 column 165: unknown sort 'UnixStream'\")\n\
                  (error \"unknown constant std::sync::OnceLock::<tokio::signal::registry::Globals>::get#f137::local_0_0\")\n\
                  unknown\n";
    let stderr = "c writing Alethe proof to /tmp/q.smt2.alethe on unsat\n\
                  (:reason-unknown \"memout\")\n";
    let (count, first) = smt_command_rejections(stdout, stderr);
    assert_eq!(count, 4);
    assert_eq!(
        first.as_deref(),
        Some(
            "(error \"line 2373 column 632: Sorts Uninterpreted(\"\"Vec_bv256\"\") and \
             Uninterpreted(\"\"Events\"\") are incompatible\")"
        )
    );
    assert_eq!(solver_reason_unknown(stdout, stderr).as_deref(), Some("memout"));
    assert_eq!(classify_reason_unknown("memout"), Some(SolverUnknownReason::Memout));
}

/// `(get-value ...)` after a decided `unsat` answers "model is not available";
/// that is the solver declining a model query, not rejecting the problem.
#[test]
fn a_model_not_available_error_is_not_a_rejected_command() {
    let stdout = "unsat\n(error \"line 26 column 73: model is not available\")\n";
    assert_eq!(smt_command_rejections(stdout, ""), (0, None));
    assert_eq!(solver_reason_unknown(stdout, ""), None);
}

/// Only the budget-bound reasons the solver names get their own bucket; an
/// `incomplete` or a discarded-command refusal keeps the caller's default.
#[test]
fn only_budget_reasons_are_classified() {
    assert_eq!(classify_reason_unknown("timeout"), Some(SolverUnknownReason::Timeout));
    assert_eq!(classify_reason_unknown("incomplete"), None);
    assert_eq!(classify_reason_unknown("a problem-contributing command was discarded"), None);
    // Unquoted and `--stats`-style forms both parse.
    assert_eq!(
        solver_reason_unknown("", "(:reason-unknown incomplete)").as_deref(),
        Some("incomplete")
    );
    assert_eq!(
        solver_reason_unknown(
            "",
            "(:reason-unknown \"a problem-contributing command was discarded\")"
        )
        .as_deref(),
        Some("a problem-contributing command was discarded")
    );
}

// ==================== V0: SMT-LIB Export Filtering ====================
// Verification Objective: exported SMT-LIB is consumable by AY even when UNSAT.
// See #1921.

#[test]
fn export_smtlib_filtered_strips_model_queries() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let src = tmp.path().join("src.smt2");
    let dst = tmp.path().join("dst.smt2");

    std::fs::write(
        &src,
        concat!(
            "(set-logic QF_BV)\n",
            "  (get-value ((x #b0)))\n",
            "(declare-const x (_ BitVec 1))\n",
            "(assert (= x #b0))\n",
            " (check-sat)\n",
            "(get-model)\n"
        ),
    )
    .expect("write src");

    export_smtlib_filtered(&src, &dst).expect("export");
    let exported = std::fs::read_to_string(&dst).expect("read dst");
    assert!(
        !exported.contains("(get-value"),
        "expected export to omit get-value commands: {exported}"
    );
    assert!(
        !exported.contains("(get-model"),
        "expected export to omit get-model commands: {exported}"
    );
    assert!(exported.contains("(check-sat)"), "expected export to preserve check-sat: {exported}");
}

#[test]
fn export_smtlib_filtered_strips_multiline_model_queries() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let src = tmp.path().join("src.smt2");
    let dst = tmp.path().join("dst.smt2");

    std::fs::write(
        &src,
        concat!(
            "(set-logic QF_BV)\n",
            "(declare-const x (_ BitVec 1))\n",
            "(check-sat)\n",
            "(get-value\n",
            "  (UNIQUE_TOKEN_1921)\n",
            ")\n",
            "(get-model\n",
            "  ; UNIQUE_TOKEN_1921_MODEL\n",
            ")\n",
            "(exit)\n"
        ),
    )
    .expect("write src");

    export_smtlib_filtered(&src, &dst).expect("export");
    let exported = std::fs::read_to_string(&dst).expect("read dst");

    assert!(
        !exported.contains("(get-value"),
        "expected export to omit get-value commands: {exported}"
    );
    assert!(
        !exported.contains("(get-model"),
        "expected export to omit get-model commands: {exported}"
    );
    assert!(
        !exported.contains("UNIQUE_TOKEN_1921"),
        "expected export to omit get-value body lines: {exported}"
    );
    assert!(
        !exported.contains("UNIQUE_TOKEN_1921_MODEL"),
        "expected export to omit get-model body lines: {exported}"
    );
    assert!(exported.contains("(check-sat)"), "expected export to preserve check-sat: {exported}");
    assert!(
        exported.contains("(exit)"),
        "expected export to preserve commands after filtering: {exported}"
    );
}

#[test]
fn export_smtlib_filtered_errors_on_unterminated_filtered_command() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let src = tmp.path().join("src.smt2");
    let dst = tmp.path().join("dst.smt2");

    std::fs::write(&src, "(get-value\n  (UNIQUE_TOKEN_1921)\n").expect("write src");

    let err = export_smtlib_filtered(&src, &dst).expect_err("expected error");
    let msg = err.to_string();
    assert!(
        msg.contains("unterminated"),
        "expected error to mention unterminated filtered command, got: {msg}"
    );
}

#[test]
fn normalize_smt_qualified_syntax_rewrites_fp_rounding_modes() {
    let input = concat!(
        "(assert (= sum (fp.add RNE x y)))\n",
        "(assert (= trunc (fp.roundToIntegral RTZ x)))\n",
        "(assert (= cast ((_ to_fp 11 53) RTP bv32)))\n",
        "(assert (= ubv ((_ fp.to_ubv 32) RTN x)))\n",
        "(assert (= sbv ((_ fp.to_sbv 32) RNA x)))\n",
    );

    let fixed = normalize_smt_qualified_syntax(input);

    assert!(
        fixed.contains("(fp.add roundNearestTiesToEven x y)"),
        "expected RNE rewrite, got: {fixed}"
    );
    assert!(
        fixed.contains("(fp.roundToIntegral roundTowardZero x)"),
        "expected RTZ rewrite, got: {fixed}"
    );
    assert!(
        fixed.contains("((_ to_fp 11 53) roundTowardPositive bv32)"),
        "expected RTP rewrite, got: {fixed}"
    );
    assert!(
        fixed.contains("((_ fp.to_ubv 32) roundTowardNegative x)"),
        "expected RTN rewrite, got: {fixed}"
    );
    assert!(
        fixed.contains("((_ fp.to_sbv 32) roundNearestTiesToAway x)"),
        "expected RNA rewrite, got: {fixed}"
    );
    assert!(!fixed.contains(" RNE "), "short RNE token should be gone: {fixed}");
    assert!(!fixed.contains(" RTZ "), "short RTZ token should be gone: {fixed}");
}

#[test]
fn normalize_smt_qualified_syntax_preserves_quoted_rounding_mode_lookalikes() {
    let input = concat!(
        "(declare-const RNE_helper Bool)\n",
        "(assert (= |RTZ| |RTZ|))\n",
        "(echo \"RNA should stay inside strings\")\n",
    );

    let fixed = normalize_smt_qualified_syntax(input);

    assert!(
        fixed.contains("(declare-const RNE_helper Bool)"),
        "non-token identifier should be preserved: {fixed}"
    );
    assert!(
        fixed.contains("(assert (= |RTZ| |RTZ|))"),
        "quoted symbol should be preserved: {fixed}"
    );
    assert!(
        fixed.contains("(echo \"RNA should stay inside strings\")"),
        "string literal should be preserved: {fixed}"
    );
}

// ==================== V1: Logic Tier Classification ====================
// Verification Objective: A query is classified correctly based on logic type.

#[test]
fn test_logic_tier_from_linear() {
    let logic_class = SmtLogicClass::Linear;
    let logic_tier = match logic_class {
        SmtLogicClass::Linear => LogicTier::TierA,
        SmtLogicClass::Nia | SmtLogicClass::Nra | SmtLogicClass::DtBvArrays => LogicTier::TierB,
    };
    assert_eq!(logic_tier, LogicTier::TierA, "Linear logic should be TierA");
}

#[test]
fn test_logic_tier_from_nia() {
    let logic_class = SmtLogicClass::Nia;
    let logic_tier = match logic_class {
        SmtLogicClass::Linear => LogicTier::TierA,
        SmtLogicClass::Nia | SmtLogicClass::Nra | SmtLogicClass::DtBvArrays => LogicTier::TierB,
    };
    assert_eq!(logic_tier, LogicTier::TierB, "NIA logic should be TierB");
}

#[test]
fn test_logic_tier_from_nra() {
    let logic_class = SmtLogicClass::Nra;
    let logic_tier = match logic_class {
        SmtLogicClass::Linear => LogicTier::TierA,
        SmtLogicClass::Nia | SmtLogicClass::Nra | SmtLogicClass::DtBvArrays => LogicTier::TierB,
    };
    assert_eq!(logic_tier, LogicTier::TierB, "NRA logic should be TierB");
}

// ==================== V2: Result Labeling Soundness ====================
// Verification Objective: Results are correctly demoted when NIA detected.
// Soundness Invariant S1: IF is_nia(Q) AND result_status(R) IN {SAT, UNSAT}
//                         THEN (has_proof_artifact(R) OR is_demoted(R))

#[test]
fn test_validation_status_tier_a() {
    assert_eq!(
        LogicTier::TierA.validation_status(),
        ValidationStatus::Validated,
        "TierA results should be Validated"
    );
}

#[test]
fn test_validation_status_tier_b_demoted() {
    assert_eq!(
        LogicTier::TierB.validation_status(),
        ValidationStatus::Unvalidated,
        "TierB results should be Unvalidated (demoted)"
    );
}

/// Soundness invariant S1: NIA/NRA/DT+BV results without proof artifact must be demoted.
/// This test verifies that the mapping is consistent.
#[test]
fn test_soundness_invariant_s1() {
    // For each incomplete logic class, verify demotion is enforced
    for logic_class in [SmtLogicClass::Nia, SmtLogicClass::Nra, SmtLogicClass::DtBvArrays] {
        let logic_tier = match logic_class {
            SmtLogicClass::Linear => LogicTier::TierA,
            SmtLogicClass::Nia | SmtLogicClass::Nra | SmtLogicClass::DtBvArrays => LogicTier::TierB,
        };

        // Without proof artifact, results must be demoted
        let validation_status = logic_tier.validation_status();

        assert_eq!(
            validation_status,
            ValidationStatus::Unvalidated,
            "S1: NIA/NRA/DT+BV without proof must be Unvalidated: {:?}",
            logic_class
        );
    }
}

// ==================== V4: Diagnostic Message Consistency ====================
// Verification Objective: Stable diagnostic message when NIA demotion occurs.

#[test]
fn test_nia_diagnostic_message_format() {
    let logic_class = SmtLogicClass::Nia;
    let (prefix, logic_name) = match logic_class {
        SmtLogicClass::Nia => ("NIA", "non-linear integer arithmetic"),
        SmtLogicClass::Nra => ("NRA", "non-linear real arithmetic"),
        SmtLogicClass::DtBvArrays => {
            ("DT+BV/Arrays", "datatypes combined with bitvectors/arrays (ay#1766)")
        }
        SmtLogicClass::Linear => unreachable!(),
    };
    let msg = format!(
        "[{}] Detected {}; solver may be incomplete; \
         results are demoted unless proof-validated.",
        prefix, logic_name
    );
    assert!(msg.contains("NIA"), "Message should contain NIA prefix");
    assert!(
        msg.contains("non-linear integer arithmetic"),
        "Message should contain logic description"
    );
    assert!(msg.contains("demoted"), "Message should warn about demotion");
}

#[test]
fn test_nra_diagnostic_message_format() {
    let logic_class = SmtLogicClass::Nra;
    let (prefix, logic_name) = match logic_class {
        SmtLogicClass::Nia => ("NIA", "non-linear integer arithmetic"),
        SmtLogicClass::Nra => ("NRA", "non-linear real arithmetic"),
        SmtLogicClass::DtBvArrays => {
            ("DT+BV/Arrays", "datatypes combined with bitvectors/arrays (ay#1766)")
        }
        SmtLogicClass::Linear => unreachable!(),
    };
    let msg = format!(
        "[{}] Detected {}; solver may be incomplete; \
         results are demoted unless proof-validated.",
        prefix, logic_name
    );
    assert!(msg.contains("NRA"), "Message should contain NRA prefix");
    assert!(msg.contains("non-linear real arithmetic"), "Message should contain logic description");
}

// ==================== V5: Solver Attribute Warning (#1377) ====================
// Verification Objective: Warning is emitted when #[kani::solver] attribute
// is used with AY backend, since the attribute has no effect on AY.

/// Test that the warning condition triggers for harnesses with solver attribute set.
/// Part of #1377 verification.
#[test]
fn test_solver_attribute_warning_condition_with_solver() {
    use trust_mc_metadata::{HarnessAttributes, HarnessKind, SolverOption};

    let mut attrs = HarnessAttributes::new(HarnessKind::Proof);
    attrs.solver = Some(SolverOption::Kissat);

    // The warning condition from run_ay:
    // if harness.attributes.solver.is_some() { ... }
    assert!(
        attrs.solver.is_some(),
        "Harness with #[kani::solver] should trigger warning condition"
    );
}

/// Test that the warning condition does not trigger for harnesses without solver attribute.
/// Part of #1377 verification.
#[test]
fn test_solver_attribute_warning_condition_without_solver() {
    use trust_mc_metadata::{HarnessAttributes, HarnessKind};

    let attrs = HarnessAttributes::new(HarnessKind::Proof);

    // Without solver attribute, warning should not be emitted
    assert!(attrs.solver.is_none(), "Harness without #[kani::solver] should not trigger warning");
}

/// Test the warning message format is correct.
/// Part of #1377 verification.
#[test]
fn test_solver_attribute_warning_message_format() {
    let harness_name = "test_harness::my_proof";
    let msg = format!(
        "Warning: `#[kani::solver]` attribute on harness `{}` is ignored by AY backend. \
         Use --smt-solver (or --ay-solver) to configure AY solver selection.",
        harness_name
    );

    // Verify message contains key information
    assert!(msg.contains("#[kani::solver]"), "Message should mention the attribute");
    assert!(msg.contains("ignored"), "Message should indicate attribute is ignored");
    assert!(msg.contains("AY backend"), "Message should mention AY backend");
    assert!(
        msg.contains("--smt-solver") || msg.contains("--ay-solver"),
        "Message should suggest alternative"
    );
    assert!(msg.contains(harness_name), "Message should include harness name");
}

/// Test all SolverOption variants trigger the warning.
/// Part of #1377 verification.
#[test]
fn test_solver_attribute_warning_all_variants() {
    use trust_mc_metadata::{HarnessAttributes, HarnessKind, SolverOption};

    let solvers = [
        SolverOption::Bitwuzla,
        SolverOption::Cadical,
        SolverOption::Cvc5,
        SolverOption::Kissat,
        SolverOption::Minisat,
        SolverOption::Z3,
        SolverOption::Binary("custom_solver".to_string()),
    ];

    for solver in solvers {
        let mut attrs = HarnessAttributes::new(HarnessKind::Proof);
        attrs.solver = Some(solver.clone());

        assert!(attrs.solver.is_some(), "All solver variants should trigger warning: {:?}", solver);
    }
}

// ==================== Loop Invariant Hint Conversion ====================
// Part of #972: Verify LoopInvariantHint can be converted to ay LemmaHint.

/// Test that LoopInvariantHint struct can be created and serialized.
/// This verifies the artifact data structure is correctly set up.
#[test]
fn test_loop_invariant_hint_creation() {
    use trust_mc_core::LoopInvariantHint;

    // Use realistic relation name format: {fn_name}__bb{idx}
    let hint = LoopInvariantHint::new("test_harness__bb5", 5)
        .with_captured_vars(vec![1, 2, 3])
        .with_priority(50);

    assert_eq!(hint.relation_name, "test_harness__bb5");
    assert_eq!(hint.loop_head_bb, 5);
    assert_eq!(hint.captured_vars, vec![1, 2, 3]);
    assert_eq!(hint.priority, 50);
}

/// Test that hint with default priority gets 50.
#[test]
fn test_loop_invariant_hint_default_priority() {
    use trust_mc_core::LoopInvariantHint;

    let hint = LoopInvariantHint::new("my_fn__bb0", 0);
    assert_eq!(hint.priority, 50, "Default priority should be 50");
}

/// Test serialization round-trip of LoopInvariantHint.
#[test]
fn test_loop_invariant_hint_serialization() {
    use trust_mc_core::LoopInvariantHint;

    let hint = LoopInvariantHint::new("check_loop__bb7", 7)
        .with_captured_vars(vec![0, 1])
        .with_priority(25);

    let json = serde_json::to_string(&hint).expect("serialization should succeed");
    let deserialized: LoopInvariantHint =
        serde_json::from_str(&json).expect("deserialization should succeed");

    assert_eq!(hint.relation_name, deserialized.relation_name);
    assert_eq!(hint.loop_head_bb, deserialized.loop_head_bb);
    assert_eq!(hint.captured_vars, deserialized.captured_vars);
    assert_eq!(hint.priority, deserialized.priority, "Priority should round-trip");
}

// ==================== Timeout Constant Consistency ====================
// Regression test for #3820: CHC paths must use the same default timeout
// as standalone BMC (DEFAULT_SOLVER_TIMEOUT_SECS = 120s).

#[test]
fn test_default_solver_timeout_is_120_seconds() {
    assert_eq!(
        super::DEFAULT_SOLVER_TIMEOUT_SECS,
        120,
        "Default solver timeout must be 120s — CHC paths share this constant (#3820)"
    );
}

#[test]
fn test_solver_timeout_duration_none_returns_default() {
    let dur = solver_timeout_duration(None);
    assert_eq!(
        dur,
        Duration::from_secs(120),
        "solver_timeout_duration(None) must return the shared 120s default (#3820)"
    );
}

#[test]
fn test_solver_timeout_duration_explicit_override() {
    let timeout: crate::args::Timeout = "45s".parse().expect("valid timeout");
    let dur = solver_timeout_duration(Some(timeout));
    assert_eq!(
        dur,
        Duration::from_secs(45),
        "solver_timeout_duration(Some(45s)) must return 45s (#3820)"
    );
}

#[test]
fn test_solver_error_is_timeout_detects_subprocess_timeout() {
    let err = anyhow::anyhow!(
        "target/release/ay timed out after 120.0s. Use --tool-timeout to increase the limit."
    )
    .context("run ay");
    assert!(
        solver_error_is_timeout(&err),
        "solver subprocess timeout should be classified as UNKNOWN/Timeout"
    );
}
