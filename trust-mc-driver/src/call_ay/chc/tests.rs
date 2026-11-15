// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::TRIVIAL_SAFE_NO_ERROR_RULE_QUALIFIER;
use super::smt_analysis::smt_has_recursive_unwind_assertion;
use super::verdict_policy::{
    ChcOutcomeKind, apply_recursion_unwind_verdict, classify_chc_outcome, recursion_unwind_property,
};

#[cfg(feature = "ay-chc-native")]
use super::dedup_lemma_hints;
#[cfg(feature = "ay-chc-native")]
use super::native::{
    NativeSolveMode, guard_timeout_within_deadline, native_bmc_per_depth_timeout,
    scalar_acyclic_bmc_counterexample_is_trusted, select_native_solve_mode,
};
#[cfg(feature = "ay-chc-native")]
use crate::args::AYChcEngine;
use crate::property_model::CheckStatus;
use crate::verification_result::{FailedProperties, VerificationStatus};

#[test]
fn classify_chc_outcome_success_is_proof() {
    assert_eq!(
        classify_chc_outcome(false, VerificationStatus::Success, FailedProperties::None),
        ChcOutcomeKind::Proof
    );
}

#[test]
fn classify_chc_outcome_solver_unknown_preserves_solver_unknown() {
    assert_eq!(
        classify_chc_outcome(true, VerificationStatus::Failure, FailedProperties::Other),
        ChcOutcomeKind::SolverUnknown
    );
}

#[test]
fn classify_chc_outcome_crosscheck_fail_closed_is_conservative_unknown() {
    assert_eq!(
        classify_chc_outcome(false, VerificationStatus::Failure, FailedProperties::Other),
        ChcOutcomeKind::ConservativeUnknown
    );
}

#[test]
fn classify_chc_outcome_panics_only_is_counterexample() {
    assert_eq!(
        classify_chc_outcome(false, VerificationStatus::Failure, FailedProperties::PanicsOnly),
        ChcOutcomeKind::Counterexample
    );
}

#[test]
fn trivial_safe_no_error_rule_qualifier_is_stable() {
    assert_eq!(TRIVIAL_SAFE_NO_ERROR_RULE_QUALIFIER, "trivial_safe=no_error_rule");
}

/// A per-test scratch directory holding `<name>.smt2` beside its `.vc.json`.
fn lost_rules_fixture(
    name: &str,
    kinds: &[(u32, trust_mc_core::violation::PropertyKind, &str)],
) -> std::path::PathBuf {
    let dir = std::env::temp_dir()
        .join(format!("trust-mc-lost-error-rules-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let smt = dir.join(format!("{name}.smt2"));
    std::fs::write(&smt, "(declare-rel error ())\n(query error)\n").expect("smt");
    let mut artifact =
        trust_mc_core::artifact::VcArtifact::new(trust_mc_core::ident::HarnessId::new(name, name));
    for (id, kind, var) in kinds {
        artifact.properties.push(
            trust_mc_core::artifact::PropertyMetadata::new(
                trust_mc_core::ident::PropertyId::new(*id),
                *kind,
            )
            .with_message(format!("check {id}"))
            .with_smt_var(*var),
        );
    }
    let artifact_path = crate::ay_parse::vc_artifact_path_for_smt(&smt);
    std::fs::write(&artifact_path, serde_json::to_string(&artifact).expect("serialize"))
        .expect("artifact");
    smt
}

/// Registered checks with no error derivation are LOST checks: the gate must
/// fire for any checked obligation, and for an artifact nobody can read.
#[test]
fn lost_error_rules_gate_fires_on_registered_checks_and_missing_artifacts() {
    use crate::ay_parse::vc_artifact::artifact_may_register_checked_obligations as registers;
    use trust_mc_core::violation::PropertyKind;
    let checked = lost_rules_fixture(
        "checked",
        &[
            (0, PropertyKind::Assertion, "error_p0"),
            (1, PropertyKind::ArithmeticOverflow, "error_p1"),
        ],
    );
    assert!(registers(&crate::ay_parse::vc_artifact_path_for_smt(&checked)));

    // Nothing registered: the no-checks gate owns this shape, not LostErrorRules.
    let empty = lost_rules_fixture("empty", &[]);
    assert!(!registers(&crate::ay_parse::vc_artifact_path_for_smt(&empty)));

    // Covers never own an error rule, so a cover-only harness is not lost checks.
    let cover_only = lost_rules_fixture("cover_only", &[(0, PropertyKind::Cover, "ay_cover_0")]);
    assert!(!registers(&crate::ay_parse::vc_artifact_path_for_smt(&cover_only)));

    // Fail closed: a missing or unparseable artifact proves nothing was empty.
    let dir = checked.parent().expect("dir");
    assert!(registers(&dir.join("does-not-exist.vc.json")));
    let garbage = dir.join("garbage.vc.json");
    std::fs::write(&garbage, "{not json").expect("garbage");
    assert!(registers(&garbage));
}

/// The fail-closed result: never SUCCESS, never a proof qualifier, every
/// registered check UNDETERMINED, typed reason `LostErrorRules`.
#[cfg(feature = "ay-chc-native")]
#[test]
fn lost_error_rules_result_is_inconclusive_with_typed_reason() {
    use crate::verification_provenance::SolverUnknownReason;
    use trust_mc_core::violation::PropertyKind;
    let smt = lost_rules_fixture(
        "result",
        &[
            (0, PropertyKind::Assertion, "error_p0"),
            (1, PropertyKind::UndefinedBehavior, "error_p1"),
        ],
    );
    let harness = crate::test_support::test_harness("check_offset_from_same_dangling", "crate");
    let result = super::native_result::lost_error_rules_result(
        &smt,
        "(declare-rel error ())\n(query error)\n",
        &harness,
    );
    assert_eq!(result.status, VerificationStatus::Failure);
    assert!(matches!(result.failed_properties, FailedProperties::Other));
    assert_eq!(result.solver_unknown_reason, Some(SolverUnknownReason::LostErrorRules));
    assert!(result.proof_qualifiers.is_empty(), "no proof qualifier on a non-proof");
    assert_eq!(result.properties.len(), 2);
    assert!(result.properties.iter().all(|p| p.status == CheckStatus::Undetermined));
    assert!(!crate::verification_result::has_decided_check(&result.properties));

    // Without a per-property table the aggregate line is UNDETERMINED too.
    let bare = lost_rules_fixture("bare", &[(0, PropertyKind::Assertion, "ay_violation_0")]);
    let result = super::native_result::lost_error_rules_result(&bare, "(query error)", &harness);
    assert_eq!(result.properties.len(), 1);
    assert_eq!(result.properties[0].status, CheckStatus::Undetermined);
    assert_eq!(result.solver_unknown_reason, Some(SolverUnknownReason::LostErrorRules));
}

#[cfg(feature = "ay-chc-native")]
#[test]
fn native_solve_mode_uses_adaptive_only_for_auto_with_retry() {
    assert_eq!(
        select_native_solve_mode(AYChcEngine::Auto, false),
        NativeSolveMode::AdaptivePortfolio
    );
}

#[cfg(feature = "ay-chc-native")]
#[test]
fn native_solve_mode_maps_no_retry_to_primary_engine_only() {
    assert_eq!(
        select_native_solve_mode(AYChcEngine::Auto, true),
        NativeSolveMode::PrimaryEngineOnly
    );
}

#[cfg(feature = "ay-chc-native")]
#[test]
fn native_solve_mode_honors_explicit_engine_selection() {
    assert_eq!(
        select_native_solve_mode(AYChcEngine::Pdr, false),
        NativeSolveMode::PrimaryEngineOnly
    );
    assert_eq!(
        select_native_solve_mode(AYChcEngine::Pdr, true),
        NativeSolveMode::PrimaryEngineOnly
    );
    assert_eq!(select_native_solve_mode(AYChcEngine::Bmc, false), NativeSolveMode::BmcOnly);
    assert_eq!(select_native_solve_mode(AYChcEngine::Bmc, true), NativeSolveMode::BmcOnly);
}

#[cfg(feature = "ay-chc-native")]
#[test]
fn native_bmc_per_depth_timeout_caps_long_harness_budgets() {
    assert_eq!(
        native_bmc_per_depth_timeout(std::time::Duration::from_secs(120)),
        std::time::Duration::from_secs(10),
        "native BMC must not let one depth consume the whole harness budget"
    );
}

#[cfg(feature = "ay-chc-native")]
#[test]
fn native_bmc_per_depth_timeout_scales_short_harness_budgets() {
    assert_eq!(
        native_bmc_per_depth_timeout(std::time::Duration::from_secs(4)),
        std::time::Duration::from_secs(1)
    );
    assert_eq!(
        native_bmc_per_depth_timeout(std::time::Duration::from_millis(500)),
        std::time::Duration::from_millis(500)
    );
    assert_eq!(
        native_bmc_per_depth_timeout(std::time::Duration::ZERO),
        std::time::Duration::from_millis(1)
    );
}

#[cfg(feature = "ay-chc-native")]
#[test]
fn scalar_acyclic_bmc_counterexample_trust_requires_scalar_exact_problem() {
    let scalar = ay::chc::ChcParser::parse(
        r#"
(set-logic HORN)
(declare-rel start ((_ BitVec 8)))
(declare-rel error ())
(declare-var x (_ BitVec 8))
(rule (start #x08))
(rule (=> (start x) error))
(query error)
"#,
    )
    .expect("scalar CHC parses");
    assert!(scalar_acyclic_bmc_counterexample_is_trusted(&scalar, 0));
    assert!(!scalar_acyclic_bmc_counterexample_is_trusted(&scalar, 1));

    let array = ay::chc::ChcParser::parse(
        r#"
(set-logic HORN)
(declare-rel start ((Array (_ BitVec 8) (_ BitVec 8))))
(declare-rel error ())
(declare-var a (Array (_ BitVec 8) (_ BitVec 8)))
(rule (=> (start a) error))
(query error)
"#,
    )
    .expect("array CHC parses");
    assert!(!scalar_acyclic_bmc_counterexample_is_trusted(&array, 0));
}

/// C4: User hints placed first in the merged vector are preserved by dedup;
/// auto-generated duplicates are dropped.
#[cfg(feature = "ay-chc-native")]
#[test]
fn dedup_preserves_user_hint_over_auto_duplicate() {
    use ay::chc::{ChcExpr, ChcSort, ChcVar, LemmaHint, PredicateId};

    let pred = PredicateId::new(0);
    let formula = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("__p0_a0".to_string(), ChcSort::Int)),
        ChcExpr::int(0),
    );

    let user_hint = LemmaHint::new(pred, formula.clone(), 10, "trust_mc-loop-hint");
    let auto_hint = LemmaHint::new(pred, formula, 58, "trust_mc-auto-inv-houdini-seed");

    // User hint first (as in the real merge path: user hints then auto hints).
    let merged = vec![user_hint, auto_hint];
    let (deduped, dropped) = dedup_lemma_hints(merged);

    assert_eq!(deduped.len(), 1, "duplicate should be removed");
    assert_eq!(dropped, 1, "one duplicate should be counted");
    assert_eq!(
        deduped[0].source, "trust_mc-loop-hint",
        "user hint (first in order) should survive dedup, not auto hint"
    );
    assert_eq!(deduped[0].priority, 10, "user hint priority should be preserved");
}

/// C4: When no duplicates exist, all hints pass through.
#[cfg(feature = "ay-chc-native")]
#[test]
fn dedup_preserves_distinct_hints() {
    use ay::chc::{ChcExpr, ChcSort, ChcVar, LemmaHint, PredicateId};

    let pred = PredicateId::new(0);
    let formula_a = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("__p0_a0".to_string(), ChcSort::Int)),
        ChcExpr::int(0),
    );
    let formula_b = ChcExpr::le(
        ChcExpr::var(ChcVar::new("__p0_a0".to_string(), ChcSort::Int)),
        ChcExpr::var(ChcVar::new("__p0_a1".to_string(), ChcSort::Int)),
    );

    let hint_a = LemmaHint::new(pred, formula_a, 10, "trust_mc-loop-hint");
    let hint_b = LemmaHint::new(pred, formula_b, 58, "trust_mc-auto-inv-houdini-seed");

    let merged = vec![hint_a, hint_b];
    let (deduped, dropped) = dedup_lemma_hints(merged);

    assert_eq!(deduped.len(), 2, "distinct hints should both survive");
    assert_eq!(dropped, 0, "no duplicates to drop");
    assert_eq!(deduped[0].source, "trust_mc-loop-hint", "order should be preserved");
    assert_eq!(deduped[1].source, "trust_mc-auto-inv-houdini-seed", "order should be preserved");
}

/// C4: Dedup across different predicates - same formula on different
/// predicates should NOT be deduplicated.
#[cfg(feature = "ay-chc-native")]
#[test]
fn dedup_does_not_collapse_across_predicates() {
    use ay::chc::{ChcExpr, ChcSort, ChcVar, LemmaHint, PredicateId};

    let pred_a = PredicateId::new(0);
    let pred_b = PredicateId::new(1);
    let formula = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("__p0_a0".to_string(), ChcSort::Int)),
        ChcExpr::int(0),
    );

    let hint_a = LemmaHint::new(pred_a, formula.clone(), 10, "trust_mc-loop-hint");
    let hint_b = LemmaHint::new(pred_b, formula, 58, "trust_mc-auto-inv-houdini-seed");

    let merged = vec![hint_a, hint_b];
    let (deduped, dropped) = dedup_lemma_hints(merged);

    assert_eq!(deduped.len(), 2, "same formula on different predicates should not dedup");
    assert_eq!(dropped, 0);
}

// --- #4058 D4: recursive unwind assertion marker detection ---

#[test]
fn recursive_unwind_assertion_marker_detected() {
    let smt = "\
(set-logic HORN)
(declare-rel error ())
(query error)
; RECURSIVE_UNWIND_ASSERTION: chc_recursive_unwind
";
    assert!(
        smt_has_recursive_unwind_assertion(smt),
        "should detect RECURSIVE_UNWIND_ASSERTION marker"
    );
}

#[test]
fn recursive_unwind_assertion_symbol_detected() {
    let smt = "\
(set-logic HORN)
(declare-fun __assert_fail_inline_recursive_unwind_42 () (_ BitVec 32))
(declare-rel error ())
(query error)
";
    assert!(
        smt_has_recursive_unwind_assertion(smt),
        "should detect recursive unwind fallback symbols even without the explicit marker"
    );
}

#[test]
fn recursive_unwind_assertion_marker_absent() {
    let smt = "\
(set-logic HORN)
(declare-rel error ())
(query error)
";
    assert!(
        !smt_has_recursive_unwind_assertion(smt),
        "clean SMT should not trigger recursive unwind detection"
    );
}

// --- #4058 D4: recursion_unwind_property construction ---

#[test]
fn recursive_unwind_property_with_harness_name() {
    let prop = recursion_unwind_property(Some("check_recursive_sum_bounded"));
    assert_eq!(prop.description.as_ref(), "recursion unwinding assertion");
    assert_eq!(prop.property_id.class.as_ref(), "recursion");
    assert_eq!(prop.property_id.id, 1);
    assert_eq!(prop.property_id.fn_name.as_deref(), Some("check_recursive_sum_bounded"));
    assert_eq!(prop.status, CheckStatus::Failure);
}

#[test]
fn recursive_unwind_property_without_harness_name() {
    let prop = recursion_unwind_property(None);
    assert_eq!(prop.description.as_ref(), "recursion unwinding assertion");
    assert_eq!(prop.property_id.class.as_ref(), "recursion");
    assert!(prop.property_id.fn_name.is_none());
}

// --- #4058: apply_recursion_unwind_verdict ---

#[test]
fn recursive_unwind_verdict_on_ctrex_with_marker() {
    let generic = vec![crate::property_model::Property {
        description: std::borrow::Cow::Borrowed("CHC verification: error reachable"),
        property_id: crate::property_model::PropertyId {
            fn_name: None,
            class: std::borrow::Cow::Borrowed("chc"),
            id: 0,
        },
        source_location: crate::property_model::RawSourceLocation {
            column: None,
            file: None,
            function: None,
            line: None,
        },
        status: CheckStatus::Failure,
        trace: None,
    }];
    let (status, failed, result, outcome) = apply_recursion_unwind_verdict(
        true,
        ChcOutcomeKind::Counterexample,
        VerificationStatus::Failure,
        FailedProperties::PanicsOnly,
        generic,
        Some("check_recursive_sum"),
    );
    assert_eq!(status, VerificationStatus::Failure);
    assert!(matches!(failed, FailedProperties::Other));
    assert_eq!(outcome, ChcOutcomeKind::Counterexample);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].description.as_ref(), "recursion unwinding assertion");
    assert_eq!(result[0].property_id.class.as_ref(), "recursion");
    assert_eq!(result[0].property_id.fn_name.as_deref(), Some("check_recursive_sum"));
}

#[test]
fn recursive_unwind_verdict_forces_failure_on_proof_with_marker() {
    let generic = vec![crate::property_model::Property {
        description: std::borrow::Cow::Borrowed("CHC verification: property proven"),
        property_id: crate::property_model::PropertyId {
            fn_name: None,
            class: std::borrow::Cow::Borrowed("chc"),
            id: 0,
        },
        source_location: crate::property_model::RawSourceLocation {
            column: None,
            file: None,
            function: None,
            line: None,
        },
        status: CheckStatus::Success,
        trace: None,
    }];
    let (status, failed, result, outcome) = apply_recursion_unwind_verdict(
        true,
        ChcOutcomeKind::Proof,
        VerificationStatus::Success,
        FailedProperties::None,
        generic,
        Some("check_recursive_sum"),
    );
    assert_eq!(status, VerificationStatus::Failure);
    assert!(matches!(failed, FailedProperties::Other));
    assert_eq!(outcome, ChcOutcomeKind::Counterexample);
    assert_eq!(result.len(), 1);
    assert_eq!(
        result[0].property_id.class.as_ref(),
        "recursion",
        "recursive unwind markers must fail closed even if the backend reports PROOF"
    );
}

#[test]
fn recursive_unwind_verdict_passthrough_without_marker() {
    let generic = vec![crate::property_model::Property {
        description: std::borrow::Cow::Borrowed("CHC verification: error reachable"),
        property_id: crate::property_model::PropertyId {
            fn_name: None,
            class: std::borrow::Cow::Borrowed("chc"),
            id: 0,
        },
        source_location: crate::property_model::RawSourceLocation {
            column: None,
            file: None,
            function: None,
            line: None,
        },
        status: CheckStatus::Failure,
        trace: None,
    }];
    let (status, failed, result, outcome) = apply_recursion_unwind_verdict(
        false,
        ChcOutcomeKind::Counterexample,
        VerificationStatus::Failure,
        FailedProperties::PanicsOnly,
        generic,
        Some("check_recursive_sum"),
    );
    assert_eq!(status, VerificationStatus::Failure);
    assert!(matches!(failed, FailedProperties::PanicsOnly));
    assert_eq!(outcome, ChcOutcomeKind::Counterexample);
    assert_eq!(result.len(), 1);
    assert_eq!(
        result[0].property_id.class.as_ref(),
        "chc",
        "without marker, CTREX should not be relabeled"
    );
}

#[test]
fn recursive_unwind_verdict_on_solver_unknown_with_marker() {
    let generic = vec![crate::property_model::Property {
        description: std::borrow::Cow::Borrowed("CHC verification: inconclusive"),
        property_id: crate::property_model::PropertyId {
            fn_name: None,
            class: std::borrow::Cow::Borrowed("chc"),
            id: 0,
        },
        source_location: crate::property_model::RawSourceLocation {
            column: None,
            file: None,
            function: None,
            line: None,
        },
        status: CheckStatus::Undetermined,
        trace: None,
    }];
    let (status, failed, result, outcome) = apply_recursion_unwind_verdict(
        true,
        ChcOutcomeKind::SolverUnknown,
        VerificationStatus::Failure,
        FailedProperties::Other,
        generic,
        None,
    );
    assert_eq!(status, VerificationStatus::Failure);
    assert!(matches!(failed, FailedProperties::Other));
    assert_eq!(outcome, ChcOutcomeKind::Counterexample);
    assert_eq!(result.len(), 1);
    assert_eq!(
        result[0].description.as_ref(),
        "recursion unwinding assertion",
        "SolverUnknown with marker should relabel to recursion failure"
    );
    assert!(
        result[0].property_id.fn_name.is_none(),
        "no harness name provided, fn_name should be None"
    );
}

/// Validates the trust_mc-side model verification cross-check for ay-chc false proof
/// bug (ay#8578).
///
/// The CHC encodes: let a: u8 = kani::any(); kani::assert(a == 0u8, "always zero");
/// Since a is unconstrained BV8, a=1 is a trivial counterexample.
///
/// ay-chc AdaptivePortfolio has a known bug where PDR's `individually_inductive`
/// validation bypass can accept wrong invariants, returning Safe (false proof).
/// This test verifies that full model verification in a fresh PDR solver catches
/// the false proof by detecting the clause failure that the bypass skips.
#[cfg(feature = "ay-chc-native")]
#[test]
fn test_ay_chc_false_proof_model_verification_crosscheck() {
    use ay::chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, PdrConfig, engines};
    use std::time::Duration;

    let smt_content = "\
(set-logic HORN)
(declare-var _main_0 Bool)
(declare-var _main_0__out Bool)
(declare-var _main_1 (_ BitVec 8))
(declare-var _main_1__out (_ BitVec 8))
(declare-var _main_2 Bool)
(declare-var _main_2__out Bool)
(declare-var _main_3 Bool)
(declare-var _main_3__out Bool)
(declare-var obj_valid (Array (_ BitVec 32) Bool))
(declare-var obj_valid__out (Array (_ BitVec 32) Bool))
(declare-var obj_size (Array (_ BitVec 32) (_ BitVec 32)))
(declare-var obj_size__out (Array (_ BitVec 32) (_ BitVec 32)))
(declare-rel main__bb0 (Bool (_ BitVec 8) Bool Bool))
(declare-rel main__bb1 (Bool (_ BitVec 8) Bool Bool))
(declare-rel main__bb2 (Bool Bool))
(declare-rel main__bb3 (Bool (_ BitVec 8) Bool Bool))
(declare-rel main__bb4 (Bool (_ BitVec 8) Bool Bool))
(declare-rel main__bb5 (Bool (_ BitVec 8) Bool Bool))
(declare-rel main__bb6 (Bool (_ BitVec 8) Bool Bool))
(declare-rel main__bb7 (Bool (_ BitVec 8) Bool Bool))
(declare-rel main__bb8 (Bool (_ BitVec 8) Bool Bool))
(declare-rel error ())
(rule (=> (= obj_valid ((as const (Array (_ BitVec 32) Bool)) true)) (main__bb0 _main_0 _main_1 _main_2 _main_3)))
(rule (=> (main__bb0 _main_0 _main_1 _main_2 _main_3) (main__bb3 _main_0 _main_1 _main_2 _main_3)))
(rule (=> (main__bb3 _main_0 _main_1 _main_2 _main_3) (main__bb5 _main_0 _main_1 _main_2 _main_3)))
(rule (=> (main__bb5 _main_0 _main_1 _main_2 _main_3) (main__bb7 _main_0 _main_1 _main_2 _main_3)))
(rule (=> (main__bb7 _main_0 _main_1 _main_2 _main_3) (main__bb8 _main_0 _main_1__out _main_2 _main_3)))
(rule (=> (main__bb8 _main_0 _main_1 _main_2 _main_3) (main__bb6 _main_0 _main_1 _main_2 _main_3)))
(rule (=> (main__bb6 _main_0 _main_1 _main_2 _main_3) (main__bb4 _main_0 _main_1 _main_2 _main_3)))
(rule (=> (main__bb4 _main_0 _main_1 _main_2 _main_3) (main__bb1 _main_0 _main_1 _main_2 _main_3)))
(rule (=> (and (and (main__bb1 _main_0 _main_1 _main_2 _main_3) (= _main_3__out (= _main_1 #x00))) (= _main_1 #x00)) (main__bb2 _main_0 _main_2__out)))
(rule (=> (and (and (main__bb1 _main_0 _main_1 _main_2 _main_3) (= _main_3__out (= _main_1 #x00))) (not (= _main_1 #x00))) error))
(query error)
";

    // Step 1: Run AdaptivePortfolio (currently produces false Safe per ay#8578).
    let problem = ChcParser::parse(smt_content).expect("parse should succeed");
    let config = AdaptiveConfig::with_budget(Duration::from_secs(30), true);
    let solver = AdaptivePortfolio::new(problem, config);
    let portfolio_result = solver.solve();

    // Step 2: If portfolio returned Safe, verify the model in a fresh PDR solver.
    // Full clause verification (not query-only) catches the wrong invariant.
    if let Some(inv) = portfolio_result.safe_invariant() {
        let verify_problem = ChcParser::parse(smt_content).expect("parse should succeed");
        let mut pdr_config = PdrConfig::default();
        pdr_config.verbose = true;
        let model_valid =
            engines::validate_external_invariant_model(&verify_problem, inv.model(), &pdr_config)
                .expect("external invariant model validation should not panic");
        assert!(
            !model_valid,
            "The false invariant from ay#8578 must FAIL full clause verification. \
             If this assertion fails, ay has fixed ay#8578 — update this test to \
             expect Unsafe from AdaptivePortfolio instead."
        );
        eprintln!(
            "CONFIRMED: AdaptivePortfolio returned false Safe, but full model \
             verification correctly detected the invalid invariant (ay#8578 defense works)."
        );
    } else {
        // AdaptivePortfolio returned Unsafe or Unknown — upstream fix may have landed.
        eprintln!(
            "NOTE: AdaptivePortfolio did NOT return Safe — ay#8578 may be fixed upstream. \
             Result is_unsafe={}, is_unknown={}",
            portfolio_result.is_unsafe(),
            portfolio_result.is_unknown()
        );
    }
}

// =============================================================================
// UNKNOWN-category classifier tests (Part of #4304 / #4301)
// =============================================================================

#[cfg(feature = "ay-chc-native")]
mod unknown_classifier_tests {
    use super::super::native::SolveBudgetGrant;
    use super::super::{BudgetSummary, UnknownCategory, classify_unknown};
    use std::time::Duration;

    fn starved() -> Option<SolveBudgetGrant> {
        Some(SolveBudgetGrant {
            granted: Duration::from_millis(400),
            nominal: Duration::from_secs(15),
        })
    }

    fn fully_funded() -> Option<SolveBudgetGrant> {
        Some(SolveBudgetGrant {
            granted: Duration::from_secs(15),
            nominal: Duration::from_secs(15),
        })
    }

    /// A solve the per-harness deadline starved of its nominal budget is
    /// budget-bound before it is anything structural: `BudgetExhausted`
    /// precedes `ArrayParamLimit` (and `PdrTimeout`), and only `NoErrorRule`
    /// — a property of the VC, not of the run — comes first.
    #[test]
    fn classify_unknown_budget_exhausted_precedes_array_param_limit() {
        let preds = vec![("main__bb0".to_string(), 3usize)];
        let summary = BudgetSummary {
            completed: 0,
            timed_out: 2,
            total_elapsed_ms: 400,
            first_non_completed: Some(("pdr".to_string(), "Timeout".to_string())),
        };
        let got = classify_unknown(&preds, Some(&summary), true, starved());
        assert_eq!(got, UnknownCategory::BudgetExhausted { granted_ms: 400, nominal_ms: 15_000 });
        assert!(got.tag_line().contains("[AY:UNKNOWN-CATEGORY] per-harness budget exhausted"));
        assert!(got.tag_line().contains("400ms of its nominal 15000ms"), "{}", got.tag_line());
        // No budget summary at all (guard timeout, portfolio never started):
        // still budget exhausted when the grant was starved.
        assert!(matches!(
            classify_unknown(&preds, None, true, starved()),
            UnknownCategory::BudgetExhausted { .. }
        ));
        // The degenerate VC still wins over everything.
        assert_eq!(classify_unknown(&preds, None, false, starved()), UnknownCategory::NoErrorRule);
    }

    /// A FULLY funded solve keeps the measured ordering: the array label
    /// still preempts the full-budget timeout (those rows did not convert
    /// at 8x budget), and an unstarved grant changes nothing.
    #[test]
    fn classify_unknown_fully_funded_grant_keeps_measured_ordering() {
        let preds = vec![("main__bb0".to_string(), 3usize)];
        let summary = BudgetSummary {
            completed: 0,
            timed_out: 2,
            total_elapsed_ms: 15_000,
            first_non_completed: Some(("pdr".to_string(), "Timeout".to_string())),
        };
        assert!(matches!(
            classify_unknown(&preds, Some(&summary), true, fully_funded()),
            UnknownCategory::ArrayParamLimit { .. }
        ));
        let scalar = vec![("main__bb0".to_string(), 0usize)];
        assert!(matches!(
            classify_unknown(&scalar, Some(&summary), true, fully_funded()),
            UnknownCategory::PdrTimeout { .. }
        ));
    }

    /// Category 4: `has_error_rule = false` always wins, regardless of other signals.
    #[test]
    fn classify_unknown_no_error_rule_wins() {
        let preds = vec![("P".to_string(), 2usize)];
        let got = classify_unknown(&preds, None, false, None);
        assert_eq!(got, UnknownCategory::NoErrorRule);
        assert!(got.tag_line().contains("no error rule encoded"));
        assert!(got.tag_line().contains("#4284"));
    }

    /// Category 1: ≥2 Array-sorted state params on any predicate fires over
    /// PDR/solver-error signals.
    #[test]
    fn classify_unknown_array_param_limit_fires() {
        let preds = vec![("P_entry".to_string(), 0usize), ("P_loop".to_string(), 3usize)];
        let got = classify_unknown(&preds, None, true, None);
        match got {
            UnknownCategory::ArrayParamLimit { predicate, array_sort_count } => {
                assert_eq!(predicate, "P_loop");
                assert_eq!(array_sort_count, 3);
            }
            other => panic!("expected ArrayParamLimit, got {other:?}"),
        }
        let tag = classify_unknown(&preds, None, true, None).tag_line();
        assert!(tag.contains("Array-sorted"));
        assert!(tag.contains("#4259"));
    }

    /// Category 2: All engines timed out → PDR timeout.
    #[test]
    fn classify_unknown_pdr_timeout() {
        let summary = BudgetSummary {
            completed: 0,
            timed_out: 2,
            total_elapsed_ms: 30500,
            first_non_completed: Some(("PDR".to_string(), "Timeout".to_string())),
        };
        let preds: Vec<(String, usize)> = vec![("P".to_string(), 1usize)];
        let got = classify_unknown(&preds, Some(&summary), true, None);
        match got {
            UnknownCategory::PdrTimeout { timed_out_engines, elapsed_ms } => {
                assert_eq!(timed_out_engines, 2);
                assert_eq!(elapsed_ms, 30500);
            }
            other => panic!("expected PdrTimeout, got {other:?}"),
        }
        let tag = classify_unknown(&preds, Some(&summary), true, None).tag_line();
        assert!(tag.contains("PDR"));
        assert!(tag.contains("30500ms"));
    }

    /// Category 3: No engine completed, none timed out — one NotApplicable
    /// means classification picks SolverError with that engine.
    #[test]
    fn classify_unknown_solver_error() {
        let summary = BudgetSummary {
            completed: 0,
            timed_out: 0,
            total_elapsed_ms: 5,
            first_non_completed: Some(("TPA".to_string(), "NotApplicable".to_string())),
        };
        let preds: Vec<(String, usize)> = vec![("P".to_string(), 0usize)];
        let got = classify_unknown(&preds, Some(&summary), true, None);
        match got {
            UnknownCategory::SolverError { engine_name, stop_reason } => {
                assert_eq!(engine_name, "TPA");
                assert_eq!(stop_reason, "NotApplicable");
            }
            other => panic!("expected SolverError, got {other:?}"),
        }
        let tag = classify_unknown(&preds, Some(&summary), true, None).tag_line();
        assert!(tag.contains("solver error"));
        assert!(tag.contains("TPA"));
    }

    /// Category 5: Budget where at least one engine completed but overall result
    /// is still UNKNOWN (e.g. demoted Safe). Falls through to Uncategorized.
    #[test]
    fn classify_unknown_uncategorized_fallthrough() {
        let summary = BudgetSummary {
            completed: 1,
            timed_out: 0,
            total_elapsed_ms: 1000,
            first_non_completed: None,
        };
        let preds: Vec<(String, usize)> = vec![("P".to_string(), 1usize)];
        let got = classify_unknown(&preds, Some(&summary), true, None);
        assert_eq!(got, UnknownCategory::Uncategorized);
        assert!(got.tag_line().contains("uncategorized"));
    }

    /// Priority: ArrayParamLimit wins over PdrTimeout when both signals present.
    #[test]
    fn classify_unknown_priority_array_over_timeout() {
        let summary = BudgetSummary {
            completed: 0,
            timed_out: 1,
            total_elapsed_ms: 30_000,
            first_non_completed: Some(("PDR".to_string(), "Timeout".to_string())),
        };
        let preds = vec![("P".to_string(), 2usize)];
        let got = classify_unknown(&preds, Some(&summary), true, None);
        assert!(matches!(got, UnknownCategory::ArrayParamLimit { .. }));
    }

    /// Priority: NoErrorRule beats ArrayParamLimit (degenerate VC detected first).
    #[test]
    fn classify_unknown_no_error_rule_beats_array_limit() {
        let preds = vec![("P".to_string(), 5usize)];
        let got = classify_unknown(&preds, None, false, None);
        assert_eq!(got, UnknownCategory::NoErrorRule);
    }
}

// ── Guards may not outlive the per-harness deadline ─────────────────────────
//
// Every lane budget in `native.rs` is `deadline.clamp(...)`, so a guard of
// `budget + grace` sits past the deadline by construction. Measured 2026-09-14:
// a 15 s per-call budget gives a 20 s acyclic-BMC guard, and units that blow it
// spend the full 20 s and then run the decision procedure inside what is left.

#[cfg(feature = "ay-chc-native")]
#[test]
fn a_guard_adds_its_grace_when_the_deadline_is_far_away() {
    let deadline = crate::deadline::Deadline::after(std::time::Duration::from_secs(3600));
    let guard = guard_timeout_within_deadline(std::time::Duration::from_secs(15), &deadline);
    assert_eq!(guard, std::time::Duration::from_secs(20));
}

#[cfg(feature = "ay-chc-native")]
#[test]
fn a_guard_never_outlives_the_deadline() {
    let deadline = crate::deadline::Deadline::after(std::time::Duration::from_secs(7));
    let guard = guard_timeout_within_deadline(std::time::Duration::from_secs(15), &deadline);
    assert!(
        guard <= std::time::Duration::from_secs(7),
        "the guard must not run past the per-harness deadline, got {guard:?}"
    );
    assert!(
        guard > std::time::Duration::from_secs(6),
        "and it must still use what is left: {guard:?}"
    );
}

#[cfg(feature = "ay-chc-native")]
#[test]
fn an_expired_deadline_gives_a_guard_no_time_at_all() {
    // Fail-closed: `recv_timeout(ZERO)` abandons the lane immediately, which
    // only skips a shortcut (acyclic BMC) or returns UNKNOWN (forced engine).
    let deadline = crate::deadline::Deadline::after(std::time::Duration::ZERO);
    assert_eq!(
        guard_timeout_within_deadline(std::time::Duration::from_secs(15), &deadline),
        std::time::Duration::ZERO
    );
}

/// D4: a shortfall INSIDE the drain window does not cut the lane's own budget.
///
/// `lane_budget` was itself clamped to the deadline before the lane started, so
/// a second of pre-solve leaves `remaining` a second short of a budget the lane
/// was already promised. Cutting there abandons a lane that may have been about
/// to answer and saves less time than the abandonment's own drain costs.
#[cfg(feature = "ay-chc-native")]
#[test]
fn a_guard_keeps_a_promised_budget_when_the_shortfall_is_inside_the_drain_window() {
    let deadline = crate::deadline::Deadline::after(std::time::Duration::from_secs(14));
    let guard = guard_timeout_within_deadline(std::time::Duration::from_secs(15), &deadline);
    assert_eq!(
        guard,
        std::time::Duration::from_secs(15),
        "a 1 s shortfall on a 15 s promised budget must not abandon the lane early"
    );
}

/// The other side of the same rule: past the drain window the deadline wins.
#[cfg(feature = "ay-chc-native")]
#[test]
fn a_guard_yields_to_the_deadline_once_the_shortfall_exceeds_the_drain_window() {
    let deadline = crate::deadline::Deadline::after(std::time::Duration::from_secs(9));
    let guard = guard_timeout_within_deadline(std::time::Duration::from_secs(15), &deadline);
    assert!(
        guard <= std::time::Duration::from_secs(9),
        "a 6 s shortfall is a deadline that genuinely moved on, got {guard:?}"
    );
    assert!(guard > std::time::Duration::from_secs(8), "and it still uses what is left: {guard:?}");
}
