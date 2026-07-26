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
    NativeSolveMode, native_bmc_per_depth_timeout, scalar_acyclic_bmc_counterexample_is_trusted,
    select_native_solve_mode,
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
    use super::super::{BudgetSummary, UnknownCategory, classify_unknown};

    /// Category 4: `has_error_rule = false` always wins, regardless of other signals.
    #[test]
    fn classify_unknown_no_error_rule_wins() {
        let preds = vec![("P".to_string(), 2usize)];
        let got = classify_unknown(&preds, None, false);
        assert_eq!(got, UnknownCategory::NoErrorRule);
        assert!(got.tag_line().contains("no error rule encoded"));
        assert!(got.tag_line().contains("#4284"));
    }

    /// Category 1: ≥2 Array-sorted state params on any predicate fires over
    /// PDR/solver-error signals.
    #[test]
    fn classify_unknown_array_param_limit_fires() {
        let preds = vec![("P_entry".to_string(), 0usize), ("P_loop".to_string(), 3usize)];
        let got = classify_unknown(&preds, None, true);
        match got {
            UnknownCategory::ArrayParamLimit { predicate, array_sort_count } => {
                assert_eq!(predicate, "P_loop");
                assert_eq!(array_sort_count, 3);
            }
            other => panic!("expected ArrayParamLimit, got {other:?}"),
        }
        let tag = classify_unknown(&preds, None, true).tag_line();
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
        let got = classify_unknown(&preds, Some(&summary), true);
        match got {
            UnknownCategory::PdrTimeout { timed_out_engines, elapsed_ms } => {
                assert_eq!(timed_out_engines, 2);
                assert_eq!(elapsed_ms, 30500);
            }
            other => panic!("expected PdrTimeout, got {other:?}"),
        }
        let tag = classify_unknown(&preds, Some(&summary), true).tag_line();
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
        let got = classify_unknown(&preds, Some(&summary), true);
        match got {
            UnknownCategory::SolverError { engine_name, stop_reason } => {
                assert_eq!(engine_name, "TPA");
                assert_eq!(stop_reason, "NotApplicable");
            }
            other => panic!("expected SolverError, got {other:?}"),
        }
        let tag = classify_unknown(&preds, Some(&summary), true).tag_line();
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
        let got = classify_unknown(&preds, Some(&summary), true);
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
        let got = classify_unknown(&preds, Some(&summary), true);
        assert!(matches!(got, UnknownCategory::ArrayParamLimit { .. }));
    }

    /// Priority: NoErrorRule beats ArrayParamLimit (degenerate VC detected first).
    #[test]
    fn classify_unknown_no_error_rule_beats_array_limit() {
        let preds = vec![("P".to_string(), 5usize)];
        let got = classify_unknown(&preds, None, false);
        assert_eq!(got, UnknownCategory::NoErrorRule);
    }
}
