// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for the emitter module.
//!
//! Extracted from emitter.rs per #775 to separate test and production code.

use super::emitter::{emit_bmc, emit_chc, emit_chc_program, emit_chc_smt2};
use ay_bindings::{DatatypeConstructor, DatatypeSort, Expr, RoundingMode, Sort};
use trust_mc_core::ident::PropertyId;
use trust_mc_core::violation::{PropertyKind, Violation};
use trust_mc_core::{
    BmcVc, ChcQuery, ChcVc, Decl, RelationApp, RelationDecl, Rule, RuleBody, VarDecl,
};

#[test]
fn test_emit_empty_bmc() {
    let vc = BmcVc::new();
    let program = emit_bmc(vc);
    let smt = program.to_string();
    // Should have trivial UNSAT query
    assert!(smt.contains("(assert false)"));
    assert!(smt.contains("(check-sat)"));
}

#[test]
fn test_emit_bmc_with_constraint() {
    let mut vc = BmcVc::new();
    vc.add_constraint(Expr::bool_const(true));

    let violation = Violation::new(
        PropertyId::new(1),
        PropertyKind::Assertion,
        Expr::bool_const(false), // violation condition
    );
    vc.add_violation(violation);

    let program = emit_bmc(vc);
    let smt = program.to_string();

    // Should have violation predicate (format: ay_violation_<label>_<id>)
    assert!(smt.contains("ay_violation_kani_assert_0"));
    assert!(smt.contains("(check-sat)"));
}

#[test]
fn test_emit_bmc_with_decl() {
    let mut vc = BmcVc::new();
    vc.add_decl(Decl::constant("x", Sort::bv32()));
    vc.add_decl(Decl::constant("y", Sort::bv32()));

    let violation = Violation::new(
        PropertyId::new(1),
        PropertyKind::ArithmeticOverflow,
        Expr::var("overflow".to_string(), Sort::bool()),
    );
    vc.add_violation(violation);

    let program = emit_bmc(vc);
    let smt = program.to_string();

    // Should declare constants
    assert!(smt.contains("declare-const"));
    assert!(smt.contains("(_ BitVec 32)"));
}

#[test]
fn test_emit_bmc_declares_implicit_fresh_vars() {
    let mut vc = BmcVc::new();
    vc.add_constraint(Expr::var("sort_mismatch_phi_0", Sort::bv32()).eq(Expr::bitvec_const(0, 32)));
    vc.add_violation(Violation::new(
        PropertyId::new(1),
        PropertyKind::Assertion,
        Expr::bool_const(false),
    ));

    let program = emit_bmc(vc);
    let smt = program.to_string();

    assert!(
        smt.contains("(declare-const sort_mismatch_phi_0 (_ BitVec 32))"),
        "implicit fresh var should be declared before use; SMT:\n{smt}"
    );
}

#[test]
fn test_emit_bmc_uses_violation_smt_var_when_present() {
    let mut vc = BmcVc::new();
    let violation = Violation::new(PropertyId::new(1), PropertyKind::Other, Expr::bool_const(true))
        .with_smt_var("ay_violation_kani_assert_42");
    vc.add_violation(violation);

    let program = emit_bmc(vc);
    let smt = program.to_string();

    assert!(smt.contains("(declare-const ay_violation_kani_assert_42 Bool)"));
    assert!(!smt.contains("ay_violation_assertion_0"));
}

#[test]
fn test_emit_bmc_upgrades_logic_for_datatypes() {
    let mut vc = BmcVc::new();
    // Set logic to QF_AUFBV (doesn't support datatypes)
    vc.query.logic = Some("QF_AUFBV".to_string());

    // Add a datatype declaration (simple enum with 3 variants)
    let dt = DatatypeSort {
        name: "MyEnum".to_string(),
        constructors: vec![
            DatatypeConstructor { name: "A".to_string(), fields: vec![] },
            DatatypeConstructor { name: "B".to_string(), fields: vec![] },
            DatatypeConstructor { name: "C".to_string(), fields: vec![] },
        ],
    };
    vc.add_decl(Decl::datatype(dt));

    let program = emit_bmc(vc);
    let smt = program.to_string();

    // Logic should be upgraded from QF_AUFBV to ALL (or contain ALL)
    // because QF_AUFBV doesn't support datatypes
    assert!(
        smt.contains("(set-logic ALL)") || !smt.contains("QF_AUFBV"),
        "Logic should be upgraded to ALL when datatypes are present, got: {}",
        smt.lines().take(5).collect::<Vec<_>>().join("\n")
    );
    // Should still contain the datatype declaration
    assert!(smt.contains("declare-datatype") || smt.contains("MyEnum"));
}

#[test]
fn test_emit_empty_chc() {
    let vc = ChcVc::new();
    let program = emit_chc(&vc);
    let smt = program.to_string();
    // Should use HORN logic
    assert!(smt.contains("(set-logic HORN)"));
}

#[test]
fn test_emit_chc_with_rules() {
    let mut vc = ChcVc::new();

    // Add error relation (nullary)
    vc.add_relation(RelationDecl::nullary("error"));

    // Add state relation with Int parameter
    vc.add_relation(RelationDecl::new("state", vec![Sort::int()]));

    // Add variable declaration for x
    vc.add_var(VarDecl::new("x", Sort::int()));

    // Init rule: x=0 => state(x)
    let init_rule = Rule::init(
        Expr::int_const(0).eq(Expr::var("x".to_string(), Sort::int())),
        RelationApp::new("state", vec![Expr::var("x".to_string(), Sort::int())]),
    );
    vc.add_rule(init_rule);

    // Error rule: state(x) & x > 10 => error
    let error_rule = Rule::new(
        RuleBody::new(
            Some(RelationApp::new("state", vec![Expr::var("x".to_string(), Sort::int())])),
            vec![Expr::var("x".to_string(), Sort::int()).int_gt(Expr::int_const(10))],
        ),
        RelationApp::nullary("error"),
    );
    vc.add_rule(error_rule);

    // Set query target
    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Should use HORN logic
    assert!(smt.contains("(set-logic HORN)"));
    // Should have declare-var for x
    assert!(smt.contains("(declare-var"), "CHC should emit (declare-var ...) for x");
    // Should have declare-rel for state and error
    assert!(smt.contains("(declare-rel"), "CHC should emit (declare-rel ...) for relations");
    // Should have rule commands for init and error rules
    assert!(smt.contains("(rule (=>"), "CHC should emit (rule (=> ...)) for Horn clauses");
    // Should have query targeting error
    assert!(smt.contains("(query error"), "CHC should emit (query error) for reachability check");
}

#[test]
fn test_programmatic_chc_emitters_match_existing_emitter() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::nullary("error"));
    vc.query = ChcQuery::new().with_target("error");

    let existing = emit_chc(&vc).to_string();

    assert_eq!(emit_chc_program(&vc).to_string(), existing);
    assert_eq!(emit_chc_smt2(&vc), existing);
    assert!(existing.contains("(set-logic HORN)"));
    assert!(existing.contains("(query error)"));
}

#[test]
fn test_emit_chc_preserves_floating_point_sorts_and_ops() {
    let fp32 = Sort::fp32();
    let x = Expr::var("x".to_string(), fp32.clone());
    let y = Expr::var("y".to_string(), fp32.clone());

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", fp32.clone()));
    vc.add_var(VarDecl::new("y", fp32.clone()));
    vc.add_relation(RelationDecl::new("state", vec![fp32.clone()]));
    vc.add_relation(RelationDecl::nullary("error"));

    vc.add_rule(Rule::init(Expr::bool_const(true), RelationApp::new("state", vec![x.clone()])));

    let fp_sum = x.clone().fp_add(RoundingMode::RNE, Expr::fp_plus_zero(&fp32));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("state", vec![x])), vec![y.eq(fp_sum)]),
        RelationApp::nullary("error"),
    ));
    vc.query = ChcQuery::new().with_target("error");

    let smt = emit_chc(&vc).to_string();

    assert!(
        smt.contains("(declare-var x (_ FloatingPoint 8 24))"),
        "CHC should preserve FP declare-var sorts, got:\n{smt}"
    );
    assert!(
        smt.contains("(declare-rel state ((_ FloatingPoint 8 24)))"),
        "CHC should preserve FP declare-rel sorts, got:\n{smt}"
    );
    assert!(smt.contains("(fp.add RNE"), "CHC should preserve FP arithmetic terms, got:\n{smt}");
    assert!(
        !smt.contains("fp.to_sbv") && !smt.contains("fp.to_ubv"),
        "emitter should not inject lossy FP-to-BV numeric conversions, got:\n{smt}"
    );
}

/// Run AY/SMT on an SMT-LIB2 string and return the verdict.
///
/// De-duplicated (#2596): these emitter tests now share the single z3-primary
/// runner used by the integration tests (`integration_ay_runner`), rather than
/// carrying their own ay-only copy. That runner routes plain SMT and the CHC
/// dialect to z3 (the oracle these tests were validated against) under a hard
/// timeout, falling back to ay only when no `z3` binary is on PATH, and always
/// enforces the `sat`/`unsat`/`unknown` whitelist.
use super::codegen_function::integration_ay_runner::run_ay_on_smt2;

/// Test that CHC emitter produces semantically correct UNSAT output.
///
/// Creates a CHC where error is unreachable:
/// - Init: x=0 => state(x)
/// - Error: state(x) & x>10 => error
/// - No transition rules to increment x
///
/// Error is unreachable because we can only reach state(0) and 0 is not > 10.
/// AY should report UNSAT (error is not reachable).
#[test]
fn test_chc_semantic_unsat() {
    let mut vc = ChcVc::new();

    // Declare variable x
    vc.add_var(VarDecl::new("x", Sort::int()));

    // Declare relations
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("state", vec![Sort::int()]));

    // Init rule: x=0 => state(x)
    let init_rule = Rule::init(
        Expr::int_const(0).eq(Expr::var("x".to_string(), Sort::int())),
        RelationApp::new("state", vec![Expr::var("x".to_string(), Sort::int())]),
    );
    vc.add_rule(init_rule);

    // Error rule: state(x) & x > 10 => error
    let error_rule = Rule::new(
        RuleBody::new(
            Some(RelationApp::new("state", vec![Expr::var("x".to_string(), Sort::int())])),
            vec![Expr::var("x".to_string(), Sort::int()).int_gt(Expr::int_const(10))],
        ),
        RelationApp::nullary("error"),
    );
    vc.add_rule(error_rule);

    // Query error reachability
    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Run AY and verify UNSAT (error unreachable)
    match run_ay_on_smt2(&smt) {
        Ok(result) => {
            assert_eq!(
                result, "unsat",
                "CHC should be UNSAT (error unreachable). Got: {}. SMT:\n{}",
                result, smt
            );
        }
        Err(e) => panic!("AY execution failed: {}. SMT:\n{}", e, smt),
    }
}

/// Test that CHC emitter produces semantically correct SAT output.
///
/// Creates a CHC where error is reachable:
/// - Init: true => state(5)
/// - Error: state(x) & x>0 => error
///
/// Error is reachable because state(5) is reachable and 5>0.
/// AY should report SAT (error is reachable).
#[test]
fn test_chc_semantic_sat() {
    let mut vc = ChcVc::new();

    // Declare variable x
    vc.add_var(VarDecl::new("x", Sort::int()));

    // Declare relations
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("state", vec![Sort::int()]));

    // Init rule: true => state(5)
    let init_rule =
        Rule::init(Expr::bool_const(true), RelationApp::new("state", vec![Expr::int_const(5)]));
    vc.add_rule(init_rule);

    // Error rule: state(x) & x > 0 => error
    let error_rule = Rule::new(
        RuleBody::new(
            Some(RelationApp::new("state", vec![Expr::var("x".to_string(), Sort::int())])),
            vec![Expr::var("x".to_string(), Sort::int()).int_gt(Expr::int_const(0))],
        ),
        RelationApp::nullary("error"),
    );
    vc.add_rule(error_rule);

    // Query error reachability
    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Run AY and verify SAT (error reachable)
    match run_ay_on_smt2(&smt) {
        Ok(result) => {
            assert_eq!(
                result, "sat",
                "CHC should be SAT (error reachable). Got: {}. SMT:\n{}",
                result, smt
            );
        }
        Err(e) => panic!("AY execution failed: {}. SMT:\n{}", e, smt),
    }
}

/// Test CHC with inductive transition (loop invariant).
///
/// Creates a CHC modeling a counter that stays bounded:
/// - Init: x=0 => state(x)
/// - Step: state(x) & x<5 => state(x+1)
/// - Error: state(x) & x>=10 => error
///
/// The loop invariant is x<=5. Error requires x>=10, so error is unreachable.
/// This tests that the CHC solver can handle inductive proofs.
#[test]
fn test_chc_semantic_inductive_unsat() {
    let mut vc = ChcVc::new();

    // Declare variable x
    vc.add_var(VarDecl::new("x", Sort::int()));

    // Declare relations
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("state", vec![Sort::int()]));

    // Init rule: x=0 => state(x)
    let init_rule = Rule::init(
        Expr::int_const(0).eq(Expr::var("x".to_string(), Sort::int())),
        RelationApp::new("state", vec![Expr::var("x".to_string(), Sort::int())]),
    );
    vc.add_rule(init_rule);

    // Step rule: state(x) & x<5 => state(x+1)
    let x = Expr::var("x".to_string(), Sort::int());
    let x_plus_1 = x.clone().int_add(Expr::int_const(1));
    let step_rule = Rule::new(
        RuleBody::new(
            Some(RelationApp::new("state", vec![x.clone()])),
            vec![x.clone().int_lt(Expr::int_const(5))],
        ),
        RelationApp::new("state", vec![x_plus_1]),
    );
    vc.add_rule(step_rule);

    // Error rule: state(x) & x >= 10 => error
    let ten = Expr::int_const(10);
    let body = RuleBody::new(Some(RelationApp::new("state", vec![x.clone()])), vec![x.int_ge(ten)]);
    vc.add_rule(Rule::new(body, RelationApp::nullary("error")));

    // Query error reachability
    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Run AY and verify UNSAT (error unreachable - inductive proof)
    match run_ay_on_smt2(&smt) {
        Ok(result) => {
            assert_eq!(
                result, "unsat",
                "CHC should be UNSAT (error unreachable via induction). Got: {}. SMT:\n{}",
                result, smt
            );
        }
        Err(e) => panic!("AY execution failed: {}. SMT:\n{}", e, smt),
    }
}

#[test]
fn test_emit_bmc_default_logic() {
    // BMC mode without datatypes should emit QF_AUFBV
    let mut vc = BmcVc::new();
    vc.query.logic = Some("QF_AUFBV".to_string());
    vc.add_decl(Decl::constant("x", Sort::bv32()));

    let program = emit_bmc(vc);
    let smt = program.to_string();

    // Should contain QF_AUFBV logic
    assert!(
        smt.contains("(set-logic QF_AUFBV)"),
        "BMC without datatypes should use QF_AUFBV, got: {}",
        smt.lines().take(5).collect::<Vec<_>>().join("\n")
    );
}

#[test]
fn test_emit_chc_horn_logic() {
    // CHC mode should always emit HORN logic
    let vc = ChcVc::new();
    let program = emit_chc(&vc);
    let smt = program.to_string();

    // HORN logic is required for CHC/fixedpoint solving
    assert!(
        smt.contains("(set-logic HORN)"),
        "CHC mode should use HORN logic, got: {}",
        smt.lines().take(5).collect::<Vec<_>>().join("\n")
    );
}

#[test]
fn test_emit_chc_entry_rule_with_true_body() {
    // Entry rules have `true` as body constraint - verify this serializes correctly (#657)
    // Use crate-level re-exports to validate they work (#658)
    let mut vc = ChcVc::new();

    // Declare variable x
    vc.add_var(VarDecl::new("x", Sort::int()));

    // Declare bb0 relation
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));

    // Add entry rule: true => bb0(x)
    // This is the exact pattern used by emit_entry_rule()
    let x_var = Expr::var("x".to_string(), Sort::int());
    let bb0_app = RelationApp::new("bb0", vec![x_var]);
    let entry_rule = Rule::init(Expr::bool_const(true), bb0_app);
    vc.add_rule(entry_rule);

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // The entry rule should appear in the output with the correct structure
    // Expected format: (rule (=> true (bb0 x)))
    assert!(smt.contains("(rule"), "Entry rule should produce a (rule ...) command. SMT:\n{}", smt);
    assert!(smt.contains("(bb0"), "Entry rule should reference bb0 relation. SMT:\n{}", smt);
    // Verify the implication structure with true body
    assert!(
        smt.contains("=> true") || smt.contains("=>true"),
        "Entry rule should have (=> true ...) implication. SMT:\n{}",
        smt
    );
}

/// Test that BMC kani::assert(true) produces UNSAT (no counterexample) (#2078).
///
/// Models: `kani::assert(true)` where the violation condition is `!true = false`.
/// The violation predicate is equivalent to `false`, so the disjunction is
/// unsatisfiable. AY should report UNSAT -> VERIFICATION: SUCCESSFUL.
///
/// Acceptance criteria #3 for #2078: "0 of 1 failed → VERIFICATION: SUCCESSFUL"
#[test]
fn test_bmc_kani_assert_true_unsat() {
    let mut vc = BmcVc::new();
    vc.query.logic = Some("QF_AUFBV".to_string());
    vc.query.produce_model = true;

    // kani::assert(true) → record_violation_guarded(!true) → violation = false
    let violation = Violation::new(
        PropertyId::new(0),
        PropertyKind::Assertion,
        Expr::bool_const(false), // !true — violation condition is never satisfied
    )
    .with_smt_var("ay_violation_kani_assert_0");
    vc.add_violation(violation);

    let program = emit_bmc(vc);
    let smt = program.to_string();

    // Structural: violation predicate should be declared
    assert!(
        smt.contains("(declare-const ay_violation_kani_assert_0 Bool)"),
        "Missing violation declaration. SMT:\n{}",
        smt
    );

    // Semantic: AY should return UNSAT (no counterexample)
    match run_ay_on_smt2(&smt) {
        Ok(result) => {
            assert_eq!(
                result, "unsat",
                "kani::assert(true) should be UNSAT (no violation). Got: {}. SMT:\n{}",
                result, smt
            );
        }
        Err(e) => panic!("AY execution failed: {}. SMT:\n{}", e, smt),
    }
}

/// Test that BMC kani::assert(false) produces SAT (counterexample found) (#2078).
///
/// Models: `kani::assert(false)` where the violation condition is `!false = true`.
/// The violation predicate is equivalent to `true`, so the disjunction is
/// trivially satisfiable. AY should report SAT -> "1 of 1 failed".
///
/// Acceptance criteria #2 for #2078: "Test with kani::assert(false) shows 1 of 1 failed"
#[test]
fn test_bmc_kani_assert_false_sat() {
    let mut vc = BmcVc::new();
    vc.query.logic = Some("QF_AUFBV".to_string());
    vc.query.produce_model = true;

    // kani::assert(false) → record_violation_guarded(!false) → violation = true
    let violation = Violation::new(
        PropertyId::new(0),
        PropertyKind::Assertion,
        Expr::bool_const(true), // !false — violation is always satisfiable
    )
    .with_smt_var("ay_violation_kani_assert_0");
    vc.add_violation(violation);

    let program = emit_bmc(vc);
    let smt = program.to_string();

    // Structural: violation predicate should be declared
    assert!(
        smt.contains("(declare-const ay_violation_kani_assert_0 Bool)"),
        "Missing violation declaration. SMT:\n{}",
        smt
    );

    // Semantic: AY should return SAT (counterexample exists)
    match run_ay_on_smt2(&smt) {
        Ok(result) => {
            assert_eq!(
                result, "sat",
                "kani::assert(false) should be SAT (violation found). Got: {}. SMT:\n{}",
                result, smt
            );
        }
        Err(e) => panic!("AY execution failed: {}. SMT:\n{}", e, smt),
    }
}

/// Test CHC assume constraint blocks error path (#1889).
///
/// This test mimics the pattern in test_div_guarded_pass:
/// - Entry rule: true → bb0(_2) with unconstrained _2
/// - Assume rule: bb0(_2) ∧ (_4__out == (_2 != 0)) ∧ _4__out → bb1(_2)
/// - Error rule: bb1(_2) ∧ (_10__out == (_2 == 0)) ∧ _10__out → error()
///
/// The assume constraint should block all paths where _2 == 0,
/// making error unreachable. AY should report UNSAT.
#[test]
fn test_chc_assume_blocks_error_path() {
    let mut vc = ChcVc::new();

    // Declare bitvec32 variable _2 for the divisor
    vc.add_var(VarDecl::new("_2", Sort::bitvec(32)));
    // Declare boolean variables for intermediate computations
    vc.add_var(VarDecl::new("_4__out", Sort::bool()));
    vc.add_var(VarDecl::new("_10__out", Sort::bool()));

    // Declare relations
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(32)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(32)]));

    // Entry rule: true → bb0(_2)
    // _2 is unconstrained (symbolic any value)
    let var_2 = Expr::var("_2", Sort::bitvec(32));
    let entry_rule =
        Rule::init(Expr::bool_const(true), RelationApp::new("bb0", vec![var_2.clone()]));
    vc.add_rule(entry_rule);

    // Assume rule: bb0(_2) ∧ (_4__out == (_2 != 0)) ∧ _4__out → bb1(_2)
    // This constrains bb1 to only be reachable when _2 != 0
    let _4_out = Expr::var("_4__out", Sort::bool());
    let zero = Expr::bitvec_const(0i32, 32);
    let var_2_ne_zero = var_2.clone().eq(zero.clone()).not(); // _2 != 0
    let assume_def = _4_out.clone().eq(var_2_ne_zero); // _4__out == (_2 != 0)
    let assume_rule = Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![var_2.clone()])),
            vec![assume_def, _4_out], // _4__out == (_2 != 0) AND _4__out
        ),
        RelationApp::new("bb1", vec![var_2.clone()]),
    );
    vc.add_rule(assume_rule);

    // Error rule: bb1(_2) ∧ (_10__out == (_2 == 0)) ∧ _10__out → error()
    // This should be unreachable because bb1 only has _2 != 0
    let _10_out = Expr::var("_10__out", Sort::bool());
    let var_2_eq_zero = var_2.clone().eq(zero); // _2 == 0
    let error_def = _10_out.clone().eq(var_2_eq_zero); // _10__out == (_2 == 0)
    let error_rule = Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![var_2])),
            vec![error_def, _10_out], // _10__out == (_2 == 0) AND _10__out
        ),
        RelationApp::nullary("error"),
    );
    vc.add_rule(error_rule);

    // Query error reachability
    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Debug: print the generated SMT-LIB
    eprintln!("Generated SMT-LIB:\n{}", smt);

    // Run AY and verify UNSAT (error unreachable)
    match run_ay_on_smt2(&smt) {
        Ok(result) => {
            assert_eq!(
                result, "unsat",
                "CHC should be UNSAT (error unreachable due to assume constraint). Got: {}. SMT:\n{}",
                result, smt
            );
        }
        Err(e) => panic!("AY execution failed: {}. SMT:\n{}", e, smt),
    }
}
