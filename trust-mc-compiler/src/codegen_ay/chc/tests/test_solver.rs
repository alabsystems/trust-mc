// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Solver-invocation tests for CHC IR.
//!
//! These tests build CHC verification conditions using the same IR that the
//! CHC codegen produces, emit them to SMT-LIB2 via `emit_chc`, and verify
//! the result by running Z3. This fills the gap identified in #2097: the CHC
//! test suite previously had zero solver invocations — all 202 tests only
//! checked sorts, string content, or IR structure.
//!
//! Each test exercises a specific CHC encoding pattern used by the codegen:
//! - SwitchInt guard encoding (Bool, bitvec)
//! - Frame conditions (unmodified locals)
//! - Assertion violation encoding (SAT: reachable error)
//! - Assume/assert interaction (UNSAT: assume blocks violation)

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use trust_mc_core::{ChcQuery, ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};

// =============================================================================
// Solver-invocation tests for CHC encoding patterns
// =============================================================================

/// Test that switchint_case_guard produces correct Bool guards via the solver.
///
/// Encodes: entry → bb0(b) with unconstrained Bool b, then:
///   bb0(b) ∧ guard(b, case=0) → bb_false(b)   [guard = NOT b]
///   bb0(b) ∧ guard(b, case=1) → bb_true(b)     [guard = b]
///   bb_true(b) ∧ NOT b → error()
///
/// If the guard is correct, bb_true only has b=true, so NOT b is false there.
/// Error should be UNSAT.
#[test]
fn test_switchint_bool_guard_correctness_via_solver() {
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("b", Sort::bool()));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bool()]));
    vc.add_relation(RelationDecl::new("bb_true", vec![Sort::bool()]));
    vc.add_relation(RelationDecl::new("bb_false", vec![Sort::bool()]));

    let b = Expr::var("b", Sort::bool());

    // Entry: true → bb0(b)
    vc.add_rule(Rule::init(Expr::bool_const(true), RelationApp::new("bb0", vec![b.clone()])));

    // Use the actual switchint_case_guard function
    let guard_false = ChcCtx::switchint_case_guard(&b, 0, 0).unwrap(); // NOT b
    let guard_true = ChcCtx::switchint_case_guard(&b, 1, 0).unwrap(); // b

    // bb0(b) ∧ guard(case=0) → bb_false(b)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![b.clone()])), vec![guard_false]),
        RelationApp::new("bb_false", vec![b.clone()]),
    ));

    // bb0(b) ∧ guard(case=1) → bb_true(b)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![b.clone()])), vec![guard_true]),
        RelationApp::new("bb_true", vec![b.clone()]),
    ));

    // Error: bb_true(b) ∧ NOT b → error()
    // This should be unreachable because bb_true only has b=true
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb_true", vec![b.clone()])), vec![b.not()]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    assert_z3_result(&smt, "unsat");
}

/// Test that bitvec switchint guard produces correct equality check.
///
/// Encodes a match on u32 discriminant with case_val=42:
///   entry → bb0(x)
///   bb0(x) ∧ (x == 42) → bb_match(x)
///   bb_match(x) ∧ (x != 42) → error()
///
/// Error should be UNSAT because bb_match only has x=42.
#[test]
fn test_switchint_bitvec_guard_correctness_via_solver() {
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("x", Sort::bitvec(32)));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(32)]));
    vc.add_relation(RelationDecl::new("bb_match", vec![Sort::bitvec(32)]));

    let x = Expr::var("x", Sort::bitvec(32));

    // Entry: true → bb0(x)
    vc.add_rule(Rule::init(Expr::bool_const(true), RelationApp::new("bb0", vec![x.clone()])));

    // Use the actual switchint_case_guard function for case_val=42
    let guard_42 = ChcCtx::switchint_case_guard(&x, 42, 0).unwrap();

    // bb0(x) ∧ guard(case=42) → bb_match(x)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone()])), vec![guard_42]),
        RelationApp::new("bb_match", vec![x.clone()]),
    ));

    // Error: bb_match(x) ∧ (x != 42) → error()
    let forty_two = Expr::bitvec_const(42u64, 32);
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb_match", vec![x.clone()])),
            vec![x.eq(forty_two).not()],
        ),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    assert_z3_result(&smt, "unsat");
}

/// Test that frame conditions correctly propagate unmodified state.
///
/// Encodes a function with two locals (x, y) where only y is modified:
///   entry → bb0(x, y)    with x=10, y=0
///   bb0(x, y) ∧ (x'=x) ∧ (y'=y+1) → bb1(x', y')   [frame: x'=x]
///   bb1(x, y) ∧ (x != 10) → error()
///
/// If the frame condition is correct, x is always 10 in bb1.
/// Error should be UNSAT.
#[test]
fn test_frame_condition_preserves_state_via_solver() {
    let mut vc = ChcVc::new();

    let state_sorts = vec![Sort::bitvec(32), Sort::bitvec(32)];
    vc.add_var(VarDecl::new("x", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("y", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("x_out", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("y_out", Sort::bitvec(32)));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", state_sorts.clone()));
    vc.add_relation(RelationDecl::new("bb1", state_sorts));

    let x = Expr::var("x", Sort::bitvec(32));
    let y = Expr::var("y", Sort::bitvec(32));
    let x_out = Expr::var("x_out", Sort::bitvec(32));
    let y_out = Expr::var("y_out", Sort::bitvec(32));

    // Entry: x=10 ∧ y=0 → bb0(x, y)
    let ten = Expr::bitvec_const(10u64, 32);
    let zero = Expr::bitvec_const(0u64, 32);
    let one = Expr::bitvec_const(1u64, 32);
    vc.add_rule(Rule::init(
        x.clone().eq(ten.clone()).and(y.clone().eq(zero)),
        RelationApp::new("bb0", vec![x.clone(), y.clone()]),
    ));

    // Transition: bb0(x, y) ∧ (x_out=x) ∧ (y_out=y+1) → bb1(x_out, y_out)
    // Frame condition: x_out=x (x is unmodified)
    // Modified: y_out = y + 1
    let frame_x = x_out.clone().eq(x.clone());
    let modify_y = y_out.clone().eq(y.clone().bvadd(one));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone(), y.clone()])),
            vec![frame_x, modify_y],
        ),
        RelationApp::new("bb1", vec![x_out, y_out]),
    ));

    // Error: bb1(x, y) ∧ (x != 10) → error()
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![x.clone(), y])), vec![x.eq(ten).not()]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    assert_z3_result(&smt, "unsat");
}

/// Test that assertion violation encoding correctly detects failing assertions.
///
/// Encodes kani::assert(x > 0) with unconstrained x:
///   entry → bb0(x)
///   bb0(x) ∧ NOT(x > 0) → error()
///
/// Error IS reachable (x=0 satisfies the violation). Z3 should report SAT.
#[test]
fn test_assertion_violation_reachable_via_solver() {
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("x", Sort::bitvec(32)));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(32)]));

    let x = Expr::var("x", Sort::bitvec(32));

    // Entry: true → bb0(x) with unconstrained x
    vc.add_rule(Rule::init(Expr::bool_const(true), RelationApp::new("bb0", vec![x.clone()])));

    // Error: bb0(x) ∧ NOT(x >u 0) → error()
    // Violation condition: x is NOT greater than 0 (unsigned)
    let zero = Expr::bitvec_const(0u64, 32);
    let x_gt_zero = x.clone().bvugt(zero);
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x])), vec![x_gt_zero.not()]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    assert_z3_result(&smt, "sat");
}

/// Test that assume + assert interaction works correctly in CHC encoding.
///
/// Encodes:
///   assume(x != 0);  // blocks x=0
///   assert(x != 0);  // should pass
///
/// Structure:
///   entry → bb0(x)
///   bb0(x) ∧ (x != 0) → bb1(x)        [assume]
///   bb1(x) ∧ NOT(x != 0) → error()     [assert violation]
///
/// Error should be UNSAT because assume blocks the path where x=0.
#[test]
fn test_assume_blocks_assertion_violation_via_solver() {
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("x", Sort::bitvec(32)));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(32)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(32)]));

    let x = Expr::var("x", Sort::bitvec(32));
    let zero = Expr::bitvec_const(0u64, 32);
    let x_ne_zero = x.clone().eq(zero).not();

    // Entry: true → bb0(x)
    vc.add_rule(Rule::init(Expr::bool_const(true), RelationApp::new("bb0", vec![x.clone()])));

    // Assume: bb0(x) ∧ (x != 0) → bb1(x)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone()])), vec![x_ne_zero.clone()]),
        RelationApp::new("bb1", vec![x.clone()]),
    ));

    // Assert violation: bb1(x) ∧ NOT(x != 0) → error()
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![x])), vec![x_ne_zero.not()]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    assert_z3_result(&smt, "unsat");
}
