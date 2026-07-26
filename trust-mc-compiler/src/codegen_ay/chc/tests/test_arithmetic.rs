// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

/// Read Z3 timeout with optional environment override for slower environments.
fn z3_test_timeout_secs() -> u64 {
    z3_test_timeout_secs_or(Z3_TEST_TIMEOUT_SECS)
}

fn assert_z3_result(smt: &str, expected: &str) {
    assert_z3_result_with_timeout(smt, expected, z3_test_timeout_secs());
}

// ===== Production function tests =====
// Trivial ay_bindings-only tests deleted per #2391 / rule #2312.
// Kept: tests that call CHC codegen production functions.

#[test]
fn test_bitwise_operand_coercion_signed_uses_sign_extend() {
    // Bitwise ops should use sign extension for signed operands when widths differ.
    let lhs = Expr::bitvec_const(-1i128, 8);
    let rhs = Expr::bitvec_const(0x0fu128, 16);

    let (lhs_coerced, rhs_coerced) = ChcCtx::coerce_bitwise_operands(lhs, rhs, true);

    assert_eq!(lhs_coerced.sort().bitvec_width(), Some(16));
    assert_eq!(rhs_coerced.sort().bitvec_width(), Some(16));
    assert!(lhs_coerced.to_string().contains("sign_extend"));
}

#[test]
fn test_bitwise_operand_coercion_unsigned_uses_zero_extend() {
    // Bitwise ops should use zero extension for unsigned operands when widths differ.
    let lhs = Expr::bitvec_const(0xffu128, 8);
    let rhs = Expr::bitvec_const(0x0fu128, 16);

    let (lhs_coerced, rhs_coerced) = ChcCtx::coerce_bitwise_operands(lhs, rhs, false);

    assert_eq!(lhs_coerced.sort().bitvec_width(), Some(16));
    assert_eq!(rhs_coerced.sort().bitvec_width(), Some(16));
    assert!(lhs_coerced.to_string().contains("zero_extend"));
}

// test_undef_counter_generates_unique_names DELETED per #2391 / rule #2312:
// Only tested AtomicU64::fetch_add (std library guarantee), not a production function.

// ===== Solver-Backed Arithmetic Semantics Tests =====

#[test]
fn test_bvadd_constant_semantics_via_solver() {
    // Build a CHC program that computes 2 + 3 and asserts result == 5.
    // If bvadd encoding is semantically wrong, error becomes reachable (SAT).
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("x", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("y", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("sum", Sort::bitvec(32)));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(32), Sort::bitvec(32)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(32)]));

    let x = Expr::var("x", Sort::bitvec(32));
    let y = Expr::var("y", Sort::bitvec(32));
    let sum = Expr::var("sum", Sort::bitvec(32));

    let two = Expr::bitvec_const(2u64, 32);
    let three = Expr::bitvec_const(3u64, 32);
    let five = Expr::bitvec_const(5u64, 32);

    // Entry: x=2 ∧ y=3 → bb0(x, y)
    vc.add_rule(Rule::init(
        x.clone().eq(two).and(y.clone().eq(three)),
        RelationApp::new("bb0", vec![x.clone(), y.clone()]),
    ));

    // Transition: bb0(x, y) ∧ sum=(x+y) → bb1(sum)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone(), y.clone()])),
            vec![sum.clone().eq(x.bvadd(y))],
        ),
        RelationApp::new("bb1", vec![sum.clone()]),
    ));

    // Error: bb1(sum) ∧ sum!=5 → error()
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![sum.clone()])), vec![sum.eq(five).not()]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let smt = emit_chc(&vc).to_string();
    assert_z3_result(&smt, "unsat");
}

#[test]
fn test_bvsdiv_signed_semantics_via_solver() {
    // Build a CHC program that computes (-8) / 2 using signed division and
    // asserts the result is -4. This catches signed/unsigned mismatch bugs.
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("x", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("y", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("quot", Sort::bitvec(32)));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(32), Sort::bitvec(32)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(32)]));

    let x = Expr::var("x", Sort::bitvec(32));
    let y = Expr::var("y", Sort::bitvec(32));
    let quot = Expr::var("quot", Sort::bitvec(32));

    let neg_eight = Expr::bitvec_const(0xFFFF_FFF8u64, 32); // -8 as i32
    let two = Expr::bitvec_const(2u64, 32);
    let neg_four = Expr::bitvec_const(0xFFFF_FFFCu64, 32); // -4 as i32

    // Entry: x=-8 ∧ y=2 → bb0(x, y)
    vc.add_rule(Rule::init(
        x.clone().eq(neg_eight).and(y.clone().eq(two)),
        RelationApp::new("bb0", vec![x.clone(), y.clone()]),
    ));

    // Transition: bb0(x, y) ∧ quot=(x bvsdiv y) → bb1(quot)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone(), y.clone()])),
            vec![quot.clone().eq(x.bvsdiv(y))],
        ),
        RelationApp::new("bb1", vec![quot.clone()]),
    ));

    // Error: bb1(quot) ∧ quot!=-4 → error()
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![quot.clone()])),
            vec![quot.eq(neg_four).not()],
        ),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let smt = emit_chc(&vc).to_string();
    assert_z3_result(&smt, "unsat");
}
