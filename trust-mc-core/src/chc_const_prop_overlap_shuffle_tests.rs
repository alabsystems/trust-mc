// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! P4-1 regression: constant propagation across a cross-slot scalar shuffle
//! (the scalarized form of an overlapping `copy`: `slot1' = slot0`,
//! `slot2' = slot1`) must not evaluate the downstream error edge against the
//! PRE-shuffle values. Observed as a false PROOF of a refutable assertion
//! after the legal-overlap `copy` disjointness FP was removed (the FP had
//! masked the mis-propagation).

use ay_bindings::{Expr, Sort};

use crate::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody};

use super::propagate_constants;

fn bv32(val: i64) -> Expr {
    Expr::bitvec_const(val, 32)
}

fn bv32_var(name: &str) -> Expr {
    Expr::var(name, Sort::bitvec(32))
}

/// entry → bb2(0, 1, 0);
/// bb2(s0,s1,s2) ∧ s0'=s0 ∧ s1'=s0 ∧ s2'=s1 → bb3(s0',s1',s2');
/// bb3(s0,s1,s2) ∧ ¬(s1 = 1) → error.
///
/// Real post-shuffle state: (0, 0, 1) — s1 = 0 ≠ 1, so the error edge is
/// REACHABLE and must survive constant propagation.
#[test]
fn test_cross_slot_shuffle_keeps_reachable_error_edge() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::nullary("entry"));
    vc.add_relation(RelationDecl::new(
        "bb2",
        vec![Sort::bitvec(32), Sort::bitvec(32), Sort::bitvec(32)],
    ));
    vc.add_relation(RelationDecl::new(
        "bb3",
        vec![Sort::bitvec(32), Sort::bitvec(32), Sort::bitvec(32)],
    ));
    vc.add_relation(RelationDecl::nullary("error"));

    // entry → bb2(0, 1, 0)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb2", vec![bv32(0), bv32(1), bv32(0)]),
    ));

    // bb2(s0,s1,s2) ∧ shuffle → bb3(s0__out, s1__out, s2__out)
    let s0 = bv32_var("s0");
    let s1 = bv32_var("s1");
    let s2 = bv32_var("s2");
    let s0_out = bv32_var("s0__out");
    let s1_out = bv32_var("s1__out");
    let s2_out = bv32_var("s2__out");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb2", vec![s0.clone(), s1.clone(), s2.clone()])),
            vec![
                s0_out.clone().eq(s0.clone()),
                s1_out.clone().eq(s0.clone()),
                s2_out.clone().eq(s1.clone()),
            ],
        ),
        RelationApp::new("bb3", vec![s0_out, s1_out, s2_out]),
    ));

    // bb3(s0,s1,s2) ∧ ¬(s1 = 1) → error
    let t0 = bv32_var("s0");
    let t1 = bv32_var("s1");
    let t2 = bv32_var("s2");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb3", vec![t0, t1.clone(), t2])),
            vec![t1.eq(bv32(1)).not()],
        ),
        RelationApp::nullary("error"),
    ));

    propagate_constants(&mut vc);

    // The REAL bb3 state is (0, 0, 1): the error premise ¬(s1=1) is TRUE.
    // The error rule must still exist and must not carry a `false` conjunct.
    let error_rule = vc
        .rules
        .iter()
        .find(|r| r.head.name.as_str() == "error")
        .expect("reachable error rule must survive constant propagation");
    let has_false = error_rule
        .body
        .constraints
        .iter()
        .any(|c| matches!(c.value(), ay_bindings::ExprValue::BoolConst(false)));
    assert!(
        !has_false,
        "error rule premise mis-folded to false: const-prop evaluated the \
         cross-slot shuffle against pre-shuffle values: {:?}",
        error_rule.body.constraints
    );
}
