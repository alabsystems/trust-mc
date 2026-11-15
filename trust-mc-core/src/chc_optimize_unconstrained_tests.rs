// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for the exact projection of unconstrained relation arguments.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};

use crate::chc::{ChcQuery, ChcVc, RelationApp, RelationDecl, Rule, RuleBody};

fn arity(vc: &ChcVc, name: &str) -> usize {
    vc.relations.iter().find(|r| r.name == name).map(RelationDecl::arity).expect("relation")
}

fn app_len(vc: &ChcVc, head: &str) -> Vec<usize> {
    let mut lens: Vec<usize> = Vec::new();
    for rule in &vc.rules {
        if &*rule.head.name == head {
            lens.push(rule.head.args.len());
        }
        if let Some(body) = &rule.body.relation
            && &*body.name == head
        {
            lens.push(body.args.len());
        }
    }
    lens
}

fn var_names(vc: &ChcVc) -> HashSet<String> {
    vc.vars().iter().map(|v| v.name.to_string()).collect()
}

fn error_query(vc: &mut ChcVc) {
    vc.add_relation(RelationDecl::nullary("error"));
    vc.query = ChcQuery::new().with_target("error");
}

/// `bb0(x, y) => bb1(x, y)`, `bb1(x, y) ∧ x < 0 => error`: `y` is forwarded but
/// never read, so both of its columns go; `x` is read by the error edge.
#[test]
fn forwarded_but_unread_column_is_projected() {
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", Sort::int());
    let y = vc.declare_var("y", Sort::int());
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int(), Sort::int()]));
    error_query(&mut vc);
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![x.clone().eq(Expr::int_const(0))]),
        RelationApp::new("bb0", vec![x.clone(), y.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone(), y.clone()])), vec![]),
        RelationApp::new("bb1", vec![x.clone(), y.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![x.clone(), y.clone()])),
            vec![x.clone().int_lt(Expr::int_const(0))],
        ),
        RelationApp::nullary("error"),
    ));

    assert_eq!(vc.prune_unconstrained_relation_args(), 2);
    assert_eq!(arity(&vc, "bb0"), 1);
    assert_eq!(arity(&vc, "bb1"), 1);
    assert_eq!(app_len(&vc, "bb0"), vec![1, 1]);
    assert_eq!(app_len(&vc, "bb1"), vec![1, 1]);
    // Every surviving application carries `x`.
    for rule in &vc.rules {
        for app in std::iter::once(&rule.head).chain(rule.body.relation.iter()) {
            for arg in app.args.iter() {
                assert_eq!(arg, &x);
            }
        }
    }
    // The stale declare-var goes with its columns; `x` stays.
    assert_eq!(var_names(&vc), HashSet::from(["x".to_string()]));
    // Idempotent.
    assert_eq!(vc.prune_unconstrained_relation_args(), 0);
}

/// A column read three relays downstream stays live through every relay.
#[test]
fn downstream_read_keeps_every_relay_live() {
    let mut vc = ChcVc::new();
    let a = vc.declare_var("a", Sort::int());
    for name in ["bb0", "bb1", "bb2", "bb3"] {
        vc.add_relation(RelationDecl::new(name, vec![Sort::int()]));
    }
    error_query(&mut vc);
    vc.add_rule(Rule::new(RuleBody::new(None, vec![]), RelationApp::new("bb0", vec![a.clone()])));
    for (from, to) in [("bb0", "bb1"), ("bb1", "bb2"), ("bb2", "bb3")] {
        vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::new(from, vec![a.clone()])), vec![]),
            RelationApp::new(to, vec![a.clone()]),
        ));
    }
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb3", vec![a.clone()])),
            vec![a.clone().eq(Expr::int_const(5))],
        ),
        RelationApp::nullary("error"),
    ));

    assert_eq!(vc.prune_unconstrained_relation_args(), 0);
    for name in ["bb0", "bb1", "bb2", "bb3"] {
        assert_eq!(arity(&vc, name), 1);
    }
}

/// `bb0(x, y) ∧ y = 0 => bb1(x)` with `bb1` never read: `y` is read by the
/// constraint (kept), `x` only defines an unread column (both go).
#[test]
fn constraint_occurrence_reads_the_column() {
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", Sort::int());
    let y = vc.declare_var("y", Sort::int());
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int()]));
    error_query(&mut vc);
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone(), y.clone()])),
            vec![y.clone().eq(Expr::int_const(0))],
        ),
        RelationApp::new("bb1", vec![x.clone()]),
    ));

    assert_eq!(vc.prune_unconstrained_relation_args(), 2);
    assert_eq!(arity(&vc, "bb0"), 1);
    assert_eq!(arity(&vc, "bb1"), 0);
    let body = vc.rules[0].body.relation.as_ref().expect("body app");
    assert_eq!(body.args.as_slice(), &[y.clone()]);
    assert!(vc.rules[0].head.args.is_empty());
}

/// `bb0(x, x)`: one variable at two body positions is an implicit equality,
/// so both columns are read.
#[test]
fn repeated_body_variable_is_an_implicit_equality() {
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", Sort::int());
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    error_query(&mut vc);
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone(), x.clone()])), vec![]),
        RelationApp::nullary("error"),
    ));

    assert_eq!(vc.prune_unconstrained_relation_args(), 0);
    assert_eq!(arity(&vc, "bb0"), 2);
}

/// A constant or compound body argument tests the column; a bare variable
/// beside it that nothing reads still goes.
#[test]
fn non_variable_body_argument_reads_the_column() {
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", Sort::int());
    let z = vc.declare_var("z", Sort::int());
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int(), Sort::int()]));
    error_query(&mut vc);
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new(
                "bb0",
                vec![x.clone(), Expr::int_const(5), z.clone().int_add(Expr::int_const(1))],
            )),
            vec![],
        ),
        RelationApp::nullary("error"),
    ));

    assert_eq!(vc.prune_unconstrained_relation_args(), 1);
    assert_eq!(arity(&vc, "bb0"), 2);
    let body = vc.rules[0].body.relation.as_ref().expect("body app");
    assert_eq!(body.args.len(), 2);
    assert_eq!(body.args[0], Expr::int_const(5));
}

/// `bb0(x, y) => bb1(x + y)` with `bb1`'s column read: both inputs feed a
/// live head position, so both stay.
#[test]
fn variables_inside_a_live_compound_head_argument_are_needed() {
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", Sort::int());
    let y = vc.declare_var("y", Sort::int());
    let z = vc.declare_var("z", Sort::int());
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int()]));
    error_query(&mut vc);
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone(), y.clone()])), vec![]),
        RelationApp::new("bb1", vec![x.clone().int_add(y.clone())]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![z.clone()])),
            vec![z.clone().int_lt(Expr::int_const(0))],
        ),
        RelationApp::nullary("error"),
    ));

    assert_eq!(vc.prune_unconstrained_relation_args(), 0);
    assert_eq!(arity(&vc, "bb0"), 2);
}

/// A head position nobody reads is projected even when its argument is a
/// compound term over live inputs.
#[test]
fn unread_compound_head_argument_is_projected() {
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", Sort::int());
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int(), Sort::int()]));
    error_query(&mut vc);
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone()])), vec![]),
        RelationApp::new("bb1", vec![x.clone(), x.clone().int_add(Expr::int_const(1))]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![x.clone(), Expr::int_const(9)])),
            vec![x.clone().eq(Expr::int_const(3))],
        ),
        RelationApp::nullary("error"),
    ));

    // Nothing is projected: position 0 is read by the guard, position 1 by
    // the constant `9` in the body application.
    assert_eq!(vc.prune_unconstrained_relation_args(), 0);
}

/// A symbol that is not a declared rule variable (a `declare-const`) is not a
/// bare variable: it tests the column.
#[test]
fn undeclared_symbol_argument_anchors_its_column() {
    let mut vc = ChcVc::new();
    let c = Expr::var("c", Sort::int());
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));
    error_query(&mut vc);
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![c.clone()])), vec![]),
        RelationApp::nullary("error"),
    ));

    assert_eq!(vc.prune_unconstrained_relation_args(), 0);
    assert_eq!(arity(&vc, "bb0"), 1);
}

/// A relation applied inside a constraint expression is read through a
/// channel the analysis does not model: every position of it is kept.
#[test]
fn relation_embedded_in_a_constraint_keeps_every_position() {
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", Sort::int());
    let y = vc.declare_var("y", Sort::int());
    vc.add_relation(RelationDecl::new("summary", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));
    error_query(&mut vc);
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![]),
        RelationApp::new("summary", vec![x.clone(), y.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![Expr::func_app("summary", vec![x.clone(), y.clone()])],
        ),
        RelationApp::nullary("error"),
    ));

    assert_eq!(vc.prune_unconstrained_relation_args(), 0);
    assert_eq!(arity(&vc, "summary"), 2);
    assert_eq!(arity(&vc, "bb0"), 1);
}

/// An application whose arity disagrees with the declaration protects the
/// whole relation (fail closed) instead of being reshaped.
#[test]
fn arity_mismatch_protects_the_relation() {
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", Sort::int());
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    error_query(&mut vc);
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone()])), vec![]),
        RelationApp::nullary("error"),
    ));

    assert_eq!(vc.prune_unconstrained_relation_args(), 0);
    assert_eq!(arity(&vc, "bb0"), 2);
    assert_eq!(app_len(&vc, "bb0"), vec![1]);
}

/// A variable a cover assertion mentions is read.
#[test]
fn cover_assertion_variable_is_read() {
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", Sort::int());
    let y = vc.declare_var("y", Sort::int());
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    error_query(&mut vc);
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone(), y.clone()])), vec![]),
        RelationApp::nullary("error"),
    ));
    vc.add_cover_assertion("cover_0".to_string(), y.clone().eq(Expr::int_const(1)));

    assert_eq!(vc.prune_unconstrained_relation_args(), 1);
    assert_eq!(arity(&vc, "bb0"), 1);
    assert_eq!(vc.rules[0].body.relation.as_ref().expect("body").args.as_slice(), &[y.clone()]);
    assert!(var_names(&vc).contains("y"));
}

/// A declared relation no rule mentions is left exactly as declared.
#[test]
fn unused_relation_is_left_alone() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("orphan", vec![Sort::int(), Sort::bool()]));
    error_query(&mut vc);
    assert_eq!(vc.prune_unconstrained_relation_args(), 0);
    assert_eq!(arity(&vc, "orphan"), 2);
}

/// A relation only ever used as a head with nothing reading it loses every
/// column; the constraint that defined the column is untouched.
#[test]
fn head_only_relation_is_projected_to_nullary() {
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", Sort::int());
    let y = vc.declare_var("y", Sort::int());
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    error_query(&mut vc);
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![x.clone().eq(Expr::int_const(1))]),
        RelationApp::new("bb0", vec![x.clone(), y.clone()]),
    ));

    assert_eq!(vc.prune_unconstrained_relation_args(), 2);
    assert_eq!(arity(&vc, "bb0"), 0);
    assert!(vc.rules[0].head.args.is_empty());
    assert_eq!(vc.rules[0].body.constraints.len(), 1);
    assert_eq!(var_names(&vc), HashSet::from(["x".to_string()]));
}

/// The query target keeps its (nullary) shape and a fresh VC is a no-op.
#[test]
fn empty_vc_is_a_no_op() {
    let mut vc = ChcVc::new();
    error_query(&mut vc);
    assert_eq!(vc.prune_unconstrained_relation_args(), 0);
}
