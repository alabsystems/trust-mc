// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for dead-argument elimination (`chc_optimize`).

use super::*;
use crate::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};
use ay_bindings::Sort;
use ay_bindings::expr::RoundingMode;

#[path = "chc_optimize_dead_scalar_array_tests.rs"]
mod dead_scalar_array_tests;

#[test]
fn test_var_eq_var_classified_as_transfer() {
    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let eq = Expr::eq(x, y);

    let mut anchored = HashSet::new();
    let mut transfers = Vec::new();
    classify_constraint(&eq, &mut anchored, &mut transfers);
    // Variable-to-variable equality is a transfer — no anchored variables.
    assert!(anchored.is_empty());
    assert_eq!(transfers.len(), 1);
    assert_eq!(transfers[0], ("x".to_string(), "y".to_string()));
}

#[test]
fn test_real_constraint_anchors_vars() {
    let x = Expr::var("x", Sort::int());
    let one = Expr::int_const(1);
    let comparison = x.int_lt(one);

    let mut anchored = HashSet::new();
    let mut transfers = Vec::new();
    classify_constraint(&comparison, &mut anchored, &mut transfers);
    assert!(anchored.contains("x"));
    assert!(transfers.is_empty());
}

#[test]
fn test_eq_var_const_anchors_var() {
    // (= x 0) is NOT a transfer — one side is a constant.
    let x = Expr::var("x", Sort::int());
    let eq = Expr::eq(x, Expr::int_const(0));

    let mut anchored = HashSet::new();
    let mut transfers = Vec::new();
    classify_constraint(&eq, &mut anchored, &mut transfers);
    assert!(anchored.contains("x"), "(= Var Const) should anchor Var");
    assert!(transfers.is_empty());
}

#[test]
fn test_prune_dead_identity_scalars_keeps_nonidentity_reads() {
    let mut vc = ChcVc::new();
    for name in ["x", "x__out"] {
        vc.add_var(VarDecl::new(name, Sort::int()));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));

    let x = Expr::var("x", Sort::int());
    let x_out = Expr::var("x__out", Sort::int());
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![Expr::eq(x_out.clone(), x.clone()), x.int_gt(Expr::int_const(0))],
        ),
        RelationApp::new("bb0", vec![x_out]),
    ));

    assert_eq!(vc.prune_dead_identity_scalars(), 0);
    assert_eq!(vc.relations[0].arity(), 1);
    assert_eq!(vc.rules[0].body.relation.as_ref().expect("bb0").args.len(), 1);
    assert_eq!(vc.rules[0].head.args.len(), 1);
}

#[test]
fn test_strip_dead_args_basic() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("y", Sort::int()));
    vc.add_var(VarDecl::new("dead", Sort::int()));

    // Relation with 3 args: x, y, dead
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let dead = Expr::var("dead", Sort::int());

    // Init rule: x=0, y=0, dead=0 → bb0(x, y, dead)
    let head = RelationApp::new("bb0", vec![x.clone(), y.clone(), dead.clone()]);
    let init_constraint = Expr::eq(x.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_constraint, head));

    // Transition: bb0(x, y, dead) ∧ x < 10 → bb0(x+1, y, dead)
    // Only x and y are in real constraints; dead is identity-copied.
    let from = RelationApp::new("bb0", vec![x.clone(), y.clone(), dead.clone()]);
    let x_next = Expr::var("x_next", Sort::int());
    vc.add_var(VarDecl::new("x_next", Sort::int()));

    let guard = x.clone().int_lt(Expr::int_const(10));
    let transition = Expr::eq(x_next.clone(), x.clone().int_add(Expr::int_const(1)));
    // Identity copy for dead — this should be detected and stripped.
    let dead_copy = Expr::eq(dead.clone(), dead.clone());

    let to = RelationApp::new("bb0", vec![x_next, y.clone(), dead.clone()]);
    let body = RuleBody::new(Some(from), vec![guard, transition, dead_copy]);
    vc.add_rule(Rule::new(body, to));

    // Error rule: bb0(x, y, dead) ∧ y > 100 → error
    let from2 = RelationApp::new("bb0", vec![x, y.clone(), dead]);
    let violation = y.int_gt(Expr::int_const(100));
    let error_head = RelationApp::nullary("error");
    let body2 = RuleBody::new(Some(from2), vec![violation]);
    vc.add_rule(Rule::new(body2, error_head));

    // Strip dead args
    let stripped = vc.strip_dead_args();
    assert_eq!(stripped, 1, "should strip 1 dead arg (dead)");

    // Verify bb0 now has 2 args instead of 3.
    let bb0_rel = vc.relations.iter().find(|r| r.name == "bb0").expect("bb0");
    assert_eq!(bb0_rel.arity(), 2);

    // Verify all RelationApp references have 2 args.
    for rule in &vc.rules {
        if rule.head.name == "bb0" {
            assert_eq!(rule.head.args.len(), 2, "head args should be stripped");
        }
        if let Some(ref rel) = rule.body.relation {
            if rel.name == "bb0" {
                assert_eq!(rel.args.len(), 2, "body rel args should be stripped");
            }
        }
    }
}

#[test]
fn test_no_dead_args_returns_zero() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));

    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let x = Expr::var("x", Sort::int());

    let head = RelationApp::new("bb0", vec![x.clone()]);
    let constraint = Expr::eq(x.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(constraint, head));

    let from = RelationApp::new("bb0", vec![x.clone()]);
    let guard = x.int_lt(Expr::int_const(10));
    let error_head = RelationApp::nullary("error");
    vc.add_rule(Rule::new(RuleBody::new(Some(from), vec![guard]), error_head));

    let stripped = vc.strip_dead_args();
    assert_eq!(stripped, 0);
}

#[test]
fn test_collect_var_names_nested() {
    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let nested = x.int_add(y).int_lt(Expr::int_const(10));

    let mut vars = HashSet::new();
    collect_var_names(&nested, &mut vars);
    assert!(vars.contains("x"));
    assert!(vars.contains("y"));
    assert_eq!(vars.len(), 2);
}

#[test]
fn test_collect_var_names_array_ops() {
    let arr = Expr::var("arr", Sort::array(Sort::int(), Sort::int()));
    let idx = Expr::var("idx", Sort::int());
    let val = Expr::var("val", Sort::int());

    let store = Expr::store(arr, idx, val);
    let mut vars = HashSet::new();
    collect_var_names(&store, &mut vars);
    assert_eq!(vars.len(), 3);
    assert!(vars.contains("arr"));
    assert!(vars.contains("idx"));
    assert!(vars.contains("val"));
}

/// Regression test: __out variables must not be falsely dead.
///
/// Head args use `x__out`; body constraints reference `x` (without suffix).
/// The identity copy `(= y y__out)` is a transfer edge in the variable graph.
/// Since `y` is anchored (used in `y > 100`), position-based liveness checks
/// all names at each position — `y` at position 1 in the body keeps the
/// position live even though `y__out` at position 1 in the head is not
/// directly anchored.
#[test]
fn test_out_suffix_not_falsely_dead() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("x__out", Sort::int()));
    vc.add_var(VarDecl::new("y", Sort::int()));
    vc.add_var(VarDecl::new("y__out", Sort::int()));

    // Relation bb0 with 2 args.
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let x = Expr::var("x", Sort::int());
    let x_out = Expr::var("x__out", Sort::int());
    let y = Expr::var("y", Sort::int());
    let y_out = Expr::var("y__out", Sort::int());

    // Init rule: x__out=0, y__out=0 → bb0(x__out, y__out)
    let head = RelationApp::new("bb0", vec![x_out.clone(), y_out.clone()]);
    let init_c = Expr::eq(x_out.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_c, head));

    // Transition: bb0(x, y) ∧ x<10 ∧ x__out=x+1 ∧ (= y y__out) → bb0(x__out, y__out)
    // y__out appears ONLY in identity copy — but y (at the same position in
    // the body) is anchored by the error rule, so position-based liveness
    // keeps this position.
    let from = RelationApp::new("bb0", vec![x.clone(), y.clone()]);
    let guard = x.clone().int_lt(Expr::int_const(10));
    let step = Expr::eq(x_out.clone(), x.clone().int_add(Expr::int_const(1)));
    let y_identity = Expr::eq(y.clone(), y_out.clone()); // identity copy
    let to = RelationApp::new("bb0", vec![x_out, y_out]);
    let body = RuleBody::new(Some(from), vec![guard, step, y_identity]);
    vc.add_rule(Rule::new(body, to));

    // Error rule: bb0(x, y) ∧ y > 100 → error
    // Uses `y` (base name) in a real constraint.
    let from2 = RelationApp::new("bb0", vec![x, y.clone()]);
    let violation = y.int_gt(Expr::int_const(100));
    let error_head = RelationApp::nullary("error");
    vc.add_rule(Rule::new(RuleBody::new(Some(from2), vec![violation]), error_head));

    let stripped = vc.strip_dead_args();
    // y__out should NOT be stripped — position-based: y at same position is anchored.
    assert_eq!(stripped, 0, "no args should be dead — y at position 1 is anchored");

    let bb0_rel = vc.relations.iter().find(|r| r.name == "bb0").expect("bb0");
    assert_eq!(bb0_rel.arity(), 2, "bb0 should keep both args");
}

/// Test that cross-variable value transfers with unanchored base are kept
/// when BFS-reachable from an anchored variable.
///
/// `(= y__out x)` where y ≠ x and y is NOT anchored: y__out is BFS-reachable
/// from x through the transfer edge. Position-based liveness sees y__out in the
/// reachable set → position 1 is live → not stripped. This is conservative but
/// prevents cross-block struct field losses (see module docs "Why no dead-end
/// pruning").
#[test]
fn test_cross_var_transfer_unanchored_base_kept_conservative() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("y__out", Sort::int()));

    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let x = Expr::var("x", Sort::int());
    let y_out = Expr::var("y__out", Sort::int());

    // Init rule
    let head = RelationApp::new("bb0", vec![x.clone(), y_out.clone()]);
    let init_c = Expr::eq(x.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_c, head));

    // Transition: bb0(x, _) ∧ x<10 ∧ (= y__out x) → bb0(x+1, y__out)
    // Cross-variable transfer: y__out gets value from x. BFS reaches y__out
    // from x, so position is conservatively kept.
    let from = RelationApp::new("bb0", vec![x.clone(), Expr::var("y", Sort::int())]);
    let guard = x.clone().int_lt(Expr::int_const(10));
    let transfer = Expr::eq(y_out.clone(), x.clone());
    let to = RelationApp::new("bb0", vec![x.clone().int_add(Expr::int_const(1)), y_out]);
    let body = RuleBody::new(Some(from), vec![guard, transfer]);
    vc.add_rule(Rule::new(body, to));

    // Error: x > 100 — only x is used, not y
    let from2 = RelationApp::new("bb0", vec![x.clone(), Expr::var("y", Sort::int())]);
    let violation = x.int_gt(Expr::int_const(100));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(from2), vec![violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.strip_dead_args();
    // Position 1 has {y__out, y}. y__out IS BFS-reachable from x → kept.
    assert_eq!(stripped, 0, "y__out position should be kept — y__out is BFS-reachable from x");
}

/// Test that cross-variable transfers with anchored base are kept.
///
/// `(= y__out x)` where y ≠ x but y IS anchored (used in a real constraint
/// elsewhere): y__out must NOT be stripped — position-based liveness sees
/// that y at position 1 is anchored.
#[test]
fn test_cross_var_transfer_anchored_base_kept() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("y", Sort::int()));
    vc.add_var(VarDecl::new("y__out", Sort::int()));

    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let y_out = Expr::var("y__out", Sort::int());

    // Init rule
    let head = RelationApp::new("bb0", vec![x.clone(), y_out.clone()]);
    let init_c = Expr::eq(x.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_c, head));

    // Transition: bb0(x, y) ∧ x<10 ∧ (= y__out x) → bb0(x+1, y__out)
    // Cross-variable transfer: y__out = x. y IS used in the error rule.
    let from = RelationApp::new("bb0", vec![x.clone(), y.clone()]);
    let guard = x.clone().int_lt(Expr::int_const(10));
    let transfer = Expr::eq(y_out.clone(), x.clone());
    let to = RelationApp::new("bb0", vec![x.clone().int_add(Expr::int_const(1)), y_out]);
    let body = RuleBody::new(Some(from), vec![guard, transfer]);
    vc.add_rule(Rule::new(body, to));

    // Error: y > 100 — y IS anchored
    let from2 = RelationApp::new("bb0", vec![x, y.clone()]);
    let violation = y.int_gt(Expr::int_const(100));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(from2), vec![violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.strip_dead_args();
    // Position 1 has {y__out, y}. y IS anchored → position 1 is live.
    assert_eq!(stripped, 0, "y__out position should be kept — y at same position is anchored");
}

/// Test that unanchored transfer chains with no path to an anchored variable
/// are correctly stripped.
///
/// `(= dead_b dead_a)` connects dead_a and dead_b, but neither is anchored
/// and neither is BFS-reachable from any anchored variable (no transfer edge
/// connects them to the anchored set). Both positions are dead.
#[test]
fn test_unanchored_transfer_chain_stripped() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("live", Sort::int()));
    vc.add_var(VarDecl::new("dead_a", Sort::int()));
    vc.add_var(VarDecl::new("dead_b", Sort::int()));

    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let live = Expr::var("live", Sort::int());
    let dead_a = Expr::var("dead_a", Sort::int());
    let dead_b = Expr::var("dead_b", Sort::int());

    // Init rule
    let head = RelationApp::new("bb0", vec![live.clone(), dead_a.clone(), dead_b.clone()]);
    let init_c = Expr::eq(live.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_c, head));

    // Transition: live < 10, (= dead_b dead_a) — cross-var transfer between dead vars
    let from = RelationApp::new("bb0", vec![live.clone(), dead_a.clone(), dead_b.clone()]);
    let guard = live.clone().int_lt(Expr::int_const(10));
    let dead_transfer = Expr::eq(dead_b.clone(), dead_a.clone());
    let to = RelationApp::new(
        "bb0",
        vec![live.clone().int_add(Expr::int_const(1)), dead_a.clone(), dead_b.clone()],
    );
    let body = RuleBody::new(Some(from), vec![guard, dead_transfer]);
    vc.add_rule(Rule::new(body, to));

    // Error: live > 100
    let from2 = RelationApp::new("bb0", vec![live.clone(), dead_a, dead_b]);
    let violation = live.int_gt(Expr::int_const(100));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(from2), vec![violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.strip_dead_args();
    // dead_a and dead_b have a transfer edge between them but no transfer path
    // to any anchored variable — BFS from {live} never reaches them.
    // Position 1: {dead_a} — not in reachable → dead.
    // Position 2: {dead_b} — not in reachable → dead.
    assert_eq!(stripped, 2, "both dead_a and dead_b should be stripped");

    let bb0_rel = vc.relations.iter().find(|r| r.name == "bb0").expect("bb0");
    assert_eq!(bb0_rel.arity(), 1, "bb0 should only keep 'live'");
}

/// Test that BFS reachability keeps bridge variables.
///
/// Variable `bridge` is not directly anchored but is BFS-reachable from
/// anchored variable `a` through the transfer edge `(= bridge a)`. Since
/// `bridge` is in the reachable set, its position is live and not stripped.
#[test]
fn test_bridge_variable_kept_by_bfs() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("a", Sort::int()));
    vc.add_var(VarDecl::new("bridge", Sort::int()));
    vc.add_var(VarDecl::new("b", Sort::int()));

    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let a = Expr::var("a", Sort::int());
    let bridge = Expr::var("bridge", Sort::int());
    let b = Expr::var("b", Sort::int());

    // Init rule
    let head = RelationApp::new("bb0", vec![a.clone(), bridge.clone(), b.clone()]);
    let init_c = Expr::eq(a.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_c, head));

    // Transition: bb0(a, bridge, b) ∧ a < 10 ∧ (= bridge a) ∧ (= b bridge) → bb0(a+1, bridge, b)
    // `bridge` connects `a` and `b` through two transfer edges.
    let from = RelationApp::new("bb0", vec![a.clone(), bridge.clone(), b.clone()]);
    let guard = a.clone().int_lt(Expr::int_const(10));
    let t1 = Expr::eq(bridge.clone(), a.clone()); // a → bridge
    let t2 = Expr::eq(b.clone(), bridge.clone()); // bridge → b
    let to = RelationApp::new(
        "bb0",
        vec![a.clone().int_add(Expr::int_const(1)), bridge.clone(), b.clone()],
    );
    let body = RuleBody::new(Some(from), vec![guard, t1, t2]);
    vc.add_rule(Rule::new(body, to));

    // Error: b > 100 — b IS anchored
    let from2 = RelationApp::new("bb0", vec![a, bridge, b.clone()]);
    let violation = b.int_gt(Expr::int_const(100));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(from2), vec![violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.strip_dead_args();
    // `bridge` is BFS-reachable from `a` (anchored) through transfer edge →
    // in the reachable set → its position is live.
    assert_eq!(stripped, 0, "bridge should be kept — BFS-reachable from anchored vars");
}

/// Test that __mid_bb<N> bridge variables are kept by BFS reachability.
///
/// `x__mid_bb3` is BFS-reachable from anchored variable `a` via the transfer
/// edge `(= a x__mid_bb3)`. Its position is live.
#[test]
fn test_mid_bb_bridge_kept() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("a", Sort::int()));
    vc.add_var(VarDecl::new("x__mid_bb3", Sort::int()));
    vc.add_var(VarDecl::new("b", Sort::int()));

    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let a = Expr::var("a", Sort::int());
    let x_mid = Expr::var("x__mid_bb3", Sort::int());
    let b = Expr::var("b", Sort::int());

    // Init rule
    let head = RelationApp::new("bb0", vec![a.clone(), x_mid.clone(), b.clone()]);
    let init_c = Expr::eq(a.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_c, head));

    // Transition: a < 10, (= a x__mid_bb3), (= x__mid_bb3 b)
    // x__mid_bb3 bridges a→b through two transfer edges.
    let from = RelationApp::new("bb0", vec![a.clone(), x_mid.clone(), b.clone()]);
    let guard = a.clone().int_lt(Expr::int_const(10));
    let t1 = Expr::eq(a.clone(), x_mid.clone()); // a → x__mid_bb3
    let t2 = Expr::eq(x_mid.clone(), b.clone()); // x__mid_bb3 → b
    let to = RelationApp::new("bb0", vec![a.clone().int_add(Expr::int_const(1)), x_mid, b.clone()]);
    let body = RuleBody::new(Some(from), vec![guard, t1, t2]);
    vc.add_rule(Rule::new(body, to));

    // Error: b > 100 — b IS anchored (distinct from a)
    let from2 = RelationApp::new("bb0", vec![a, Expr::var("x__mid_bb3", Sort::int()), b.clone()]);
    let violation = b.int_gt(Expr::int_const(100));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(from2), vec![violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.strip_dead_args();
    // x__mid_bb3 is BFS-reachable from a (anchored) → in reachable set → kept.
    assert_eq!(stripped, 0, "x__mid_bb3 must not be stripped — BFS-reachable from a");
}

/// Test that __mid_bb<N> variables reachable from an anchored variable via
/// transfer edges are conservatively kept.
///
/// `x__mid_bb3` connects to anchored variable `x` via transfer edge `(= x
/// x__mid_bb3)`. BFS from x reaches x__mid_bb3 → it is in the reachable set
/// → its position is live. This is more conservative than dead-end pruning
/// but prevents cross-block struct field losses.
#[test]
fn test_mid_bb_reachable_alias_kept() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("x__mid_bb3", Sort::int()));

    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let x = Expr::var("x", Sort::int());
    let x_mid = Expr::var("x__mid_bb3", Sort::int());

    // Init rule
    let head = RelationApp::new("bb0", vec![x.clone(), x_mid.clone()]);
    let init_c = Expr::eq(x.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_c, head));

    // Transition: (= x x__mid_bb3) — alias of x reachable via transfer
    let from = RelationApp::new("bb0", vec![x.clone(), x_mid.clone()]);
    let guard = x.clone().int_lt(Expr::int_const(10));
    let relay = Expr::eq(x.clone(), x_mid.clone());
    let to = RelationApp::new("bb0", vec![x.clone().int_add(Expr::int_const(1)), x_mid]);
    let body = RuleBody::new(Some(from), vec![guard, relay]);
    vc.add_rule(Rule::new(body, to));

    // Error: x > 100 — only x is anchored
    let from2 = RelationApp::new("bb0", vec![x.clone(), Expr::var("x__mid_bb3", Sort::int())]);
    let violation = x.int_gt(Expr::int_const(100));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(from2), vec![violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.strip_dead_args();
    // x__mid_bb3 is BFS-reachable from x (anchored) → kept conservatively.
    assert_eq!(stripped, 0, "x__mid_bb3 should be kept — BFS-reachable from x");

    let bb0_rel = vc.relations.iter().find(|r| r.name == "bb0").expect("bb0");
    assert_eq!(bb0_rel.arity(), 2, "bb0 should keep both x and x__mid_bb3");
}

/// Test that __mid_bb<N> suffix variables with unanchored base ARE stripped.
#[test]
fn test_mid_bb_suffix_unanchored_base_stripped() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("live", Sort::int()));
    vc.add_var(VarDecl::new("dead__mid_bb2", Sort::int()));

    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let live = Expr::var("live", Sort::int());
    let dead_mid = Expr::var("dead__mid_bb2", Sort::int());

    // Init rule
    let head = RelationApp::new("bb0", vec![live.clone(), dead_mid.clone()]);
    let init_c = Expr::eq(live.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_c, head));

    // Transition: just a guard on live, dead__mid_bb2 is unanchored
    let from = RelationApp::new("bb0", vec![live.clone(), dead_mid.clone()]);
    let guard = live.clone().int_lt(Expr::int_const(10));
    let to = RelationApp::new("bb0", vec![live.clone().int_add(Expr::int_const(1)), dead_mid]);
    let body = RuleBody::new(Some(from), vec![guard]);
    vc.add_rule(Rule::new(body, to));

    // Error: live > 100
    let from2 =
        RelationApp::new("bb0", vec![live.clone(), Expr::var("dead__mid_bb2", Sort::int())]);
    let violation = live.int_gt(Expr::int_const(100));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(from2), vec![violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.strip_dead_args();
    // dead__mid_bb2 base "dead" is NOT anchored → stripped.
    assert_eq!(stripped, 1, "dead__mid_bb2 should be stripped — base 'dead' is not anchored");

    let bb0_rel = vc.relations.iter().find(|r| r.name == "bb0").expect("bb0");
    assert_eq!(bb0_rel.arity(), 1, "bb0 should only keep 'live'");
}

/// Test multiple relations with different dead positions in the same VC.
///
/// bb0 has args (x, dead_a) and loop1 has args (dead_b, y). The optimizer
/// should independently strip dead_a from bb0 position 1 and dead_b from
/// loop1 position 0, while keeping x at bb0 position 0 and y at loop1
/// position 1.
#[test]
fn test_multiple_relations_different_dead_positions() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("y", Sort::int()));
    vc.add_var(VarDecl::new("dead_a", Sort::int()));
    vc.add_var(VarDecl::new("dead_b", Sort::int()));

    // bb0(x, dead_a) — position 0 is live, position 1 is dead
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    // loop1(dead_b, y) — position 0 is dead, position 1 is live
    vc.add_relation(RelationDecl::new("loop1", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let dead_a = Expr::var("dead_a", Sort::int());
    let dead_b = Expr::var("dead_b", Sort::int());

    // Init for bb0: x=0 → bb0(x, dead_a)
    let head0 = RelationApp::new("bb0", vec![x.clone(), dead_a.clone()]);
    let init_c0 = Expr::eq(x.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_c0, head0));

    // Transition bb0 → loop1: bb0(x, dead_a) ∧ x < 10 → loop1(dead_b, x)
    // x is passed to loop1 position 1; dead_b at position 0 is unconstrained.
    let from0 = RelationApp::new("bb0", vec![x.clone(), dead_a.clone()]);
    let guard0 = x.clone().int_lt(Expr::int_const(10));
    let to_loop = RelationApp::new("loop1", vec![dead_b.clone(), x]);
    let body0 = RuleBody::new(Some(from0), vec![guard0]);
    vc.add_rule(Rule::new(body0, to_loop));

    // Transition loop1 → bb0: loop1(dead_b, y) ∧ y < 5 → bb0(y, dead_a)
    // y is passed to bb0 position 0; dead_a at position 1 is unconstrained.
    let from1 = RelationApp::new("loop1", vec![dead_b.clone(), y.clone()]);
    let guard1 = y.clone().int_lt(Expr::int_const(5));
    let to_bb0 = RelationApp::new("bb0", vec![y.clone(), dead_a]);
    let body1 = RuleBody::new(Some(from1), vec![guard1]);
    vc.add_rule(Rule::new(body1, to_bb0));

    // Error rule: loop1(dead_b, y) ∧ y > 100 → error
    let from_err = RelationApp::new("loop1", vec![dead_b, y.clone()]);
    let violation = y.int_gt(Expr::int_const(100));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(from_err), vec![violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.strip_dead_args();
    // bb0 position 1 (dead_a) is dead; loop1 position 0 (dead_b) is dead.
    assert_eq!(stripped, 2, "should strip dead_a from bb0 and dead_b from loop1");

    let bb0_rel = vc.relations.iter().find(|r| r.name == "bb0").expect("bb0");
    assert_eq!(bb0_rel.arity(), 1, "bb0 should keep only x");

    let loop1_rel = vc.relations.iter().find(|r| r.name == "loop1").expect("loop1");
    assert_eq!(loop1_rel.arity(), 1, "loop1 should keep only y");

    // Verify all RelationApp references have correct arity.
    for rule in &vc.rules {
        match rule.head.name.as_ref() {
            "bb0" => assert_eq!(rule.head.args.len(), 1, "bb0 head should have 1 arg"),
            "loop1" => assert_eq!(rule.head.args.len(), 1, "loop1 head should have 1 arg"),
            _ => {}
        }
        if let Some(ref rel) = rule.body.relation {
            match rel.name.as_ref() {
                "bb0" => assert_eq!(rel.args.len(), 1, "bb0 body should have 1 arg"),
                "loop1" => assert_eq!(rel.args.len(), 1, "loop1 body should have 1 arg"),
                _ => {}
            }
        }
    }
}

/// Regression test: intermediate relay block must not lose state (#3151).
///
/// When a variable is "passed through" an intermediate block only via transfer
/// edges (no real constraints), the old algorithm stripped its position from
/// the intermediate relation — making the variable universally quantified and
/// breaking the state chain.
///
/// Setup: bb0 → bb1 → bb2, where `y` is anchored in bb0 and bb2 but only
/// appears in transfer edges in bb1.
///
/// Before fix: bb1 position 1 was stripped (y' only in transfer → dead).
/// After fix: cross-relation liveness propagation keeps bb1 position 1 alive.
#[test]
fn test_intermediate_relay_block_not_stripped() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("x_out", Sort::int()));
    vc.add_var(VarDecl::new("y", Sort::int()));
    vc.add_var(VarDecl::new("y_out", Sort::int()));
    vc.add_var(VarDecl::new("x1", Sort::int()));
    vc.add_var(VarDecl::new("x1_out", Sort::int()));
    vc.add_var(VarDecl::new("y1", Sort::int()));
    vc.add_var(VarDecl::new("y1_out", Sort::int()));
    vc.add_var(VarDecl::new("x2", Sort::int()));
    vc.add_var(VarDecl::new("y2", Sort::int()));

    // Three block relations with 2 args each.
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::new("bb2", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let x = Expr::var("x", Sort::int());
    let x_out = Expr::var("x_out", Sort::int());
    let y = Expr::var("y", Sort::int());
    let y_out = Expr::var("y_out", Sort::int());
    let x1 = Expr::var("x1", Sort::int());
    let x1_out = Expr::var("x1_out", Sort::int());
    let y1 = Expr::var("y1", Sort::int());
    let y1_out = Expr::var("y1_out", Sort::int());
    let x2 = Expr::var("x2", Sort::int());
    let y2 = Expr::var("y2", Sort::int());

    // Init: x_out=0, y_out=5 → bb0(x_out, y_out)
    let head = RelationApp::new("bb0", vec![x_out.clone(), y_out.clone()]);
    let init_c1 = Expr::eq(x_out.clone(), Expr::int_const(0));
    let init_c2 = Expr::eq(y_out.clone(), Expr::int_const(5));
    vc.add_rule(Rule::new(RuleBody::new(None, vec![init_c1, init_c2]), head));

    // bb0 → bb1: bb0(x, y) ∧ x<10 ∧ (= x_out (+ x 1)) ∧ (= y_out y) → bb1(x_out, y_out)
    // y is anchored in bb0 (via the error rule below), x_out computed.
    let from0 = RelationApp::new("bb0", vec![x.clone(), y.clone()]);
    let guard0 = x.clone().int_lt(Expr::int_const(10));
    let step0 = Expr::eq(x_out.clone(), x.int_add(Expr::int_const(1)));
    let y_copy0 = Expr::eq(y_out.clone(), y); // transfer
    let to1 = RelationApp::new("bb1", vec![x_out, y_out]);
    vc.add_rule(Rule::new(RuleBody::new(Some(from0), vec![guard0, step0, y_copy0]), to1));

    // bb1 → bb2: bb1(x1, y1) ∧ (= x1_out x1) ∧ (= y1_out y1) → bb2(x1_out, y1_out)
    // CRITICAL: y1 at position 1 of bb1 has NO anchoring constraint —
    // only transfer edges. Without cross-relation propagation, position 1
    // of bb1 is wrongly stripped.
    let from1 = RelationApp::new("bb1", vec![x1.clone(), y1.clone()]);
    let x_copy1 = Expr::eq(x1_out.clone(), x1); // transfer
    let y_copy1 = Expr::eq(y1_out.clone(), y1); // transfer — only connection for y through bb1
    let to2 = RelationApp::new("bb2", vec![x1_out, y1_out]);
    vc.add_rule(Rule::new(RuleBody::new(Some(from1), vec![x_copy1, y_copy1]), to2));

    // Error: bb2(x2, y2) ∧ y2 > 100 → error
    // y2 IS anchored in bb2 — liveness must propagate back to bb1.
    let from2 = RelationApp::new("bb2", vec![x2, y2.clone()]);
    let violation = y2.int_gt(Expr::int_const(100));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(from2), vec![violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.strip_dead_args();
    // Position 1 (y) must be kept in ALL three relations because liveness
    // propagates: bb2 (anchored) → bb1 (via transfer link) → bb0 (anchored).
    assert_eq!(stripped, 0, "no positions should be stripped — y is live across all blocks");

    // Verify all relations keep both args.
    for name in &["bb0", "bb1", "bb2"] {
        let rel = vc.relations.iter().find(|r| r.name == *name).expect(name);
        assert_eq!(rel.arity(), 2, "{name} should keep both args");
    }
}

/// Test that the fix doesn't prevent stripping truly dead positions in
/// multi-relation VCs where dead positions are independent.
///
/// bb0(x, dead_a) and bb1(dead_b, y) with NO transfer edges linking the
/// dead positions. dead_a at bb0 pos 1 and dead_b at bb1 pos 0 should
/// still be stripped.
#[test]
fn test_independent_dead_positions_still_stripped() {
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("y", Sort::int()));
    vc.add_var(VarDecl::new("dead_a", Sort::int()));
    vc.add_var(VarDecl::new("dead_b", Sort::int()));

    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int(), Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let x = Expr::var("x", Sort::int());
    let y = Expr::var("y", Sort::int());
    let dead_a = Expr::var("dead_a", Sort::int());
    let dead_b = Expr::var("dead_b", Sort::int());

    // Init: x=0 → bb0(x, dead_a)
    let head0 = RelationApp::new("bb0", vec![x.clone(), dead_a.clone()]);
    let init_c = Expr::eq(x.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_c, head0));

    // bb0 → bb1: bb0(x, dead_a) ∧ x<10 → bb1(dead_b, x)
    // No transfer edges linking dead_a to dead_b.
    let from0 = RelationApp::new("bb0", vec![x.clone(), dead_a]);
    let guard = x.clone().int_lt(Expr::int_const(10));
    let to1 = RelationApp::new("bb1", vec![dead_b.clone(), x]);
    vc.add_rule(Rule::new(RuleBody::new(Some(from0), vec![guard]), to1));

    // Error: bb1(dead_b, y) ∧ y > 100 → error
    let from1 = RelationApp::new("bb1", vec![dead_b, y.clone()]);
    let violation = y.int_gt(Expr::int_const(100));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(from1), vec![violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.strip_dead_args();
    // dead_a at bb0 pos 1 and dead_b at bb1 pos 0 are truly dead —
    // no transfer edges link them to live positions.
    assert_eq!(stripped, 2, "should strip dead_a from bb0 and dead_b from bb1");

    let bb0_rel = vc.relations.iter().find(|r| r.name == "bb0").expect("bb0");
    assert_eq!(bb0_rel.arity(), 1, "bb0 should keep only x");

    let bb1_rel = vc.relations.iter().find(|r| r.name == "bb1").expect("bb1");
    assert_eq!(bb1_rel.arity(), 1, "bb1 should keep only y");
}

/// Test that store/select connected variables propagate liveness across blocks.
///
/// bb0 stores a field value into a memory array. bb1 only relays the memory
/// array via transfer edge. bb2 selects from the array. The memory array
/// position must stay live in bb1 despite only having transfer edges there.
#[test]
fn test_store_select_relay_propagation() {
    let arr_sort = Sort::array(Sort::int(), Sort::int());
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("x_out", Sort::int()));
    vc.add_var(VarDecl::new("arr", arr_sort.clone()));
    vc.add_var(VarDecl::new("arr_out", arr_sort.clone()));
    vc.add_var(VarDecl::new("arr1", arr_sort.clone()));
    vc.add_var(VarDecl::new("arr1_out", arr_sort.clone()));
    vc.add_var(VarDecl::new("x2", Sort::int()));
    vc.add_var(VarDecl::new("arr2", arr_sort.clone()));
    vc.add_var(VarDecl::new("val", Sort::int()));
    vc.add_var(VarDecl::new("result", Sort::int()));

    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int(), arr_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int(), arr_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb2", vec![Sort::int(), arr_sort.clone()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let x = Expr::var("x", Sort::int());
    let x_out = Expr::var("x_out", Sort::int());
    let arr = Expr::var("arr", arr_sort.clone());
    let arr_out = Expr::var("arr_out", arr_sort.clone());
    let arr1 = Expr::var("arr1", arr_sort.clone());
    let arr1_out = Expr::var("arr1_out", arr_sort.clone());
    let x2 = Expr::var("x2", Sort::int());
    let arr2 = Expr::var("arr2", arr_sort);
    let val = Expr::var("val", Sort::int());
    let result = Expr::var("result", Sort::int());

    // Init: x_out=0, arr_out=const_arr → bb0(x_out, arr_out)
    let head = RelationApp::new("bb0", vec![x_out.clone(), arr_out.clone()]);
    let init_c = Expr::eq(x_out.clone(), Expr::int_const(0));
    vc.add_rule(Rule::init(init_c, head));

    // bb0 → bb1: store val into arr, relay to bb1
    // arr_out = store(arr, x, val) — arr is anchored by store
    let from0 = RelationApp::new("bb0", vec![x.clone(), arr.clone()]);
    let store_c = Expr::eq(arr_out.clone(), Expr::store(arr, x.clone(), val));
    let x_step = Expr::eq(x_out.clone(), x.int_add(Expr::int_const(1)));
    let to1 = RelationApp::new("bb1", vec![x_out, arr_out]);
    vc.add_rule(Rule::new(RuleBody::new(Some(from0), vec![store_c, x_step]), to1));

    // bb1 → bb2: ONLY transfer edges for arr — no real constraints on arr1
    let from1 = RelationApp::new("bb1", vec![Expr::var("x1", Sort::int()), arr1.clone()]);
    let x_relay = Expr::eq(Expr::var("x1_out", Sort::int()), Expr::var("x1", Sort::int()));
    let arr_relay = Expr::eq(arr1_out.clone(), arr1); // transfer — only connection
    let to2 = RelationApp::new("bb2", vec![Expr::var("x1_out", Sort::int()), arr1_out]);
    vc.add_rule(Rule::new(RuleBody::new(Some(from1), vec![x_relay, arr_relay]), to2));

    // bb2: select from arr, check result
    let from2 = RelationApp::new("bb2", vec![x2.clone(), arr2.clone()]);
    let select_c = Expr::eq(result.clone(), Expr::select(arr2, x2));
    let violation = result.int_gt(Expr::int_const(1000));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(from2), vec![select_c, violation]),
        RelationApp::nullary("error"),
    ));

    let stripped = vc.strip_dead_args();
    // arr at position 1 must be live in ALL blocks:
    // bb0 (store anchors it), bb1 (transfer relay), bb2 (select anchors it).
    assert_eq!(stripped, 0, "no args should be stripped — arr is live across all blocks");

    for name in &["bb0", "bb1", "bb2"] {
        let rel = vc.relations.iter().find(|r| r.name == *name).expect(name);
        assert_eq!(rel.arity(), 2, "{name} should keep both args");
    }
}

/// Test that collect_var_names handles FP unary expressions.
///
/// Before the FP handler was added, FP expressions fell through to the
/// catch-all `_ => {}` and silently dropped variables.
#[test]
fn test_collect_var_names_fp_unary() {
    let fp_sort = Sort::fp(8, 24); // fp32
    let x = Expr::var("x", fp_sort);
    let abs_x = x.fp_abs();

    let mut vars = HashSet::new();
    collect_var_names(&abs_x, &mut vars);
    assert!(vars.contains("x"), "FpAbs should collect variable x");
    assert_eq!(vars.len(), 1);
}

/// Test that collect_var_names handles FP binary expressions with rounding mode.
#[test]
fn test_collect_var_names_fp_binary_rounding() {
    let fp_sort = Sort::fp(8, 24);
    let a = Expr::var("a", fp_sort.clone());
    let b = Expr::var("b", fp_sort);
    let sum = a.fp_add(RoundingMode::RNE, b);

    let mut vars = HashSet::new();
    collect_var_names(&sum, &mut vars);
    assert!(vars.contains("a"), "FpAdd should collect variable a");
    assert!(vars.contains("b"), "FpAdd should collect variable b");
    assert_eq!(vars.len(), 2);
}

/// Test that collect_var_names handles FP comparison expressions.
#[test]
fn test_collect_var_names_fp_comparison() {
    let fp_sort = Sort::fp(8, 24);
    let a = Expr::var("a", fp_sort.clone());
    let b = Expr::var("b", fp_sort);
    let lt = a.fp_lt(b);

    let mut vars = HashSet::new();
    collect_var_names(&lt, &mut vars);
    assert!(vars.contains("a"), "FpLt should collect variable a");
    assert!(vars.contains("b"), "FpLt should collect variable b");
    assert_eq!(vars.len(), 2);
}

/// Test that collect_var_names handles nested FP expressions.
///
/// Exercises the recursion path: FpAdd contains FpNeg which contains a Var.
#[test]
fn test_collect_var_names_fp_nested() {
    let fp_sort = Sort::fp(8, 24);
    let x = Expr::var("x", fp_sort.clone());
    let y = Expr::var("y", fp_sort);
    // fp_add(rne, fp_neg(x), y)
    let nested = x.fp_neg().fp_add(RoundingMode::RNE, y);

    let mut vars = HashSet::new();
    collect_var_names(&nested, &mut vars);
    assert!(vars.contains("x"), "nested FpNeg(x) should be collected");
    assert!(vars.contains("y"), "y in FpAdd should be collected");
    assert_eq!(vars.len(), 2);
}

/// Test that FP predicate expressions (is_nan, etc.) collect variables.
#[test]
fn test_collect_var_names_fp_predicates() {
    let fp_sort = Sort::fp(8, 24);
    let x = Expr::var("x", fp_sort);
    let is_nan = x.fp_is_nan();

    let mut vars = HashSet::new();
    collect_var_names(&is_nan, &mut vars);
    assert!(vars.contains("x"), "FpIsNaN should collect variable x");
    assert_eq!(vars.len(), 1);
}
