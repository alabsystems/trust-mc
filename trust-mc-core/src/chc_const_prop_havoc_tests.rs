// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! An unbound head `X__out` is a havoc, never an identity frame.
//!
//! A clause variable is universally quantified over its clause, so a head
//! argument `X__out` that no body constraint binds lets the head hold for EVERY
//! value of it. The encoder relies on exactly that to havoc a slot: the
//! constraint-or-unchanged fix-up (#3138) registers `true` for a modified local
//! it could not constrain, `havoc_local_fail_closed` registers `true` for every
//! flattened slot of a store it could not mirror, and each audited `SoundHavoc`
//! site leaves its destination unbound. An unchanged slot is stated either by
//! putting the INPUT variable `X` in the head or by an explicit `(= X__out X)`.
//!
//! Constant propagation used to read an unbound `X__out` whose input `X` it knew
//! to be constant as the identity `X__out = X` and copied the constant across
//! (`propagate_to_unconstrained_out_vars`). That re-bound every such havoc to
//! the slot's stale value before the solver saw it: a store the encoder had
//! given up on (and havocked) vanished, a `SoundHavoc` proof rested on the stale
//! value with no qualifier, and a fail-closed one survived only because the
//! recorded reason demoted it. Each `bug_` test below fails with that rule in
//! place; the `keeps_` tests pin the precision the removal must not cost.

use ay_bindings::{Expr, Sort};

use crate::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody};

use super::propagate_constants;

fn bv8(val: i64) -> Expr {
    Expr::bitvec_const(val, 8)
}

fn bv8_var(name: &str) -> Expr {
    Expr::var(name, Sort::bitvec(8))
}

fn relation<'a>(vc: &'a ChcVc, name: &str) -> &'a RelationDecl {
    vc.relations
        .iter()
        .find(|r| r.name == name)
        .unwrap_or_else(|| panic!("relation {name} not found in VC"))
}

fn has_error_rule(vc: &ChcVc) -> bool {
    vc.rules.iter().any(|r| r.head.name.as_str() == "error")
}

/// The head of the (single) rule whose head relation is `head`.
fn head_args_of(vc: &ChcVc, head: &str) -> Vec<Expr> {
    let rules: Vec<_> = vc.rules.iter().filter(|r| r.head.name.as_str() == head).collect();
    assert_eq!(rules.len(), 1, "expected exactly one rule into {head}");
    rules[0].head.args.to_vec()
}

/// `error :- rel(v), not (v = expected)` over a one-column relation.
fn error_unless_equal(vc: &mut ChcVc, rel: &str, expected: i64) {
    let v = bv8_var("err_v");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new(rel, vec![v.clone()])),
            vec![Expr::not(v.eq(bv8(expected)))],
        ),
        RelationApp::nullary("error"),
    ));
}

/// entry -> bb0(7); bb0(x) -> bb1(x__out) with NO constraint on x__out;
/// bb1(v) /\ v != 7 -> error.
///
/// `x__out` is free, so bb1(v) holds for every v and the error edge is
/// reachable. The identity reading made bb1 the constant 7 and deleted the
/// error rule: a proof of a reachable error.
#[test]
fn bug_unbound_out_var_is_havoc_not_identity() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv8(7)]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![bv8_var("x")])), vec![]),
        RelationApp::new("bb1", vec![bv8_var("x__out")]),
    ));
    error_unless_equal(&mut vc, "bb1", 7);

    propagate_constants(&mut vc);

    assert_eq!(relation(&vc, "bb0").arity(), 0, "bb0 really is the constant 7");
    assert_eq!(relation(&vc, "bb1").arity(), 1, "bb1's column is havocked, not constant");
    assert_eq!(
        head_args_of(&vc, "bb1"),
        vec![bv8_var("x__out")],
        "the havoc stays a free variable"
    );
    assert!(has_error_rule(&vc), "the error edge over the havocked slot must survive");
}

/// The fail-closed shape `havoc_local_fail_closed` emits for a flattened
/// two-slot owner `o = P { a: 0, c: 0 }` whose store through a reference could
/// not be mirrored: the slot constraints were replaced by `true`, and the head
/// carries both output variables. A check `o.a == 0` must stay refutable.
#[test]
fn bug_fail_closed_true_havoc_of_flattened_slots_survives() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(8), Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(8), Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv8(0), bv8(0)]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![bv8_var("_1_fld0"), bv8_var("_1_fld1")])),
            vec![Expr::bool_const(true), Expr::bool_const(true)],
        ),
        RelationApp::new("bb1", vec![bv8_var("_1_fld0__out"), bv8_var("_1_fld1__out")]),
    ));
    let (a, c) = (bv8_var("a"), bv8_var("c"));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![a.clone(), c])),
            vec![Expr::not(a.eq(bv8(0)))],
        ),
        RelationApp::nullary("error"),
    ));

    propagate_constants(&mut vc);

    assert_eq!(relation(&vc, "bb0").arity(), 0, "the owner's input slots are constant");
    assert_eq!(relation(&vc, "bb1").arity(), 2, "both havocked slots stay columns");
    assert!(has_error_rule(&vc), "a check over a fail-closed slot must reach the solver");
}

/// A havoc in the middle of a chain stops the constant: the slot is constant
/// before the havoc (so its column is removed there) and free after it, through
/// every later unchanged frame.
#[test]
fn bug_havoc_blocks_the_downstream_constant_cascade() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    for bb in ["bb0", "bb1", "bb2"] {
        vc.add_relation(RelationDecl::new(bb, vec![Sort::bitvec(8)]));
    }
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv8(0)]),
    ));
    // bb0 -> bb1 havocs the slot (the `constraint_invariant_fixup` shape).
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![bv8_var("x")])),
            vec![Expr::bool_const(true)],
        ),
        RelationApp::new("bb1", vec![bv8_var("x__out")]),
    ));
    // bb1 -> bb2 leaves it unchanged: the INPUT variable is the head argument.
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![bv8_var("x")])), vec![]),
        RelationApp::new("bb2", vec![bv8_var("x")]),
    ));
    error_unless_equal(&mut vc, "bb2", 0);

    propagate_constants(&mut vc);

    assert_eq!(relation(&vc, "bb0").arity(), 0, "before the havoc the slot is constant");
    assert_eq!(relation(&vc, "bb1").arity(), 1, "the havoc frees the slot");
    assert_eq!(relation(&vc, "bb2").arity(), 1, "an unchanged frame keeps it free");
    assert!(has_error_rule(&vc), "the check after the havoc must survive");
}

/// A havoc whose output variable occurs only as the argument of a datatype
/// constructor that binds nothing else (`w = Some(x__out)`, `w` free) is still a
/// havoc: `w` takes whatever value `x__out` gives it. The identity reading
/// treated constructor arguments as unconstrained and pinned `x__out` to the
/// input constant (#3398/#3405).
#[test]
fn bug_out_var_inside_unbound_constructor_is_havoc() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv8(16)]),
    ));
    let option_sort = Sort::enum_type(
        "Option",
        vec![("Some", vec![("val", Sort::bitvec(8))]), ("None", vec![] as Vec<(&str, Sort)>)],
    );
    let x_out = bv8_var("x__out");
    let wrapped =
        Expr::datatype_constructor("Option", "Some", vec![x_out.clone()], option_sort.clone());
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![bv8_var("x")])),
            vec![Expr::var("wrapped", option_sort).eq(wrapped)],
        ),
        RelationApp::new("bb1", vec![x_out]),
    ));
    error_unless_equal(&mut vc, "bb1", 16);

    propagate_constants(&mut vc);

    assert_eq!(relation(&vc, "bb1").arity(), 1, "x__out is free inside an unbound constructor");
    assert!(has_error_rule(&vc), "the error edge over the free slot must survive");
}

/// Precision control: an explicit identity frame `(= x__out x)` is followed by
/// the ordinary equality propagation, so the constant still cascades and the
/// infeasible error edge is still removed before the solver.
#[test]
fn keeps_explicit_identity_frame_propagating() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv8(7)]),
    ));
    let (x, x_out) = (bv8_var("x"), bv8_var("x__out"));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone()])), vec![x_out.clone().eq(x)]),
        RelationApp::new("bb1", vec![x_out]),
    ));
    error_unless_equal(&mut vc, "bb1", 7);

    propagate_constants(&mut vc);

    assert_eq!(relation(&vc, "bb1").arity(), 0, "an explicit frame keeps the constant");
    assert!(!has_error_rule(&vc), "the infeasible error edge is still folded away");
}

/// Precision control: the encoder's usual unchanged frame (the INPUT variable in
/// the head) still carries the constant.
#[test]
fn keeps_input_variable_frame_propagating() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv8(7)]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![bv8_var("x")])), vec![]),
        RelationApp::new("bb1", vec![bv8_var("x")]),
    ));
    error_unless_equal(&mut vc, "bb1", 7);

    propagate_constants(&mut vc);

    assert_eq!(relation(&vc, "bb1").arity(), 0, "the input-variable frame keeps the constant");
    assert!(!has_error_rule(&vc), "the infeasible error edge is still folded away");
}

/// Control: a havoc bound to a fresh variable (`(= x__out __havoc_1)`, the
/// shape `emit_intrinsic_nondet_destination` and the foreign-effect frame emit)
/// was already safe and stays a free column.
#[test]
fn keeps_fresh_bound_havoc_free() {
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![bv8(7)]),
    ));
    let x_out = bv8_var("x__out");
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![bv8_var("x")])),
            vec![x_out.clone().eq(bv8_var("__havoc_1"))],
        ),
        RelationApp::new("bb1", vec![x_out]),
    ));
    error_unless_equal(&mut vc, "bb1", 7);

    propagate_constants(&mut vc);

    assert_eq!(relation(&vc, "bb1").arity(), 1);
    assert!(has_error_rule(&vc));
}
