// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for the naming of deep bitvector `ite` chains
//! (`chc_optimize_ite_chains.rs`).

use std::collections::HashMap;

use ay_bindings::{Expr, ExprValue, Sort};
use num_bigint::BigInt;

use super::ite_chains::{ITE_CHAIN_DEPTH_THRESHOLD, ITE_CHAIN_LINK_DEPTH, ITE_CHAIN_VAR_PREFIX};
use crate::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};

fn bv8(value: u64) -> Expr {
    Expr::bitvec_const(value, 8)
}

/// The value the CHC inline walker leaves for `while i < n { i += 1 }`
/// replayed `depth` passes: `ite(!(k >= n), <pass k + 1>, k)`, innermost
/// `ite(!(depth >= n), depth + 1, depth)`.
fn replayed_count(n: &Expr, depth: u64) -> Expr {
    let mut value = Expr::ite(bv8(depth).bvuge(n.clone()).not(), bv8(depth + 1), bv8(depth));
    for k in (0..depth).rev() {
        value = Expr::ite(bv8(k).bvuge(n.clone()).not(), value, bv8(k));
    }
    value
}

/// `bb0(n, i) /\ i_out = <chain> => bb1(n, i_out)`, plus the facts around it.
fn chain_vc(chain: Expr) -> ChcVc {
    let mut vc = ChcVc::new();
    for name in ["n", "i", "i__out"] {
        vc.add_var(VarDecl::new(name, Sort::bitvec(8)));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(8), Sort::bitvec(8)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(8), Sort::bitvec(8)]));
    let n = Expr::var("n", Sort::bitvec(8));
    let i = Expr::var("i", Sort::bitvec(8));
    let i_out = Expr::var("i__out", Sort::bitvec(8));
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![n.clone().bvule(bv8(12))]),
        RelationApp::new("bb0", vec![n.clone(), i.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![n.clone(), i.clone()])),
            vec![i_out.clone().eq(chain)],
        ),
        RelationApp::new("bb1", vec![n, i_out]),
    ));
    vc
}

fn ite_depth(expr: &Expr) -> usize {
    let deepest = expr.children().map(ite_depth).max().unwrap_or(0);
    deepest + usize::from(matches!(expr.value(), ExprValue::Ite { .. }) && expr.sort().is_bitvec())
}

/// A small evaluator for the terms these tests build.
fn eval(expr: &Expr, env: &HashMap<String, Value>) -> Value {
    let bv = |e: &Expr| match eval(e, env) {
        Value::Bv(v) => v,
        Value::Bool(_) => panic!("expected a bitvector: {e:?}"),
    };
    let boolean = |e: &Expr| match eval(e, env) {
        Value::Bool(b) => b,
        Value::Bv(_) => panic!("expected a bool: {e:?}"),
    };
    match expr.value() {
        ExprValue::BitVecConst { value, .. } => Value::Bv(u64::try_from(value).unwrap()),
        ExprValue::BoolConst(b) => Value::Bool(*b),
        ExprValue::Var { name } => *env.get(name).unwrap_or_else(|| panic!("unbound {name}")),
        ExprValue::Ite { cond, then_expr, else_expr } => {
            if boolean(cond) {
                eval(then_expr, env)
            } else {
                eval(else_expr, env)
            }
        }
        ExprValue::Not(e) => Value::Bool(!boolean(e)),
        ExprValue::BvUGe(a, b) => Value::Bool(bv(a) >= bv(b)),
        ExprValue::BvULe(a, b) => Value::Bool(bv(a) <= bv(b)),
        ExprValue::BvAdd(a, b) => Value::Bv((bv(a) + bv(b)) & 0xff),
        ExprValue::Eq(a, b) => Value::Bool(eval(a, env) == eval(b, env)),
        other => panic!("not evaluated here: {other:?}"),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Value {
    Bv(u64),
    Bool(bool),
}

/// The value of `i__out` the renamed rule determines for `n`: the defining
/// equalities are evaluated in order (each names a term over earlier ones),
/// then the first constraint.
fn renamed_value(rule: &Rule, n: u64) -> u64 {
    let mut env = HashMap::from([("n".to_string(), Value::Bv(n))]);
    let constraints: Vec<&Expr> = rule.body.constraints.iter().collect();
    // Definitions are appended after the original constraint, innermost
    // first, so each mentions only links defined before it.
    for constraint in &constraints[1..] {
        let ExprValue::Eq(var, term) = constraint.value() else {
            panic!("a definition is an equality: {constraint:?}");
        };
        let ExprValue::Var { name } = var.value() else {
            panic!("a definition names a variable: {constraint:?}");
        };
        assert!(name.starts_with(ITE_CHAIN_VAR_PREFIX), "{name}");
        let value = eval(term, &env);
        env.insert(name.clone(), value);
    }
    let ExprValue::Eq(out, chain) = constraints[0].value() else {
        panic!("the original constraint stays first: {:?}", constraints[0]);
    };
    assert!(matches!(out.value(), ExprValue::Var { name } if name == "i__out"));
    match eval(chain, &env) {
        Value::Bv(v) => v,
        Value::Bool(_) => unreachable!(),
    }
}

#[test]
fn a_thirteen_deep_replay_chain_is_named_in_links_and_keeps_its_value() {
    let n = Expr::var("n", Sort::bitvec(8));
    let chain = replayed_count(&n, 12);
    assert_eq!(ite_depth(&chain), 13);
    let mut vc = chain_vc(chain.clone());

    let named = vc.name_deep_ite_chains_unconditionally();

    assert!(named >= 2, "a 13-deep chain needs more than one link, got {named}");
    let rule = &vc.rules[1];
    assert_eq!(rule.body.constraints.len(), 1 + named);
    for constraint in rule.body.constraints.iter() {
        assert!(
            ite_depth(constraint) <= ITE_CHAIN_LINK_DEPTH,
            "every remaining chain is at most one link deep: {constraint:?}"
        );
    }
    for var in vc.vars().iter().filter(|v| v.name.starts_with(ITE_CHAIN_VAR_PREFIX)) {
        assert!(var.sort.is_bitvec());
    }
    assert_eq!(
        vc.vars().iter().filter(|v| v.name.starts_with(ITE_CHAIN_VAR_PREFIX)).count(),
        named,
        "every link variable is declared"
    );
    // Exact: for every input the renamed rule determines the value the chain
    // had, including inputs past the chain's depth.
    for n_value in 0..=40u64 {
        let original = match eval(&chain, &HashMap::from([("n".to_string(), Value::Bv(n_value))])) {
            Value::Bv(v) => v,
            Value::Bool(_) => unreachable!(),
        };
        assert_eq!(renamed_value(rule, n_value), original, "n = {n_value}");
    }
    // The fact and the relation applications are untouched.
    assert_eq!(vc.rules[0].body.constraints.len(), 1);
    assert_eq!(rule.head.args.len(), 2);
}

#[test]
fn a_chain_at_the_threshold_is_left_as_it_is() {
    let n = Expr::var("n", Sort::bitvec(8));
    let chain = replayed_count(&n, (ITE_CHAIN_DEPTH_THRESHOLD - 1) as u64);
    assert_eq!(ite_depth(&chain), ITE_CHAIN_DEPTH_THRESHOLD);
    let mut vc = chain_vc(chain);
    let before = vc.rules.clone();

    assert_eq!(vc.name_deep_ite_chains_unconditionally(), 0);
    assert_eq!(vc.rules, before);
}

#[test]
fn a_shared_link_is_named_once() {
    let n = Expr::var("n", Sort::bitvec(8));
    let shared = replayed_count(&n, 9);
    // Both arms reach the same 10-deep chain object.
    let both = Expr::ite(n.clone().bvule(bv8(3)), shared.clone(), shared.bvadd(bv8(1)));
    let mut vc = chain_vc(both.clone());

    let named = vc.name_deep_ite_chains_unconditionally();

    let mut alone = chain_vc(replayed_count(&n, 9));
    let named_alone = alone.name_deep_ite_chains_unconditionally();
    assert_eq!(named, named_alone, "the shared chain's links are named once");
    for n_value in 0..=20u64 {
        let original = match eval(&both, &HashMap::from([("n".to_string(), Value::Bv(n_value))])) {
            Value::Bv(v) => v,
            Value::Bool(_) => unreachable!(),
        };
        assert_eq!(renamed_value(&vc.rules[1], n_value), original, "n = {n_value}");
    }
}

#[test]
fn a_deep_chain_of_another_sort_is_left_as_it_is() {
    // An integer chain: the pass names bitvector chains only.
    let n = Expr::var("n", Sort::int());
    let mut value = Expr::ite(
        n.clone().int_lt(Expr::int_const(BigInt::from(9))),
        Expr::int_const(1),
        Expr::int_const(0),
    );
    for k in 0..12 {
        value = Expr::ite(
            n.clone().int_lt(Expr::int_const(BigInt::from(k))),
            value,
            Expr::int_const(BigInt::from(k)),
        );
    }
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("n", Sort::int()));
    vc.add_var(VarDecl::new("m", Sort::int()));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int()]));
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![Expr::var("m", Sort::int()).eq(value)]),
        RelationApp::new("bb1", vec![Expr::var("m", Sort::int())]),
    ));
    let before = vc.rules.clone();

    assert_eq!(vc.name_deep_ite_chains_unconditionally(), 0);
    assert_eq!(vc.rules, before);
}

#[test]
fn a_deep_chain_in_a_head_argument_is_defined_in_the_body() {
    let n = Expr::var("n", Sort::bitvec(8));
    let chain = replayed_count(&n, 12);
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("n", Sort::bitvec(8)));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(8), Sort::bitvec(8)]));
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![n.clone().bvule(bv8(12))]),
        RelationApp::new("bb1", vec![n.clone(), chain.clone()]),
    ));

    let named = vc.name_deep_ite_chains_unconditionally();

    assert!(named >= 2);
    let rule = &vc.rules[0];
    assert!(ite_depth(&rule.head.args[1]) <= ITE_CHAIN_LINK_DEPTH);
    assert_eq!(rule.body.constraints.len(), 1 + named);
    // The head argument evaluates to the chain's value once the definitions
    // in the body are evaluated.
    for n_value in 0..=12u64 {
        let mut env = HashMap::from([("n".to_string(), Value::Bv(n_value))]);
        for constraint in rule.body.constraints.iter().skip(1) {
            let ExprValue::Eq(var, term) = constraint.value() else { unreachable!() };
            let ExprValue::Var { name } = var.value() else { unreachable!() };
            let value = eval(term, &env);
            env.insert(name.clone(), value);
        }
        let original = eval(&chain, &HashMap::from([("n".to_string(), Value::Bv(n_value))]));
        assert_eq!(eval(&rule.head.args[1], &env), original, "n = {n_value}");
    }
}

#[test]
fn a_deep_chain_under_a_quantifier_is_left_as_it_is() {
    // `forall k. out = <chain over k>`: the chain reads the bound `k`, so a
    // definition at the rule's level would read a different, free `k`.
    let k = Expr::var("k", Sort::bitvec(8));
    let chain = replayed_count(&k, 12);
    let body = Expr::var("i__out", Sort::bitvec(8)).eq(chain).not();
    let quantified = Expr::forall(vec![("k".to_string(), Sort::bitvec(8))], body);
    let mut vc = chain_vc(bv8(0));
    vc.rules[1].body.constraints = crate::constraints::Constraints::Owned(vec![quantified]);
    let before = vc.rules.clone();

    assert_eq!(vc.name_deep_ite_chains_unconditionally(), 0);
    assert_eq!(vc.rules, before);
}
