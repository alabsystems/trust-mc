// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for `normalize_free_array_bases`: a store chain base is replaced by
//! `const_array` only where its rule leaves it unconstrained.

use super::*;
use crate::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};
use ay_bindings::Sort;

fn arr_sort() -> Sort {
    Sort::array(Sort::bitvec(64), Sort::bitvec(8))
}

fn arr(name: &str) -> Expr {
    Expr::var(name, arr_sort())
}

fn idx(i: u128) -> Expr {
    Expr::bitvec_const(i, 64)
}

fn byte(v: u128) -> Expr {
    Expr::bitvec_const(v, 8)
}

fn vc_with(vars: &[&str]) -> ChcVc {
    let mut vc = ChcVc::new();
    for name in vars {
        vc.add_var(VarDecl::new(*name, arr_sort()));
    }
    vc.add_var(VarDecl::new("v", Sort::bitvec(8)));
    vc.add_var(VarDecl::new("w", Sort::bitvec(8)));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort()]));
    vc
}

fn names_in(e: &Expr, out: &mut HashSet<String>) {
    if let ExprValue::Var { name } = e.value() {
        out.insert(name.clone());
    }
    for child in e.children() {
        names_in(child, out);
    }
}

fn mentions(vc: &ChcVc, rule: usize, var: &str) -> bool {
    let mut names = HashSet::new();
    for c in vc.rules[rule].body.constraints.iter() {
        names_in(c, &mut names);
    }
    names.contains(var)
}

fn constraints_of(vc: &ChcVc, rule: usize) -> Vec<String> {
    vc.rules[rule].body.constraints.iter().map(|c| format!("{c:?}")).collect()
}

/// The frame identity `(= a__mid_bb4 a)` binds the store base, so its unstored
/// lanes are `a`'s lanes. Replacing the base with `const_array(0)` zeroed lane 1,
/// and `a=[1,2]; while i<2 { a[0]+=1 }; assert!(a[1]==0)` was proved.
#[test]
fn a_frame_bound_store_base_is_not_replaced() {
    let mut vc = vc_with(&["a", "a__mid_bb4", "a__mid_bb5"]);
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![arr("a")])),
            vec![
                Expr::eq(arr("a__mid_bb4"), arr("a")),
                Expr::eq(
                    arr("a__mid_bb5"),
                    arr("a__mid_bb4").store(idx(0), Expr::var("v", Sort::bitvec(8))),
                ),
            ],
        ),
        RelationApp::new("bb1", vec![arr("a__mid_bb5")]),
    ));
    let before = constraints_of(&vc, 0);

    assert_eq!(vc.normalize_free_array_bases(), 0);
    assert_eq!(constraints_of(&vc, 0), before, "the bound base must survive unchanged");
}

/// A base read elsewhere in the rule (here by a `select`) is constrained too.
#[test]
fn a_store_base_that_is_also_selected_is_not_replaced() {
    let mut vc = vc_with(&["x", "y"]);
    vc.add_rule(Rule::new(
        RuleBody::new(
            None,
            vec![
                Expr::eq(arr("y"), arr("x").store(idx(0), byte(5))),
                Expr::eq(Expr::var("w", Sort::bitvec(8)), arr("x").select(idx(1))),
            ],
        ),
        RelationApp::new("bb1", vec![arr("y")]),
    ));
    let before = constraints_of(&vc, 0);

    assert_eq!(vc.normalize_free_array_bases(), 0);
    assert_eq!(constraints_of(&vc, 0), before);
}

/// The encoder's fresh aggregate base occurs only as a store chain base, so it
/// is replaced: `(= a__out (store (store __chc_array_2 0 1) 1 2))`.
#[test]
fn a_fresh_aggregate_base_is_replaced() {
    let mut vc = vc_with(&["a__out", "__chc_array_2"]);
    let chain = arr("__chc_array_2").store(idx(0), byte(1)).store(idx(1), byte(2));
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![Expr::eq(arr("a__out"), chain)]),
        RelationApp::new("bb1", vec![arr("a__out")]),
    ));

    assert_eq!(vc.normalize_free_array_bases(), 1);
    assert!(
        !mentions(&vc, 0, "__chc_array_2"),
        "base must be replaced: {:?}",
        constraints_of(&vc, 0)
    );
}

/// Variables are quantified per rule: a base left unconstrained in one rule is
/// replaced there even though another rule binds a var of the same name.
#[test]
fn the_occurrence_check_is_per_rule() {
    let mut vc = vc_with(&["a", "t", "y"]);
    vc.add_rule(Rule::new(
        RuleBody::new(
            None,
            vec![Expr::eq(arr("y"), arr("t").store(idx(0), byte(1)).store(idx(1), byte(2)))],
        ),
        RelationApp::new("bb1", vec![arr("y")]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![arr("a")])),
            vec![Expr::eq(arr("t"), arr("a")), Expr::eq(arr("y"), arr("t").store(idx(0), byte(3)))],
        ),
        RelationApp::new("bb1", vec![arr("y")]),
    ));
    let second_before = constraints_of(&vc, 1);

    assert_eq!(vc.normalize_free_array_bases(), 1);
    assert!(!mentions(&vc, 0, "t"), "rule 0 leaves t free");
    assert_eq!(constraints_of(&vc, 1), second_before, "rule 1 binds t to a");
}

/// A free base nested inside another chain's stored value is replaced as well,
/// so no occurrence of it is left raw beside a replaced one.
#[test]
fn a_base_nested_in_a_stored_value_is_replaced_everywhere() {
    let mut vc = vc_with(&["a", "x", "y"]);
    let inner = arr("x").store(idx(0), byte(7)).select(idx(0));
    let outer = arr("a").store(idx(1), inner);
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![arr("a")])),
            vec![Expr::eq(arr("y"), outer), Expr::eq(arr("y"), arr("x").store(idx(1), byte(9)))],
        ),
        RelationApp::new("bb1", vec![arr("y")]),
    ));

    assert_eq!(vc.normalize_free_array_bases(), 2);
    assert!(
        !mentions(&vc, 0, "x"),
        "every base occurrence of x must be replaced: {:?}",
        constraints_of(&vc, 0)
    );
}
