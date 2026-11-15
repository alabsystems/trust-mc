// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for pruning datatype declarations nothing emitted reaches.

use ay_bindings::{Expr, Sort};

use crate::chc::{ChcQuery, ChcVc, RelationApp, RelationDecl, Rule, RuleBody};
use crate::decl::Decl;

fn st(name: &str, fields: Vec<(&str, Sort)>) -> Sort {
    Sort::struct_type(name, fields.into_iter().map(|(n, s)| (n.to_string(), s)).collect::<Vec<(String, Sort)>>())
}

fn decl_of(sort: &Sort) -> Decl {
    Decl::datatype(sort.datatype_sort().expect("datatype sort").clone())
}

fn datatype_names(vc: &ChcVc) -> Vec<String> {
    vc.decls
        .iter()
        .filter_map(|d| d.datatype_sort().map(|dt| dt.name.clone()))
        .collect()
}

/// A VC with one relation `bb0(x: Int)` and an error edge on `x < 0`, so every
/// test starts from a problem whose clauses reach no datatype.
fn base_vc() -> ChcVc {
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", Sort::int());
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.query = ChcQuery::new().with_target("error");
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![x.clone().eq(Expr::int_const(0))]),
        RelationApp::new("bb0", vec![x.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![x.clone().eq(Expr::int_const(-1))],
        ),
        RelationApp::new("error", vec![]),
    ));
    vc
}

#[test]
fn unreferenced_datatype_is_removed_and_other_decls_stay() {
    let mut vc = base_vc();
    let unused = st("Unused", vec![("Unused_a", Sort::int())]);
    vc.add_decl(Decl::constant("k", Sort::int()));
    vc.add_decl(decl_of(&unused));
    vc.add_decl(Decl::function("f", vec![Sort::int()], Sort::bool()));
    assert_eq!(vc.prune_unreachable_datatype_decls(), 1);
    assert!(datatype_names(&vc).is_empty());
    let names: Vec<&str> = vc.decls.iter().map(Decl::name).collect();
    assert_eq!(names, vec!["k", "f"]);
}

#[test]
fn declare_var_sort_keeps_its_datatype() {
    let mut vc = base_vc();
    let point = st("Point", vec![("Point_x", Sort::int())]);
    vc.add_decl(decl_of(&point));
    vc.declare_var("p", point);
    assert_eq!(vc.prune_unreachable_datatype_decls(), 0);
    assert_eq!(datatype_names(&vc), vec!["Point"]);
}

#[test]
fn relation_signature_keeps_its_datatype_through_an_array_element() {
    let mut vc = base_vc();
    let cell = st("Cell", vec![("Cell_v", Sort::int())]);
    vc.add_decl(decl_of(&cell));
    vc.add_relation(RelationDecl::new("bb9", vec![Sort::array(Sort::int(), cell)]));
    assert_eq!(vc.prune_unreachable_datatype_decls(), 0);
    assert_eq!(datatype_names(&vc), vec!["Cell"]);
}

/// Reachability is closed over DECLARED definitions: `Outer` is reached by a
/// variable, its field is `Inner`, and `Inner` in turn holds a `Seq` of `Leaf`.
/// Order of the kept declarations is preserved (dependencies first).
#[test]
fn nested_field_datatypes_are_kept_in_order() {
    let mut vc = base_vc();
    let leaf = st("Leaf", vec![("Leaf_v", Sort::int())]);
    let inner = st("Inner", vec![("Inner_leaves", Sort::seq(leaf.clone()))]);
    let outer = st("Outer", vec![("Outer_inner", inner.clone())]);
    let stray = st("Stray", vec![("Stray_v", Sort::bool())]);
    vc.add_decl(decl_of(&leaf));
    vc.add_decl(decl_of(&stray));
    vc.add_decl(decl_of(&inner));
    vc.add_decl(decl_of(&outer));
    vc.declare_var("o", outer);
    assert_eq!(vc.prune_unreachable_datatype_decls(), 1);
    assert_eq!(datatype_names(&vc), vec!["Leaf", "Inner", "Outer"]);
}

/// A field held through an uninterpreted placeholder of a declared name (the
/// shape a recursive or forward-referenced datatype takes) keeps the target.
#[test]
fn uninterpreted_sort_of_a_declared_name_keeps_it() {
    let mut vc = base_vc();
    let node = st("Node", vec![("Node_v", Sort::int())]);
    let holder = st("Holder", vec![("Holder_next", Sort::uninterpreted("Node"))]);
    vc.add_decl(decl_of(&node));
    vc.add_decl(decl_of(&holder));
    vc.declare_var("h", holder);
    assert_eq!(vc.prune_unreachable_datatype_decls(), 0);
    assert_eq!(datatype_names(&vc), vec!["Node", "Holder"]);
}

#[test]
fn constructor_selector_and_tester_in_constraints_keep_their_datatypes() {
    let mut vc = base_vc();
    let a = st("A", vec![("A_v", Sort::int())]);
    let b = st("B", vec![("B_v", Sort::int())]);
    let c = Sort::enum_type(
        "C",
        vec![
            ("C_one".to_string(), Vec::<(String, Sort)>::new()),
            ("C_two".to_string(), Vec::<(String, Sort)>::new()),
        ],
    );
    vc.add_decl(decl_of(&a));
    vc.add_decl(decl_of(&b));
    vc.add_decl(decl_of(&c));
    let x = Expr::var("x", Sort::int());
    // Held under an uninterpreted predicate: a selector applied directly to a
    // constructor application folds to the argument and would drop `A` from
    // the tree (which pruning then correctly treats as unreachable).
    let built = Expr::func_app_with_sort(
        "keep",
        vec![Expr::datatype_constructor("A", "A_mk", vec![x.clone()], a.clone())],
        Sort::bool(),
    );
    let read = Expr::var("bv", b.clone()).field_select("B", "B_v", Sort::int());
    let tested = Expr::var("cv", c.clone()).is_constructor("C", "C_one");
    // The rule's variables are declared under Int only, so nothing but the
    // expressions themselves reaches A, B and C.
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![built, read.eq(x.clone()), tested],
        ),
        RelationApp::new("bb0", vec![x]),
    ));
    assert_eq!(vc.prune_unreachable_datatype_decls(), 0);
    assert_eq!(datatype_names(&vc), vec!["A", "B", "C"]);
}

#[test]
fn function_application_spelled_as_a_member_keeps_its_datatype() {
    let mut vc = base_vc();
    let opt = Sort::enum_type(
        "Opt",
        vec![
            ("Opt_None".to_string(), Vec::<(String, Sort)>::new()),
            ("Opt_Some".to_string(), vec![("Opt_Some_0".to_string(), Sort::int())]),
        ],
    );
    let sel = st("Sel", vec![("Sel_field", Sort::int())]);
    vc.add_decl(decl_of(&opt));
    vc.add_decl(decl_of(&sel));
    let x = Expr::var("x", Sort::int());
    let tester = Expr::func_app_with_sort("is-Opt_Some", vec![x.clone()], Sort::bool());
    let selector = Expr::func_app_with_sort("Sel_field", vec![x.clone()], Sort::int());
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![tester, selector.eq(x.clone())],
        ),
        RelationApp::new("bb0", vec![x]),
    ));
    assert_eq!(vc.prune_unreachable_datatype_decls(), 0);
    assert_eq!(datatype_names(&vc), vec!["Opt", "Sel"]);
}

#[test]
fn cover_assertion_fun_signature_and_quantifier_binder_keep_their_datatypes() {
    let mut vc = base_vc();
    let cov = st("Cov", vec![("Cov_v", Sort::int())]);
    let ret = st("Ret", vec![("Ret_v", Sort::int())]);
    let bound = st("Bound", vec![("Bound_v", Sort::int())]);
    vc.add_decl(decl_of(&cov));
    vc.add_decl(decl_of(&ret));
    vc.add_decl(decl_of(&bound));
    vc.add_decl(Decl::function("mk_ret", vec![Sort::int()], ret));
    vc.add_cover_assertion(
        "cover_0".to_string(),
        Expr::var("c", cov).field_select("Cov", "Cov_v", Sort::int()).eq(Expr::int_const(1)),
    );
    let q = Expr::forall(
        vec![("q".to_string(), bound.clone())],
        Expr::var("q", bound).field_select("Bound", "Bound_v", Sort::int()).eq(Expr::int_const(0)),
    );
    let x = Expr::var("x", Sort::int());
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone()])), vec![q]),
        RelationApp::new("bb0", vec![x]),
    ));
    assert_eq!(vc.prune_unreachable_datatype_decls(), 0);
    assert_eq!(datatype_names(&vc), vec!["Cov", "Ret", "Bound"]);
}

/// The emitter keeps the first definition of a name and skips later ones, so a
/// later same-name declaration is dropped without changing the output.
#[test]
fn later_same_name_duplicate_is_dropped_first_kept() {
    let mut vc = base_vc();
    let first = st("Dup", vec![("Dup_a", Sort::int())]);
    let second = st("Dup", vec![("Dup_b", Sort::bool())]);
    vc.add_decl(decl_of(&first));
    vc.add_decl(decl_of(&second));
    vc.declare_var("d", first);
    assert_eq!(vc.prune_unreachable_datatype_decls(), 1);
    let kept: Vec<_> = vc.decls.iter().filter_map(Decl::datatype_sort).collect();
    assert_eq!(kept.len(), 1);
    assert_eq!(kept[0].constructors[0].fields[0].name, "Dup_a");
}

#[test]
fn pruning_is_idempotent_and_a_vc_without_datatypes_is_untouched() {
    let mut vc = base_vc();
    assert_eq!(vc.prune_unreachable_datatype_decls(), 0);
    let used = st("Used", vec![("Used_v", Sort::int())]);
    let unused = st("Unused", vec![("Unused_v", Sort::int())]);
    vc.add_decl(decl_of(&unused));
    vc.add_decl(decl_of(&used));
    vc.declare_var("u", used);
    assert_eq!(vc.prune_unreachable_datatype_decls(), 1);
    assert_eq!(vc.prune_unreachable_datatype_decls(), 0);
    assert_eq!(datatype_names(&vc), vec!["Used"]);
}
