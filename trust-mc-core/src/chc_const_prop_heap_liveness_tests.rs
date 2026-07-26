// Copyright 2026 Andrew Yates, Inc.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for heap-liveness handling in CHC constant propagation.

use ay_bindings::{Expr, Sort};

use crate::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody};

use super::{
    has_block_relation_cycle, has_scalarized_obj_size_bounds, has_signed_overflow_error_edge,
    propagate_constants,
};

fn bool_var(name: &str) -> Expr {
    Expr::var(name, Sort::bool())
}

fn bv64(name: &str) -> Expr {
    Expr::var(name, Sort::bitvec(64))
}

fn find_relation<'a>(vc: &'a ChcVc, name: &str) -> &'a RelationDecl {
    vc.relations
        .iter()
        .find(|r| r.name == name)
        .unwrap_or_else(|| panic!("relation {name} not found in VC"))
}

#[test]
fn test_scalarized_obj_valid_lane_not_propagated() {
    // Scalarized obj_valid lanes carry heap allocation liveness. Even when a
    // lane is initialized to true and later written to false, constant
    // propagation must not strip it from relation signatures: that loses the
    // state distinction needed by use-after-free checks after realloc.
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("entry", vec![]));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bool()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bool()]));
    vc.add_relation(RelationDecl::nullary("error"));

    let live = bool_var("obj_valid_at_0x34_bv32");
    let live_out = bool_var("obj_valid_at_0x34_bv32__out");

    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::nullary("entry")), vec![]),
        RelationApp::new("bb0", vec![Expr::bool_const(true)]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![live.clone()])),
            vec![live_out.clone().eq(Expr::bool_const(false))],
        ),
        RelationApp::new("bb1", vec![live_out]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![live.clone()])), vec![live.not()]),
        RelationApp::nullary("error"),
    ));

    propagate_constants(&mut vc);

    let bb0 = find_relation(&vc, "bb0");
    let bb1 = find_relation(&vc, "bb1");
    assert_eq!(bb0.arity(), 1, "bb0 must retain scalarized obj_valid");
    assert_eq!(bb1.arity(), 1, "bb1 must retain scalarized obj_valid");
    assert!(
        vc.rules.iter().any(|r| {
            r.head.name.as_str() == "error"
                && r.body.constraints.iter().any(|c| c.to_string().contains("obj_valid_at_0x34"))
        }),
        "stale-pointer error rule must still depend on obj_valid liveness"
    );
}

#[test]
fn test_scalarized_obj_size_bounds_detected_for_dynamic_heap_cell() {
    // A constant-address heap cell alongside heap allocation metadata is a
    // dynamic-allocation access whose obj_size bound const-prop could drop.
    let mut vc = ChcVc::new();
    vc.declare_var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    vc.declare_var("_main_mem_i16_at_0xc000000004_bv64", Sort::bitvec(64));
    assert!(has_scalarized_obj_size_bounds(&vc));
}

#[test]
fn test_scalarized_obj_size_bounds_requires_heap_metadata() {
    // A const-address cell without any heap metadata array (e.g. a stack-local
    // constant-index access) must NOT trip the guard.
    let mut vc = ChcVc::new();
    vc.declare_var("_main_mem_i16_at_0xc000000004_bv64", Sort::bitvec(64));
    assert!(!has_scalarized_obj_size_bounds(&vc));
}

#[test]
fn test_scalarized_obj_size_bounds_requires_const_address_cell() {
    // Heap metadata present but no scalarized const-address cell: nothing for
    // const-prop to unsoundly scalarize, so the guard stays off.
    let mut vc = ChcVc::new();
    vc.declare_var("obj_size", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    vc.declare_var("_main_5", Sort::bitvec(64));
    assert!(!has_scalarized_obj_size_bounds(&vc));
}

#[test]
fn test_signed_overflow_error_edge_detected() {
    // error :- bb0, not(bvsdiv(bvmul(count, 16), 16) == count)  — the byte-offset
    // overflow check.
    let count = bv64("count");
    let size = Expr::bitvec_const(16u64, 64);
    let check = count.clone().bvmul(size.clone()).bvsdiv(size).eq(count.clone()).not();
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![count])), vec![check]),
        RelationApp::nullary("error"),
    ));
    assert!(has_signed_overflow_error_edge(&vc));
}

#[test]
fn test_plain_signed_division_edge_not_detected() {
    // Ordinary signed division (no bvmul numerator) must NOT trip the guard.
    let a = bv64("a");
    let b = bv64("b");
    let edge = a.clone().bvsdiv(b.clone()).eq(Expr::bitvec_const(0u64, 64));
    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64), Sort::bitvec(64)]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![a, b])), vec![edge]),
        RelationApp::nullary("error"),
    ));
    assert!(!has_signed_overflow_error_edge(&vc));
}

#[test]
fn test_block_relation_cycle_detection() {
    // bb0 -> bb1 -> bb0 is a loop back-edge.
    let x = bv64("x");
    let mut cyclic = ChcVc::new();
    cyclic.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
    cyclic.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(64)]));
    cyclic.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone()])), vec![]),
        RelationApp::new("bb1", vec![x.clone()]),
    ));
    cyclic.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![x.clone()])), vec![]),
        RelationApp::new("bb0", vec![x.clone()]),
    ));
    assert!(has_block_relation_cycle(&cyclic));

    // bb0 -> bb1 -> bb2 is acyclic.
    let mut acyclic = ChcVc::new();
    acyclic.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
    acyclic.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(64)]));
    acyclic.add_relation(RelationDecl::new("bb2", vec![Sort::bitvec(64)]));
    acyclic.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone()])), vec![]),
        RelationApp::new("bb1", vec![x.clone()]),
    ));
    acyclic.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![x.clone()])), vec![]),
        RelationApp::new("bb2", vec![x]),
    ));
    assert!(!has_block_relation_cycle(&acyclic));
}
