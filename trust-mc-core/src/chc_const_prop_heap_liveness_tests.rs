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

/// A VC with the heap metadata arrays, one scalarized cell of `cell_width`
/// bits at `cell_addr`, entry-rule `facts`, and `stores` on a bb0 -> bb1 edge.
fn heap_cell_vc(cell_addr: u64, cell_width: u32, facts: Vec<Expr>, stores: Vec<Expr>) -> ChcVc {
    let size_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
    let mut vc = ChcVc::new();
    let obj_size = vc.declare_var("obj_size", size_sort.clone());
    vc.declare_var("obj_size__out", size_sort.clone());
    vc.declare_var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    vc.declare_var(format!("_main_mem_u8_at_0x{cell_addr:x}_bv64"), Sort::bitvec(cell_width));
    vc.add_relation(RelationDecl::new("bb0", vec![size_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb1", vec![size_sort.clone()]));
    vc.add_rule(Rule::new(RuleBody::new(None, facts), RelationApp::new("bb0", vec![obj_size.clone()])));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![obj_size])), stores),
        RelationApp::new("bb1", vec![Expr::var("obj_size__out", size_sort)]),
    ));
    vc
}

fn size_store(obj: u64, size: Expr) -> Expr {
    let size_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
    Expr::var("obj_size__out", size_sort.clone())
        .eq(Expr::var("obj_size", size_sort).store(Expr::bitvec_const(obj, 32), size))
}

fn size_fact(obj: u64, size: u64) -> Expr {
    Expr::var("obj_size", Sort::array(Sort::bitvec(32), Sort::bitvec(32)))
        .select(Expr::bitvec_const(obj, 32))
        .eq(Expr::bitvec_const(size, 32))
}

#[test]
fn test_obj_size_guard_off_when_every_cell_is_inside_a_constant_size() {
    // `Box::new(DV { a, b })` (obj 0x34, size 2) with both bytes scalarized: no
    // cell is out of bounds, so constant propagation may run
    // (fix/chc-lost-writes: the drop's obligations stayed symbolic otherwise).
    let heap = heap_cell_vc(0x34_0000_0001, 8, vec![], vec![size_store(0x34, Expr::bitvec_const(2u64, 32))]);
    assert!(!has_scalarized_obj_size_bounds(&heap));
    // A stack object sized by an entry-rule fact counts the same way.
    let stack = heap_cell_vc(0x5_0000_0001, 8, vec![size_fact(5, 2)], vec![]);
    assert!(!has_scalarized_obj_size_bounds(&stack));
}

#[test]
fn test_obj_size_guard_fires_on_a_cell_past_its_object() {
    // offset 2 of a 2-byte object: the out-of-bounds cell the guard protects.
    let past = heap_cell_vc(0x34_0000_0002, 8, vec![], vec![size_store(0x34, Expr::bitvec_const(2u64, 32))]);
    assert!(has_scalarized_obj_size_bounds(&past));
    // A 16-bit cell at offset 1 of a 2-byte object ends past it too.
    let straddle = heap_cell_vc(0x34_0000_0001, 16, vec![], vec![size_store(0x34, Expr::bitvec_const(2u64, 32))]);
    assert!(has_scalarized_obj_size_bounds(&straddle));
}

#[test]
fn test_obj_size_guard_fires_without_one_constant_size() {
    // A symbolic size (`realloc/shrink`: the layout's size).
    let symbolic = heap_cell_vc(0x34_0000_0000, 8, vec![], vec![size_store(0x34, Expr::var("n", Sort::bitvec(32)))]);
    assert!(has_scalarized_obj_size_bounds(&symbolic));
    // Two sizes for one object (a resize).
    let resized = heap_cell_vc(
        0x34_0000_0000,
        8,
        vec![size_fact(0x34, 8)],
        vec![size_store(0x34, Expr::bitvec_const(2u64, 32))],
    );
    assert!(has_scalarized_obj_size_bounds(&resized));
    // A store into obj_size at a symbolic index may resize any object.
    let size_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
    let symbolic_index = Expr::var("obj_size__out", size_sort.clone()).eq(Expr::var("obj_size", size_sort)
        .store(Expr::var("o", Sort::bitvec(32)), Expr::bitvec_const(4u64, 32)));
    let any = heap_cell_vc(0x5_0000_0000, 8, vec![size_fact(5, 2)], vec![symbolic_index]);
    assert!(has_scalarized_obj_size_bounds(&any));
    // An object with no size at all.
    let no_size = heap_cell_vc(0x34_0000_0000, 8, vec![], vec![]);
    assert!(has_scalarized_obj_size_bounds(&no_size));
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
