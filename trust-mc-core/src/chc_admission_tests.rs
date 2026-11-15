// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for the AY executor admission estimate.

use super::*;
use crate::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody};

#[test]
fn empty_vc_is_admitted() {
    let vc = ChcVc::new();
    let estimate = estimate_ay_admission(&vc);
    assert_eq!(estimate, AyAdmissionEstimate::default());
    assert_eq!(estimate.first_exceeded(), None);
}

/// One transition `bb0(x, mem) ∧ x = 0 => bb1(x, mem)` with a bit-vector and
/// an array column: every occurrence is charged, an array sort is three nodes.
#[test]
fn charges_every_variable_occurrence() {
    let bv = Sort::bitvec(32);
    let mem = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let mut vc = ChcVc::new();
    let x = vc.declare_var("x", bv.clone());
    let m = vc.declare_var("mem", mem.clone());
    vc.add_relation(RelationDecl::new("bb0", vec![bv.clone(), mem.clone()]));
    vc.add_relation(RelationDecl::new("bb1", vec![bv, mem]));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone(), m.clone()])),
            vec![x.clone().eq(Expr::bitvec_const(0u64, 32))],
        ),
        RelationApp::new("bb1", vec![x, m]),
    ));

    let estimate = estimate_ay_admission(&vc);
    // Roots: the constraint, two body arguments, two head arguments.
    assert_eq!(estimate.expr_roots, 5);
    // Sort nodes: `x` three times (1 each), `mem` twice (3 each).
    assert_eq!(estimate.sort_nodes, 3 + 6);
    // Name bytes: "x" three times, "mem" twice.
    assert_eq!(estimate.name_bytes, 3 + 6);
    // Expression nodes: `(= x #x0)` is 3 nodes, plus four argument leaves.
    assert_eq!(estimate.expr_nodes, 3 + 4);
    assert_eq!(estimate.first_exceeded(), None);
}

/// A datatype's definition is expanded (and its names charged) once; later
/// occurrences of the same sort cost one node.
#[test]
fn datatype_definition_is_expanded_once() {
    let pair = Sort::struct_type("Pair", [("fst", Sort::bitvec(8)), ("snd", Sort::bool())]);
    let mut vc = ChcVc::new();
    let p = vc.declare_var("p", pair.clone());
    vc.add_relation(RelationDecl::new("bb0", vec![pair.clone()]));
    vc.add_relation(RelationDecl::new("bb1", vec![pair]));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![p.clone()])), vec![]),
        RelationApp::new("bb1", vec![p]),
    ));

    let estimate = estimate_ay_admission(&vc);
    // First occurrence: the datatype node plus its two field sorts; second: one node.
    assert_eq!(estimate.sort_nodes, 3 + 1);
    // "p" twice, plus "Pair", "Pair_mk", "fst", "snd" once.
    assert_eq!(estimate.name_bytes, 2 + "Pair".len() + "Pair_mk".len() + "fst".len() + "snd".len());
}

#[test]
fn first_exceeded_names_the_ay_resource() {
    let admitted = AyAdmissionEstimate {
        expr_roots: AY_MAX_EXECUTOR_EXPR_ROOTS,
        expr_nodes: AY_MAX_DT_EXPR_NODES,
        sort_nodes: AY_MAX_DT_SORT_NODES,
        name_bytes: AY_MAX_EXECUTOR_SURFACE_NAME_BYTES,
    };
    assert_eq!(admitted.first_exceeded(), None, "the caps are inclusive");
    assert_eq!(
        AyAdmissionEstimate { sort_nodes: AY_MAX_DT_SORT_NODES + 1, ..admitted }.first_exceeded(),
        Some("datatype sort nodes")
    );
    assert_eq!(
        AyAdmissionEstimate { expr_roots: AY_MAX_EXECUTOR_EXPR_ROOTS + 1, ..admitted }
            .first_exceeded(),
        Some("expression roots")
    );
    assert_eq!(
        AyAdmissionEstimate { expr_nodes: AY_MAX_DT_EXPR_NODES + 1, ..admitted }.first_exceeded(),
        Some("datatype expression nodes")
    );
    assert_eq!(
        AyAdmissionEstimate { name_bytes: AY_MAX_EXECUTOR_SURFACE_NAME_BYTES + 1, ..admitted }
            .first_exceeded(),
        Some("executor surface name bytes")
    );
}

/// The corpus shape: every block relation carries the whole frame. 200 blocks
/// of 100 bit-vector columns charge 40 000 sort nodes against the 32 768 cap
/// with only identity transitions; projecting the unread columns admits it.
#[test]
fn wide_frame_exceeds_the_sort_node_cap_until_projected() {
    let bv = Sort::bitvec(64);
    let mut vc = ChcVc::new();
    let cols: Vec<Expr> = (0..100).map(|i| vc.declare_var(format!("_{i}"), bv.clone())).collect();
    for b in 0..200 {
        vc.add_relation(RelationDecl::new(format!("bb{b}"), vec![bv.clone(); 100]));
    }
    for b in 1..200 {
        vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::new(format!("bb{}", b - 1), cols.clone())), vec![]),
            RelationApp::new(format!("bb{b}"), cols.clone()),
        ));
    }
    let before = estimate_ay_admission(&vc);
    assert_eq!(before.sort_nodes, 199 * 200);
    assert_eq!(before.expr_roots, 199 * 200);
    assert_eq!(before.first_exceeded(), Some("datatype sort nodes"));

    assert_eq!(vc.prune_unconstrained_relation_args(), 200 * 100);
    let after = estimate_ay_admission(&vc);
    assert_eq!(after, AyAdmissionEstimate::default());
    assert_eq!(after.first_exceeded(), None);
}
