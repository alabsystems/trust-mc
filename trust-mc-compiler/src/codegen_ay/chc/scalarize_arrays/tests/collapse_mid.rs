// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Part of #40: fragment-composition `__mid_bbN` array alias chains must not
//! defeat scalarization. Before the collapse pre-pass, a frame rule like
//! `bb1(mem) ∧ (= mem__mid_bb2 mem) → bb2(mem__mid_bb2)` left a whole-array
//! mention (`mem__mid_bb2`) that the residual fail-closed check treated as an
//! unconstrained free array, banning `mem` from scalarization in EVERY rule —
//! dragging Array-sorted params into all loop predicates (the ArrayParamLimit
//! PDR-stall class).

use super::super::collapse_mid_aliases::collapse_mid_aliases;
use super::super::rewrite::scalarize_vc;
use super::{arr_sort, bv32_sort, bv64_const};
use ay_bindings::Expr;
use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};

/// Two-rule VC: rule 0 does const-index work on `mem` (scalarizable);
/// rule 1 is a pure frame chain threading `mem` through a `__mid_bb2` alias.
fn build_mid_chain_vc(frame_constraints: Vec<Expr>, frame_head_arg: Expr) -> ChcVc {
    let mem_in = Expr::var("mem", arr_sort());
    let mem_out = Expr::var("mem__out", arr_sort());
    let x = Expr::var("x", bv32_sort());
    let x_out = Expr::var("x__out", bv32_sort());
    let addr = bv64_const(0x10);

    let mut vc = ChcVc::new();
    for (name, sort) in [
        ("mem", arr_sort()),
        ("mem__out", arr_sort()),
        ("mem__mid_bb2", arr_sort()),
        ("x", bv32_sort()),
        ("x__out", bv32_sort()),
    ] {
        vc.add_var(VarDecl::new(name, sort));
    }
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort(), bv32_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort(), bv32_sort()]));
    vc.add_relation(RelationDecl::new("bb2", vec![arr_sort()]));

    // Rule 0: bb0(mem, x) ∧ mem__out = store(mem, 0x10, x) ∧ x__out = select(mem, 0x10)
    //         → bb1(mem__out, x__out)
    let store_constraint = mem_out.clone().eq(mem_in.clone().store(addr.clone(), x.clone()));
    let select_constraint = x_out.clone().eq(mem_in.clone().select(addr));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![mem_in.clone(), x.clone()])),
            vec![store_constraint, select_constraint],
        ),
        RelationApp::new("bb1", vec![mem_out, x_out]),
    ));

    // Rule 1: bb1(mem, x) ∧ <frame_constraints> → bb2(<frame_head_arg>)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![mem_in, x])), frame_constraints),
        RelationApp::new("bb2", vec![frame_head_arg]),
    ));
    vc
}

fn mid_identity() -> Expr {
    Expr::var("mem__mid_bb2", arr_sort()).eq(Expr::var("mem", arr_sort()))
}

#[test]
fn collapse_substitutes_mid_alias_and_drops_identity() {
    let mut vc = build_mid_chain_vc(vec![mid_identity()], Expr::var("mem__mid_bb2", arr_sort()));
    collapse_mid_aliases(&mut vc);

    let frame_rule = &vc.rules[1];
    // Identity conjunct dropped as tautological after substitution.
    assert_eq!(frame_rule.body.constraints.iter().count(), 0);
    // Head arg substituted to the canonical name.
    let head_arg = &frame_rule.head.args[0];
    assert_eq!(
        format!("{head_arg:?}").contains("mem__mid_bb2"),
        false,
        "mid alias must be substituted out of the head args"
    );
}

#[test]
fn mid_alias_chain_no_longer_bans_scalarization() {
    let mut vc = build_mid_chain_vc(vec![mid_identity()], Expr::var("mem__mid_bb2", arr_sort()));
    scalarize_vc(&mut vc);

    // Success criterion (#40): no relation keeps an Array-sorted parameter.
    for rel in &vc.relations {
        for sort in &rel.arg_sorts {
            assert!(
                !sort.is_array(),
                "relation {} still carries an Array-sorted param after scalarization",
                rel.name
            );
        }
    }
}

#[test]
fn non_identity_mid_definition_fails_closed() {
    // The mid var has a REAL definition (a store), so the rule must be left
    // untouched and the residual ban must keep `mem` un-scalarized (sound).
    let mem_in = Expr::var("mem", arr_sort());
    let mid = Expr::var("mem__mid_bb2", arr_sort());
    let store_def =
        mid.clone().eq(mem_in.clone().store(bv64_const(0x20), Expr::bitvec_const(7u64, 32)));
    let mut vc =
        build_mid_chain_vc(vec![store_def, mid_identity()], Expr::var("mem__mid_bb2", arr_sort()));
    let with_guard = vc.rules[1].body.constraints.iter().count();
    collapse_mid_aliases(&mut vc);
    assert_eq!(
        vc.rules[1].body.constraints.iter().count(),
        with_guard,
        "rule with a non-identity mid definition must be left untouched"
    );

    scalarize_vc(&mut vc);
    let bb2 = vc.relations.iter().find(|r| r.name == "bb2").expect("bb2 exists");
    assert!(
        bb2.arg_sorts.iter().any(|s| s.is_array()),
        "fail-closed: mem must stay un-scalarized when the mid var has a real definition"
    );
}
