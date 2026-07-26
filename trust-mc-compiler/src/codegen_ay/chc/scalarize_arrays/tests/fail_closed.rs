// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Fail-closed regression tests for the two scalarize/const-fold soundness
//! holes:
//!
//! 1. A select with a symbolic index discovered only AFTER identification
//!    (at rewrite time) must NOT lower to an unconstrained `_select_any_N`
//!    free variable — free vars let the solver fabricate counterexample
//!    witnesses (false CTREX). The array's scalarization must unwind instead.
//! 2. `apply_const_folding` must NOT fold a `const_map`-miss select to
//!    `uniform_default` unless the uniform-init precondition actually holds
//!    (no store override hiding behind the `const_array` root, and the
//!    uniform state provably reaches the read). Otherwise reads of a lane
//!    that holds an overridden value would fold to the wrong constant
//!    (false PROOF / false CTREX).

use std::collections::BTreeMap;

use num_bigint::BigInt;

use super::super::const_fold::{ConstFoldInfo, identify_const_foldable_arrays};
use super::super::const_fold_apply::apply_const_folding;
use super::super::rewrite::RewriteMaps;
use super::super::{ConstIdx, RewriteContext, ScalarInfo, rewrite_expr};
use super::{arr_sort, bv32_sort, bv64_const, bv64_sort, expr_mentions_name};
use ay_bindings::Expr;
use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};

// ---------------------------------------------------------------------------
// Hole 1: rewrite-time symbolic select must fail closed (no free var)
// ---------------------------------------------------------------------------

/// A symbolic-index select on a scalarized array discovered only at rewrite
/// time (i.e. after identification built `ScalarInfo`) must not be lowered to
/// an unconstrained free variable. The rewrite must leave the expression
/// untouched and report the array for fail-closed rejection.
#[test]
fn test_post_identification_symbolic_select_produces_no_free_var() {
    let idx0 = ConstIdx { value: BigInt::from(0u64), width: 64 };
    let infos = vec![ScalarInfo {
        input_name: "arr".to_string(),
        output_name: "arr__out".to_string(),
        elem_sort: bv32_sort(),
        index_to_scalar: BTreeMap::from([(idx0, "arr_at_0x0_bv64".to_string())]),
    }];
    let maps = RewriteMaps::new(&infos);
    let mut ctx = RewriteContext::new();

    let sym_idx = Expr::var("sym_idx", bv64_sort());
    let constraint =
        Expr::var("read__out", bv32_sort()).eq(Expr::var("arr", arr_sort()).select(sym_idx));

    let rewritten = rewrite_expr(&constraint, &infos, &maps, &mut ctx);

    assert_eq!(
        rewritten, constraint,
        "a rewrite-time symbolic select must be left untouched, not replaced",
    );
    assert!(
        !rewritten.to_string().contains("select_any")
            && !rewritten.to_string().contains("dead_const_lane"),
        "no fallback variable may appear in the rewritten expression",
    );
    assert!(
        ctx.rejected_arrays().contains("arr"),
        "the array must be reported for fail-closed rejection",
    );
    assert!(
        ctx.take_extra_vars().is_empty(),
        "no free fallback variable may be minted for a symbolic select",
    );
}

/// Same property on the OUTPUT array name.
#[test]
fn test_post_identification_symbolic_output_select_produces_no_free_var() {
    let idx0 = ConstIdx { value: BigInt::from(0u64), width: 64 };
    let infos = vec![ScalarInfo {
        input_name: "arr".to_string(),
        output_name: "arr__out".to_string(),
        elem_sort: bv32_sort(),
        index_to_scalar: BTreeMap::from([(idx0, "arr_at_0x0_bv64".to_string())]),
    }];
    let maps = RewriteMaps::new(&infos);
    let mut ctx = RewriteContext::new();

    let sym_idx = Expr::var("sym_idx", bv64_sort());
    let constraint =
        Expr::var("read__out", bv32_sort()).eq(Expr::var("arr__out", arr_sort()).select(sym_idx));

    let rewritten = rewrite_expr(&constraint, &infos, &maps, &mut ctx);

    assert_eq!(rewritten, constraint, "symbolic output select must be left untouched");
    assert!(
        ctx.rejected_arrays().contains("arr"),
        "rejection must be recorded under the INPUT name so identification can ban it",
    );
    assert!(ctx.take_extra_vars().is_empty(), "no free fallback variable may be minted");
}

// ---------------------------------------------------------------------------
// Hole 2: const_map miss must not fold to an unverified uniform_default
// ---------------------------------------------------------------------------

/// Build the override VC: the entry rule initializes `arr` to
/// `store(const_array(7), #x10, 9)` — uniform default 7 EXCEPT lane 0x10 —
/// and a transition reads `arr` at `read_idx`.
fn override_vc(read_idx: Expr) -> ChcVc {
    let arr = Expr::var("arr", arr_sort());
    let arr_out = Expr::var("arr__out", arr_sort());
    let idx = Expr::var("idx", bv64_sort());
    let read_out = Expr::var("read__out", bv32_sort());

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("arr", arr_sort()));
    vc.add_var(VarDecl::new("arr__out", arr_sort()));
    vc.add_var(VarDecl::new("idx", bv64_sort()));
    vc.add_var(VarDecl::new("read__out", bv32_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort(), bv64_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort(), bv32_sort()]));

    let init = Expr::const_array(bv64_sort(), Expr::bitvec_const(7, 32))
        .store(bv64_const(0x10), Expr::bitvec_const(9, 32));
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![arr.clone().eq(init)]),
        RelationApp::new("bb0", vec![arr.clone(), idx.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![arr.clone(), idx])),
            vec![arr_out.clone().eq(arr.clone()), read_out.clone().eq(arr.select(read_idx))],
        ),
        RelationApp::new("bb1", vec![arr_out, read_out]),
    ));
    vc
}

fn vc_constraint_strings(vc: &ChcVc) -> Vec<String> {
    vc.rules.iter().flat_map(|rule| rule.body.constraints.iter().map(|c| c.to_string())).collect()
}

/// A SYMBOLIC select against `store(const_array(7), #x10, 9)` may observe the
/// overridden lane, so folding it to the uniform default 7 is wrong (the true
/// value at 0x10 is 9). Identification's blind spot produces exactly this fold
/// candidate (`const_map` empty, `uniform_default = 7`); the apply-time
/// invariant check must reject it and leave the VC untouched.
#[test]
fn test_apply_rejects_uniform_default_fold_over_store_override() {
    let mut vc = override_vc(Expr::var("idx", bv64_sort()));

    let fold_infos = identify_const_foldable_arrays(&vc);
    let arr_info = fold_infos
        .iter()
        .find(|info| info.input_name == "arr")
        .expect("identification's blind spot should still nominate `arr` for folding");
    assert!(arr_info.const_map.is_empty(), "no const-index selects were observed");
    assert_eq!(
        arr_info.uniform_default,
        Some(Expr::bitvec_const(7, 32)),
        "identification records the const_array root default, ignoring the override",
    );

    let before = vc_constraint_strings(&vc);
    apply_const_folding(&mut vc, &fold_infos);
    let after = vc_constraint_strings(&vc);

    assert_eq!(before, after, "the fail-closed check must leave the VC untouched");
    assert!(
        vc.rules[1]
            .body
            .constraints
            .iter()
            .any(|c| { expr_mentions_name(c, "arr") && c.to_string().contains("select") }),
        "the symbolic select must survive un-folded",
    );
    assert!(
        vc.relations.iter().any(|rel| rel.arg_sorts.iter().any(|s| s.is_array())),
        "the array must remain in relation signatures",
    );
}

/// A post-identification select at the STORED index (`#x10`, missing from
/// `const_map` because identification never saw it) must NOT fold to the
/// uniform default: the lane actually holds the override value 9.
#[test]
fn test_apply_rejects_const_map_miss_at_stored_index() {
    let mut vc = override_vc(bv64_const(0x10));

    // Simulate the unchecked precondition directly: a fold candidate whose
    // const_map does not cover the select (as if the select appeared only
    // after identification).
    let fold_infos = vec![ConstFoldInfo {
        input_name: "arr".to_string(),
        output_name: "arr__out".to_string(),
        const_map: BTreeMap::new(),
        uniform_default: Some(Expr::bitvec_const(7, 32)),
    }];

    let before = vc_constraint_strings(&vc);
    apply_const_folding(&mut vc, &fold_infos);
    let after = vc_constraint_strings(&vc);

    assert_eq!(
        before, after,
        "a const_map-miss select at a stored index must not fold to uniform_default",
    );
    assert!(
        vc.rules[1]
            .body
            .constraints
            .iter()
            .any(|c| { expr_mentions_name(c, "arr") && c.to_string().contains("select") }),
        "the constant-index select must survive un-folded",
    );
}

/// Uniform defaults recorded from TRANSITION inits alone say nothing about the
/// entry (havoc) state; a read of the pre-init state must not fold.
#[test]
fn test_apply_rejects_uniform_default_without_entry_init() {
    let arr = Expr::var("arr", arr_sort());
    let arr_out = Expr::var("arr__out", arr_sort());
    let idx = Expr::var("idx", bv64_sort());
    let read_out = Expr::var("read__out", bv32_sort());

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("arr", arr_sort()));
    vc.add_var(VarDecl::new("arr__out", arr_sort()));
    vc.add_var(VarDecl::new("idx", bv64_sort()));
    vc.add_var(VarDecl::new("read__out", bv32_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort(), bv64_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort(), bv32_sort()]));

    // Entry rule HAVOCS `arr` (no initialization).
    vc.add_rule(Rule::new(
        RuleBody::new(None, Vec::new()),
        RelationApp::new("bb0", vec![arr.clone(), idx.clone()]),
    ));
    // The transition initializes the POST-state but reads the PRE-state.
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![arr.clone(), idx.clone()])),
            vec![
                arr_out.clone().eq(Expr::const_array(bv64_sort(), Expr::bitvec_const(7, 32))),
                read_out.clone().eq(arr.select(idx)),
            ],
        ),
        RelationApp::new("bb1", vec![arr_out, read_out]),
    ));

    let fold_infos = identify_const_foldable_arrays(&vc);
    let before = vc_constraint_strings(&vc);
    apply_const_folding(&mut vc, &fold_infos);
    let after = vc_constraint_strings(&vc);

    assert_eq!(
        before, after,
        "a read of the entry havoc state must not fold to a transition-only default",
    );
}

/// Positive control: a genuinely uniform array (every init is
/// `const_array(7)`, entry included, identity-threaded) must still fold —
/// the #4097 rescue stays intact.
#[test]
fn test_apply_still_folds_verified_uniform_array() {
    let arr = Expr::var("arr", arr_sort());
    let arr_out = Expr::var("arr__out", arr_sort());
    let idx = Expr::var("idx", bv64_sort());
    let read_out = Expr::var("read__out", bv32_sort());

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("arr", arr_sort()));
    vc.add_var(VarDecl::new("arr__out", arr_sort()));
    vc.add_var(VarDecl::new("idx", bv64_sort()));
    vc.add_var(VarDecl::new("read__out", bv32_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort(), bv64_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort(), bv32_sort()]));

    vc.add_rule(Rule::new(
        RuleBody::new(
            None,
            vec![arr.clone().eq(Expr::const_array(bv64_sort(), Expr::bitvec_const(7, 32)))],
        ),
        RelationApp::new("bb0", vec![arr.clone(), idx.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![arr.clone(), idx])),
            vec![
                arr_out.clone().eq(arr.clone()),
                read_out.clone().eq(arr.select(Expr::var("idx", bv64_sort()))),
            ],
        ),
        RelationApp::new("bb1", vec![arr_out, read_out]),
    ));

    let fold_infos = identify_const_foldable_arrays(&vc);
    assert!(
        fold_infos.iter().any(|info| info.input_name == "arr"),
        "uniform array should be nominated",
    );
    apply_const_folding(&mut vc, &fold_infos);

    assert!(
        vc.relations.iter().all(|rel| rel.arg_sorts.iter().all(|s| !s.is_array())),
        "the verified uniform array should be removed from relation signatures",
    );
    assert!(
        vc.rules
            .iter()
            .flat_map(|rule| rule.body.constraints.iter())
            .all(|c| !expr_mentions_name(c, "arr") && !expr_mentions_name(c, "arr__out")),
        "no residual reference to the folded array may remain",
    );
    assert!(
        vc.rules[1]
            .body
            .constraints
            .iter()
            .any(|c| c.to_string().contains("read__out") && c.to_string().contains("#x00000007")),
        "the symbolic select must fold to the verified uniform default 7",
    );
}
