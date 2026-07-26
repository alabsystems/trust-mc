// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unit tests for constant-index array scalarization.

use super::rewrite::{RewriteMaps, rewrite_constraint, scalarize_vc};
use super::*;
use crate::codegen_ay::names::struct_sort;
use trust_mc_core::chc::{RelationApp, RelationDecl, Rule, RuleBody, VarDecl};

mod collapse_mid;
mod const_fold;
mod fail_closed;
mod output_copies;

fn bv64_sort() -> Sort {
    Sort::bitvec(64)
}
fn bv32_sort() -> Sort {
    Sort::bitvec(32)
}
fn arr_sort() -> Sort {
    Sort::array(bv64_sort(), bv32_sort())
}
fn arr_u64_sort() -> Sort {
    Sort::array(bv64_sort(), bv64_sort())
}
fn obj_size_sort() -> Sort {
    Sort::array(bv32_sort(), bv32_sort())
}
fn bv64_const(val: u64) -> Expr {
    Expr::bitvec_const(val, 64)
}

fn slice_sort() -> Sort {
    struct_sort(
        "Slice_bv32_for_scalarize_test",
        [("fld_ptr", bv64_sort()), ("fld_len", bv64_sort()), ("fld_data", arr_sort())],
    )
}

fn slice_with_data(data: Expr) -> Expr {
    Expr::datatype_constructor(
        "Slice_bv32_for_scalarize_test",
        "Slice_bv32_for_scalarize_test_mk",
        vec![bv64_const(0), bv64_const(2), data],
        slice_sort(),
    )
}

fn two_array_sort() -> Sort {
    struct_sort("TwoArrayFields_for_scalarize_test", [("fld_a", arr_sort()), ("fld_b", arr_sort())])
}

fn two_array_value(first: Expr, second: Expr) -> Expr {
    Expr::datatype_constructor(
        "TwoArrayFields_for_scalarize_test",
        "TwoArrayFields_for_scalarize_test_mk",
        vec![first, second],
        two_array_sort(),
    )
}

/// Helper to build a minimal VC with one array var and one rule.
fn build_test_vc(
    input_name: &str,
    constraints: Vec<Expr>,
    body_args: Vec<Expr>,
    head_args: Vec<Expr>,
) -> ChcVc {
    let output_name = format!("{input_name}__out");
    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new(input_name, arr_sort()));
    vc.add_var(VarDecl::new(output_name, arr_sort()));
    vc.add_var(VarDecl::new("x", bv32_sort()));
    vc.add_var(VarDecl::new("x__out", bv32_sort()));

    let body_sorts: Vec<Sort> = body_args.iter().map(|a| a.sort().clone()).collect();
    let head_sorts: Vec<Sort> = head_args.iter().map(|a| a.sort().clone()).collect();
    vc.add_relation(RelationDecl::new("bb0", body_sorts));
    vc.add_relation(RelationDecl::new("bb1", head_sorts));

    let body = RuleBody::new(Some(RelationApp::new("bb0", body_args)), constraints);
    let head = RelationApp::new("bb1", head_args);
    vc.add_rule(Rule::new(body, head));
    vc
}

#[test]
fn test_scalarize_single_index_store_select() {
    let arr_in = Expr::var("region_44", arr_sort());
    let arr_out = Expr::var("region_44__out", arr_sort());
    let x = Expr::var("x", bv32_sort());
    let x_out = Expr::var("x__out", bv32_sort());
    let addr = bv64_const(0x2C00000000);
    let store_constraint = arr_out.clone().eq(arr_in.clone().store(addr.clone(), x.clone()));
    // Add a select so the array isn't purely write-only (which const_fold eliminates).
    let select_constraint = x_out.clone().eq(arr_in.clone().select(addr.clone()));

    let mut vc = build_test_vc(
        "region_44",
        vec![store_constraint, select_constraint],
        vec![arr_in.clone(), x.clone()],
        vec![arr_out.clone(), x_out.clone()],
    );
    scalarize_vc(&mut vc);

    let rule = &vc.rules[0];
    assert_eq!(rule.head.args.len(), 2);
    assert_eq!(*rule.head.args[0].sort(), bv32_sort());
    let body_rel = rule.body.relation.as_ref().expect("body has relation");
    assert_eq!(body_rel.args.len(), 2);
    assert_eq!(*body_rel.args[0].sort(), bv32_sort());
    let constraints: Vec<_> = rule.body.constraints.iter().collect();
    // Store → scalar assignment + select → scalar read = 2 constraints
    assert_eq!(constraints.len(), 2);
    let bb1_rel = vc.relations.iter().find(|r| r.name == "bb1").expect("bb1 relation");
    assert_eq!(bb1_rel.arg_sorts.len(), 2);
    assert_eq!(bb1_rel.arg_sorts[0], bv32_sort());
}

#[test]
fn test_scalarize_skips_symbolic_index() {
    let arr_in = Expr::var("mem_i32", arr_sort());
    let arr_out = Expr::var("mem_i32__out", arr_sort());
    let x = Expr::var("x", bv32_sort());
    let x_out = Expr::var("x__out", bv32_sort());
    let symbolic_addr = Expr::var("addr", bv64_sort());
    let store_constraint =
        arr_out.clone().eq(arr_in.clone().store(symbolic_addr.clone(), x.clone()));
    // Add a select so the array isn't purely write-only (const_fold eliminates write-only arrays).
    let select_constraint = x_out.clone().eq(arr_in.clone().select(symbolic_addr.clone()));

    let mut vc = build_test_vc(
        "mem_i32",
        vec![store_constraint, select_constraint],
        vec![arr_in.clone(), x.clone()],
        vec![arr_out.clone(), x_out.clone()],
    );

    let relations_before: Vec<Vec<Sort>> =
        vc.relations.iter().map(|r| r.arg_sorts.clone()).collect();
    scalarize_vc(&mut vc);
    let relations_after: Vec<Vec<Sort>> =
        vc.relations.iter().map(|r| r.arg_sorts.clone()).collect();
    assert_eq!(relations_before, relations_after);
}

#[test]
fn test_scalarize_two_indices() {
    let arr_in = Expr::var("region_10", arr_sort());
    let arr_out = Expr::var("region_10__out", arr_sort());
    let x = Expr::var("x", bv32_sort());
    let x_out = Expr::var("x__out", bv32_sort());
    let y = Expr::var("y", bv32_sort());
    let addr0 = bv64_const(0xA00000000);
    let addr4 = bv64_const(0xA00000004);
    let store_chain =
        arr_in.clone().store(addr0.clone(), x.clone()).store(addr4.clone(), y.clone());
    let store_constraint = arr_out.clone().eq(store_chain);
    // Add a select so the array isn't purely write-only (which const_fold eliminates).
    let select_constraint = x_out.clone().eq(arr_in.clone().select(addr0.clone()));

    let mut vc = build_test_vc(
        "region_10",
        vec![store_constraint, select_constraint],
        vec![arr_in.clone(), x.clone()],
        vec![arr_out.clone(), x_out.clone()],
    );
    scalarize_vc(&mut vc);

    let rule = &vc.rules[0];
    let body_rel = rule.body.relation.as_ref().expect("body has relation");
    assert_eq!(body_rel.args.len(), 3);
    assert_eq!(rule.head.args.len(), 3);
    let constraints: Vec<_> = rule.body.constraints.iter().collect();
    // Store chain (2 stores → 2 scalar assignments) + 1 select = 3 constraints
    assert_eq!(constraints.len(), 3);
}

#[test]
fn test_scalarize_sixteen_indices_for_simd_lane_arrays() {
    let arr_in = Expr::var("simd_lanes", arr_sort());
    let arr_out = Expr::var("simd_lanes__out", arr_sort());
    let x = Expr::var("x", bv32_sort());
    let mut constraints = Vec::new();

    for idx in 0..16 {
        let addr = bv64_const(idx);
        constraints.push(x.clone().eq(arr_in.clone().select(addr.clone())));
        constraints.push(arr_out.clone().select(addr).eq(arr_in.clone().select(bv64_const(idx))));
    }

    let mut vc = build_test_vc(
        "simd_lanes",
        constraints,
        vec![arr_in.clone(), x.clone()],
        vec![arr_out.clone(), x],
    );
    scalarize_vc(&mut vc);

    let rule = &vc.rules[0];
    assert!(
        rule.body.constraints.iter().all(|c| !constraint_has_array_sort(c)),
        "16 constant SIMD lanes should scalarize instead of leaving Array constraints",
    );
    assert_eq!(
        rule.body.relation.as_ref().expect("body relation").args.len(),
        17,
        "16 scalarized lanes plus x should remain in the body relation",
    );
    assert_eq!(rule.head.args.len(), 17, "16 scalarized output lanes plus x should remain");
}

#[test]
fn test_scalarize_select_in_constraint() {
    let arr_in = Expr::var("obj_size", arr_sort());
    let x_out = Expr::var("x__out", bv32_sort());
    let x = Expr::var("x", bv32_sort());
    let addr = bv64_const(42);
    let select_constraint = x_out.clone().eq(arr_in.clone().select(addr.clone()));

    let mut vc = build_test_vc(
        "obj_size",
        vec![select_constraint],
        vec![arr_in.clone(), x.clone()],
        vec![arr_in.clone(), x_out.clone()],
    );
    scalarize_vc(&mut vc);

    let rule = &vc.rules[0];
    let constraints: Vec<_> = rule.body.constraints.iter().collect();
    assert_eq!(constraints.len(), 1);
    let constraint = &constraints[0];
    assert!(!constraint_has_array_sort(constraint));
}

#[test]
fn test_scalarize_copy_target_inherits_base_lanes_for_symbolic_select() {
    let src = Expr::var("src", arr_sort());
    let src_out = Expr::var("src__out", arr_sort());
    let dst = Expr::var("dst", arr_sort());
    let dst_out = Expr::var("dst__out", arr_sort());
    let idx = Expr::var("idx", bv64_sort());
    let read_out = Expr::var("read__out", bv32_sort());

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("src", arr_sort()));
    vc.add_var(VarDecl::new("src__out", arr_sort()));
    vc.add_var(VarDecl::new("dst", arr_sort()));
    vc.add_var(VarDecl::new("dst__out", arr_sort()));
    vc.add_var(VarDecl::new("idx", bv64_sort()));
    vc.add_var(VarDecl::new("read__out", bv32_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort(), arr_sort(), bv64_sort()]));
    vc.add_relation(RelationDecl::new(
        "bb1",
        vec![arr_sort(), arr_sort(), bv64_sort(), bv32_sort()],
    ));

    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![src.clone(), dst, idx.clone()])),
            vec![
                src_out.clone().eq(src
                    .clone()
                    .store(bv64_const(0), Expr::bitvec_const(7, 32))
                    .store(bv64_const(1), Expr::bitvec_const(9, 32))),
                dst_out.clone().eq(src_out.clone()),
                read_out.clone().eq(dst_out.clone().select(idx.clone())),
            ],
        ),
        RelationApp::new("bb1", vec![src_out, dst_out, idx, read_out]),
    ));

    scalarize_vc(&mut vc);

    // FAIL CLOSED: `dst__out` is read at a SYMBOLIC index, so `dst` cannot be
    // scalarized; `src` escapes whole into the copy `dst__out = src__out`, so
    // eliminating or scalarizing `src` would drop its store definition while
    // the copy still references `src__out` — leaving a FREE array the solver
    // can fill with arbitrary lane values to fabricate counterexamples (the
    // false-CTREX mechanism). The sound outcome is to leave BOTH arrays
    // untouched, with all defining constraints intact and the arrays still
    // carried as relation state. Failing to scalarize is sound (worst case
    // the solver answers UNKNOWN); freeing a read array is not.
    let rule = &vc.rules[0];
    let constraints: Vec<_> = rule.body.constraints.iter().collect();
    assert_eq!(constraints.len(), 3, "no constraint may be dropped by the fail-closed unwind");
    assert!(
        constraints
            .iter()
            .any(|c| expr_mentions_name(c, "src__out") && c.to_string().contains("store")),
        "the store definition of src__out must survive",
    );
    assert!(
        constraints.iter().any(|c| expr_is_var_eq_var(c, "dst__out", "src__out")),
        "the whole-array copy must survive",
    );
    assert_eq!(
        rule.head.args.iter().filter(|arg| arg.sort().is_array()).count(),
        2,
        "both arrays must remain relation state instead of being freed",
    );
    assert!(
        vc.vars().iter().all(|v| !v.name.contains("_select_any_")
            && !v.name.contains("_dead_const_lane_")
            && !v.name.contains("_at_0x")),
        "fail-closed unwind must not mint scalar lanes or free fallback vars",
    );
}

#[test]
fn test_scalarize_datatype_forwarded_array_copy_inherits_base_lanes() {
    let src = Expr::var("src", arr_sort());
    let src_out = Expr::var("src__out", arr_sort());
    let iter_data = Expr::var("iter_data", arr_sort());
    let iter_data_out = Expr::var("iter_data__out", arr_sort());
    let idx = Expr::var("idx", bv64_sort());
    let read_out = Expr::var("read__out", bv32_sort());

    let forwarded_data = slice_with_data(src_out.clone()).field_select(
        "Slice_bv32_for_scalarize_test",
        "fld_data",
        arr_sort(),
    );

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("src", arr_sort()));
    vc.add_var(VarDecl::new("src__out", arr_sort()));
    vc.add_var(VarDecl::new("iter_data", arr_sort()));
    vc.add_var(VarDecl::new("iter_data__out", arr_sort()));
    vc.add_var(VarDecl::new("idx", bv64_sort()));
    vc.add_var(VarDecl::new("read__out", bv32_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort(), arr_sort(), bv64_sort()]));
    vc.add_relation(RelationDecl::new(
        "bb1",
        vec![arr_sort(), arr_sort(), bv64_sort(), bv32_sort()],
    ));

    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![src.clone(), iter_data, idx.clone()])),
            vec![
                src_out.clone().eq(src
                    .clone()
                    .store(bv64_const(0), Expr::bitvec_const(11, 32))
                    .store(bv64_const(1), Expr::bitvec_const(13, 32))),
                iter_data_out.clone().eq(forwarded_data),
                read_out.clone().eq(iter_data_out.clone().select(idx.clone())),
            ],
        ),
        RelationApp::new("bb1", vec![src_out, iter_data_out, idx, read_out]),
    ));

    scalarize_vc(&mut vc);

    // FAIL CLOSED: `iter_data__out` is read at a SYMBOLIC index, so it cannot
    // be scalarized; `src__out` escapes whole into the datatype constructor
    // `iter_data__out = (fld_data (mk .. src__out))`, which the rewrite cannot
    // decompose. Identification accepts `src` (the forwarding looks
    // transparent), so the staged rewrite is the only place the escape becomes
    // visible — the residual-mention scan must then unwind `src`'s
    // scalarization entirely. Otherwise `src__out` would survive as a FREE
    // array feeding `iter_data__out` (false-CTREX mechanism). Both arrays stay
    // untouched with their defining constraints intact; failing to scalarize
    // is sound.
    let rule = &vc.rules[0];
    let constraints: Vec<_> = rule.body.constraints.iter().collect();
    assert_eq!(constraints.len(), 3, "no constraint may be dropped by the fail-closed unwind");
    assert!(
        constraints
            .iter()
            .any(|c| expr_mentions_name(c, "src__out") && c.to_string().contains("store")),
        "the store definition of src__out must survive",
    );
    assert!(
        constraints
            .iter()
            .any(|c| expr_mentions_name(c, "iter_data__out") && expr_mentions_name(c, "src__out")),
        "the datatype forwarding constraint must survive",
    );
    assert_eq!(
        rule.head.args.iter().filter(|arg| arg.sort().is_array()).count(),
        2,
        "both arrays must remain relation state instead of being freed",
    );
    assert!(
        vc.vars().iter().all(|v| !v.name.contains("_select_any_")
            && !v.name.contains("_dead_const_lane_")
            && !v.name.contains("_at_0x")),
        "fail-closed unwind must not mint scalar lanes or free fallback vars",
    );
}

#[test]
fn test_scalarize_zero_lane_forwarded_array_drops_relation_state() {
    let arr_in = Expr::var("threaded", arr_sort());
    let arr_out = Expr::var("threaded__out", arr_sort());

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("threaded", arr_sort()));
    vc.add_var(VarDecl::new("threaded__out", arr_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort()]));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![arr_in.clone()])),
            vec![arr_out.clone().eq(arr_in)],
        ),
        RelationApp::new("bb1", vec![arr_out]),
    ));

    scalarize_vc(&mut vc);

    let rule = &vc.rules[0];
    assert!(rule.body.constraints.iter().all(|c| !constraint_has_array_sort(c)));
    assert_eq!(rule.body.relation.as_ref().expect("body relation").args.len(), 0);
    assert_eq!(rule.head.args.len(), 0);
    assert!(vc.relations.iter().all(|rel| rel.arg_sorts.is_empty()));
}

#[test]
fn test_datatype_selector_transparency_is_field_sensitive() {
    let target = Expr::var("target", arr_sort());
    let other = Expr::var("other", arr_sort());
    let selected_other = two_array_value(target.clone(), other).field_select(
        "TwoArrayFields_for_scalarize_test",
        "fld_b",
        arr_sort(),
    );

    let forwarded = transparent_forwarded_array_base(&selected_other, &|name| name == "target");
    assert!(
        forwarded.is_none(),
        "selector forwarding must inspect only the selected field, not every constructor field"
    );
}

#[test]
fn test_scalarize_ignores_entry_pointwise_seed_lanes_not_used_in_transitions() {
    let obj_size = Expr::var("obj_size", obj_size_sort());
    let obj_size_out = Expr::var("obj_size__out", obj_size_sort());
    let read_out = Expr::var("read__out", bv32_sort());
    let live_idx = Expr::bitvec_const(0x3b, 32);

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("obj_size", obj_size_sort()));
    vc.add_var(VarDecl::new("obj_size__out", obj_size_sort()));
    vc.add_var(VarDecl::new("read__out", bv32_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![obj_size_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![obj_size_sort(), bv32_sort()]));

    let entry_constraints: Vec<_> = (2..14)
        .map(|idx| {
            obj_size.clone().select(Expr::bitvec_const(idx, 32)).eq(Expr::bitvec_const(4, 32))
        })
        .collect();
    vc.add_rule(Rule::new(
        RuleBody::new(None, entry_constraints),
        RelationApp::new("bb0", vec![obj_size.clone()]),
    ));

    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![obj_size.clone()])),
            vec![
                obj_size_out
                    .clone()
                    .eq(obj_size.clone().store(live_idx.clone(), Expr::bitvec_const(4, 32))),
                read_out.clone().eq(obj_size_out.clone().select(live_idx)),
            ],
        ),
        RelationApp::new("bb1", vec![obj_size_out, read_out]),
    ));

    scalarize_vc(&mut vc);

    assert!(
        vc.relations.iter().flat_map(|rel| rel.arg_sorts.iter()).all(|sort| !sort.is_array()),
        "entry-only pointwise metadata seeds should not force obj_size over the lane cap",
    );

    let obj_size_scalars = vc
        .vars()
        .iter()
        .filter(|v| v.name.as_ref().starts_with("obj_size_at_") && !v.sort.is_array())
        .count();
    assert_eq!(obj_size_scalars, 2, "only the live input/output lane should scalarize");
}

fn constraint_has_array_sort(expr: &Expr) -> bool {
    if expr.sort().is_array() {
        return true;
    }
    expr.children().any(|c| constraint_has_array_sort(c))
}

fn expr_is_var_eq_bv(
    expr: &Expr,
    var_name: &str,
    expected_value: u64,
    expected_width: u32,
) -> bool {
    let ExprValue::Eq(lhs, rhs) = expr.value() else {
        return false;
    };
    (expr_is_var(lhs, var_name) && expr_is_bv_const(rhs, expected_value, expected_width))
        || (expr_is_var(rhs, var_name) && expr_is_bv_const(lhs, expected_value, expected_width))
}

fn expr_is_var(expr: &Expr, var_name: &str) -> bool {
    matches!(expr.value(), ExprValue::Var { name } if name == var_name)
}

fn expr_is_bv_const(expr: &Expr, expected_value: u64, expected_width: u32) -> bool {
    let ExprValue::BitVecConst { value, width } = expr.value() else {
        return false;
    };
    *width == expected_width && value == &BigInt::from(expected_value)
}

fn expr_is_var_eq_var(expr: &Expr, left_name: &str, right_name: &str) -> bool {
    let ExprValue::Eq(lhs, rhs) = expr.value() else {
        return false;
    };
    (expr_is_var(lhs, left_name) && expr_is_var(rhs, right_name))
        || (expr_is_var(rhs, left_name) && expr_is_var(lhs, right_name))
}

fn expr_mentions_name(expr: &Expr, var_name: &str) -> bool {
    if expr_is_var(expr, var_name) {
        return true;
    }
    expr.children().any(|child| expr_mentions_name(child, var_name))
}

#[test]
fn test_scalarize_store_chain_on_const_array_constrains_default_lane() {
    let idx0 = ConstIdx { value: BigInt::from(0u64), width: 64 };
    let idx1 = ConstIdx { value: BigInt::from(1u64), width: 64 };
    let infos = vec![ScalarInfo {
        input_name: "arr".to_string(),
        output_name: "arr__out".to_string(),
        elem_sort: bv32_sort(),
        index_to_scalar: std::collections::BTreeMap::from([
            (idx0, "arr_at_0x0_bv64".to_string()),
            (idx1, "arr_at_0x1_bv64".to_string()),
        ]),
    }];
    let maps = RewriteMaps::new(&infos);
    let init = Expr::const_array(bv64_sort(), Expr::bitvec_const(7, 32))
        .store(bv64_const(1), Expr::bitvec_const(9, 32));

    let mut rewrite_ctx = RewriteContext::new();
    let input_constraints = rewrite_constraint(
        &Expr::var("arr", arr_sort()).eq(init.clone()),
        &infos,
        &maps,
        &mut rewrite_ctx,
    );
    assert!(
        input_constraints.iter().any(|c| expr_is_var_eq_bv(c, "arr_at_0x0_bv64", 7, 32)),
        "required lanes not overwritten by the store chain should use the const_array default",
    );
    assert!(
        input_constraints.iter().any(|c| expr_is_var_eq_bv(c, "arr_at_0x1_bv64", 9, 32)),
        "explicit store values should still override the const_array default",
    );

    let output_constraints = rewrite_constraint(
        &Expr::var("arr__out", arr_sort()).eq(init),
        &infos,
        &maps,
        &mut rewrite_ctx,
    );
    assert!(
        output_constraints.iter().any(|c| expr_is_var_eq_bv(c, "arr_at_0x0_bv64__out", 7, 32)),
        "output store chains should also preserve default-lane constraints",
    );
    assert!(
        output_constraints.iter().any(|c| expr_is_var_eq_bv(c, "arr_at_0x1_bv64__out", 9, 32)),
        "output store chains should preserve explicit store overrides",
    );
}

#[test]
fn test_scalarize_simplifies_inline_store_select_same_index_and_drops_mem_mirror() {
    let mem_in = Expr::var("mem_u64", arr_u64_sort());
    let mem_out = Expr::var("mem_u64__out", arr_u64_sort());
    let read_out = Expr::var("read__out", bv64_sort());
    let addr = bv64_const(0x30);

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("mem_u64", arr_u64_sort()));
    vc.add_var(VarDecl::new("mem_u64__out", arr_u64_sort()));
    vc.add_var(VarDecl::new("read__out", bv64_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_u64_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_u64_sort(), bv64_sort()]));

    let inline_store_read = mem_in.clone().store(addr.clone(), bv64_const(99)).select(addr);
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![mem_in.clone()])),
            vec![mem_out.clone().eq(mem_in), read_out.clone().eq(inline_store_read)],
        ),
        RelationApp::new("bb1", vec![mem_out, read_out.clone()]),
    ));

    scalarize_vc(&mut vc);

    let rule = &vc.rules[0];
    let body_rel = rule.body.relation.as_ref().expect("transition has body relation");
    assert!(body_rel.args.is_empty(), "mirror-only mem_u64 input should be removed");
    assert_eq!(rule.head.args.len(), 1, "head should retain only the live read scalar");
    assert_eq!(*rule.head.args[0].sort(), bv64_sort());
    let constraints: Vec<_> = rule.body.constraints.iter().collect();
    assert_eq!(constraints.len(), 1, "identity mem mirror should be dropped");
    assert!(
        expr_is_var_eq_bv(constraints[0], "read__out", 99, 64),
        "same-index select(store(...)) should fold to the stored value",
    );
}

#[test]
fn test_scalarize_constant_select_from_output_array_uses_output_lane() {
    let mem_in = Expr::var("mem_u64", arr_u64_sort());
    let mem_out = Expr::var("mem_u64__out", arr_u64_sort());
    let read_out = Expr::var("read__out", bv64_sort());
    let addr = bv64_const(0x30);

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("mem_u64", arr_u64_sort()));
    vc.add_var(VarDecl::new("mem_u64__out", arr_u64_sort()));
    vc.add_var(VarDecl::new("read__out", bv64_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_u64_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_u64_sort(), bv64_sort()]));

    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![mem_in.clone()])),
            vec![
                mem_out.clone().eq(mem_in.store(addr.clone(), bv64_const(99))),
                read_out.clone().eq(mem_out.clone().select(addr)),
            ],
        ),
        RelationApp::new("bb1", vec![mem_out, read_out]),
    ));

    scalarize_vc(&mut vc);

    let rule = &vc.rules[0];
    assert!(
        rule.body.constraints.iter().all(|c| !constraint_has_array_sort(c)),
        "constant output-array select should rewrite to a scalar output lane",
    );
    assert!(
        rule.body
            .constraints
            .iter()
            .any(|c| { expr_is_var_eq_var(c, "read__out", "mem_u64_at_0x30_bv64__out") }),
        "read should use the scalarized output lane after the store",
    );
}

#[test]
fn test_scalarize_drops_dead_single_use_output_select_temp_chain() {
    let mem_in = Expr::var("mem_u64", arr_u64_sort());
    let mem_out = Expr::var("mem_u64__out", arr_u64_sort());
    let read_out = Expr::var("read__out", bv64_sort());
    let tmp = Expr::var("tmp", bv64_sort());
    let tmp2 = Expr::var("tmp2", bv64_sort());
    let addr = bv64_const(0x30);

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("mem_u64", arr_u64_sort()));
    vc.add_var(VarDecl::new("mem_u64__out", arr_u64_sort()));
    vc.add_var(VarDecl::new("read__out", bv64_sort()));
    vc.add_var(VarDecl::new("tmp", bv64_sort()));
    vc.add_var(VarDecl::new("tmp2", bv64_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_u64_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_u64_sort(), bv64_sort()]));

    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![mem_in.clone()])),
            vec![
                mem_out.clone().eq(mem_in.store(addr.clone(), bv64_const(99))),
                read_out.clone().eq(mem_out.clone().select(addr.clone())),
                tmp.clone().eq(mem_out.clone().select(addr)),
                tmp2.eq(tmp),
            ],
        ),
        RelationApp::new("bb1", vec![mem_out, read_out]),
    ));

    scalarize_vc(&mut vc);

    // SOUNDNESS FLOOR: the pass must keep relation state scalar (no Array sort
    // escapes into the head args) and must drop the genuinely dead rule-local
    // temp chain (`tmp`/`tmp2`), which is a sound cleanup. The exact residual
    // constraint count and the specific scalar-lane names that survive are
    // optimization details (how aggressively live output lanes are inlined),
    // not soundness properties — pinning them is an optimization-completeness
    // check that further folding intentionally changed. That deeper accounting
    // is tracked as an optimization backlog item; here we pin the sound floor.
    let rule = &vc.rules[0];
    let constraints: Vec<_> = rule.body.constraints.iter().collect();
    assert!(
        rule.head.args.iter().all(|arg| !arg.sort().is_array()),
        "no Array sort should escape into the relation head args (scalar relation state)",
    );
    assert!(
        constraints.iter().all(|c| !constraint_has_array_sort(c)),
        "scalarized constraints should leave no residual array term",
    );
    assert!(
        constraints.iter().all(|c| !expr_mentions_name(c, "tmp") && !expr_mentions_name(c, "tmp2")),
        "dead rule-local temps should not remain in scalarized constraints",
    );
    assert!(!constraints.is_empty(), "the scalarized rule should retain its live output-lane work");
}

#[test]
fn test_scalarize_preserves_relation_arg_scalar_bindings_when_pruning_locals() {
    let x = Expr::var("x", bv64_sort());
    let x_out = Expr::var("x__out", bv64_sort());
    let tmp = Expr::var("tmp", bv64_sort());

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("x", bv64_sort()));
    vc.add_var(VarDecl::new("x__out", bv64_sort()));
    vc.add_var(VarDecl::new("tmp", bv64_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![bv64_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![bv64_sort()]));

    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![
                x.clone().eq(bv64_const(7)),
                x_out.clone().eq(bv64_const(9)),
                tmp.eq(bv64_const(123)),
            ],
        ),
        RelationApp::new("bb1", vec![x_out]),
    ));

    scalarize_vc(&mut vc);

    let constraints: Vec<_> = vc.rules[0].body.constraints.iter().collect();
    assert_eq!(constraints.len(), 2, "only the dead local temp should be pruned");
    assert!(
        constraints.iter().any(|c| expr_is_var_eq_bv(c, "x", 7, 64)),
        "body relation arg binding must be preserved",
    );
    assert!(
        constraints.iter().any(|c| expr_is_var_eq_bv(c, "x__out", 9, 64)),
        "head relation arg binding must be preserved",
    );
    assert!(
        constraints.iter().all(|c| !expr_mentions_name(c, "tmp")),
        "dead rule-local temp should be pruned",
    );
}

#[test]
fn test_scalarize_preserves_local_assignment_when_lhs_appears_in_value() {
    let tmp = Expr::var("tmp", bv64_sort());

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("tmp", bv64_sort()));
    vc.add_relation(RelationDecl::new("bb0", Vec::new()));
    vc.add_relation(RelationDecl::new("bb1", Vec::new()));

    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", Vec::new())),
            vec![tmp.clone().eq(tmp.clone().bvadd(bv64_const(1)))],
        ),
        RelationApp::new("bb1", Vec::new()),
    ));

    scalarize_vc(&mut vc);

    let constraints: Vec<_> = vc.rules[0].body.constraints.iter().collect();
    assert_eq!(constraints.len(), 1, "self-referential local assignment is a real constraint");
    assert!(
        expr_mentions_name(constraints[0], "tmp"),
        "value-side self reference must prevent pruning",
    );
}

#[test]
fn test_scalarize_simplifies_inline_store_select_miss_to_base_lane() {
    let mem_in = Expr::var("mem_u64", arr_u64_sort());
    let mem_out = Expr::var("mem_u64__out", arr_u64_sort());
    let read_out = Expr::var("read__out", bv64_sort());
    let stored_addr = bv64_const(0x30);
    let read_addr = bv64_const(0x38);

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("mem_u64", arr_u64_sort()));
    vc.add_var(VarDecl::new("mem_u64__out", arr_u64_sort()));
    vc.add_var(VarDecl::new("read__out", bv64_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_u64_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_u64_sort(), bv64_sort()]));

    let store_chain = mem_in.clone().store(stored_addr.clone(), bv64_const(99));
    let inline_store_read = store_chain.clone().select(read_addr);
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![mem_in.clone()])),
            vec![mem_out.clone().eq(store_chain), read_out.clone().eq(inline_store_read)],
        ),
        RelationApp::new("bb1", vec![mem_out, read_out]),
    ));

    scalarize_vc(&mut vc);

    let rule = &vc.rules[0];
    let body_rel = rule.body.relation.as_ref().expect("transition has body relation");
    assert_eq!(body_rel.args.len(), 2, "stored and read lanes should scalarize");
    assert_eq!(rule.head.args.len(), 3, "head keeps two mem lanes plus read scalar");
    assert!(
        rule.body.constraints.iter().all(|c| !constraint_has_array_sort(c)),
        "constant-index store/select miss should rewrite to a scalar base-lane read",
    );
    assert!(
        rule.body.constraints.iter().any(|c| expr_is_var_eq_var(
            c,
            "read__out",
            "mem_u64_at_0x38_bv64"
        )),
        "read should use the scalarized base lane after bypassing the unrelated store",
    );
}

// Helpers for realistic heap encoding patterns.
fn bool_sort() -> Sort {
    Sort::bool()
}
fn obj_valid_sort() -> Sort {
    Sort::array(bv32_sort(), bool_sort())
}

/// Construct a BvConcat expression: concat(bv32(obj_id), bv32(offset)).
/// This is how `get_or_create_local_address` builds heap addresses.
fn heap_addr(obj_id: u32, offset: u32) -> Expr {
    let hi = Expr::bitvec_const(obj_id as i128, 32);
    let lo = Expr::bitvec_const(offset as i128, 32);
    hi.concat(lo)
}

/// Test realistic heap VC: region array with concat-constant indices should
/// scalarize, even when obj_valid in the same VC has symbolic indices.
#[test]
fn test_scalarize_region_with_concat_indices() {
    let region_in = Expr::var("region_2_i32", arr_sort());
    let region_out = Expr::var("region_2_i32__out", arr_sort());
    let x = Expr::var("x", bv32_sort());
    let x_out = Expr::var("x__out", bv32_sort());

    // Store using concat(bv32(2), bv32(0)) — heap address for obj_id=2
    let addr = heap_addr(2, 0);
    let store_constraint = region_out.clone().eq(region_in.clone().store(addr.clone(), x.clone()));
    // Add a select so the array isn't purely write-only (which const_fold eliminates).
    let select_constraint = x_out.clone().eq(region_in.clone().select(addr));

    let mut vc = build_test_vc(
        "region_2_i32",
        vec![store_constraint, select_constraint],
        vec![region_in.clone(), x.clone()],
        vec![region_out.clone(), x_out.clone()],
    );
    scalarize_vc(&mut vc);

    // Region array should be scalarized: concat(2, 0) is constant
    let rule = &vc.rules[0];
    assert_eq!(rule.head.args.len(), 2, "head should have scalar + x");
    assert_eq!(*rule.head.args[0].sort(), bv32_sort(), "region replaced by scalar");
}

/// Test that BvExtract of a constant concat is handled as constant.
/// Pattern: select(obj_valid, extract[63:32](concat(bv32(2), bv32(0))))
#[test]
fn test_scalarize_extract_of_concat_is_constant() {
    let idx = heap_addr(2, 0);
    let extracted = try_extract_const_idx(&idx);
    assert!(extracted.is_some(), "concat(const, const) should be constant");
    let ci = extracted.expect("concat(const, const) should extract a constant index");
    assert_eq!(ci.width, 64); // concat of two bv32 = bv64
    assert_eq!(ci.value, BigInt::from(2u64) << 32); // (2 << 32) | 0
}

/// Test: two arrays in same VC — one scalarizable, one not.
/// Simulates real heap VC where region arrays are constant-index
/// but obj_valid has symbolic index from dealloc.
#[test]
fn test_scalarize_mixed_arrays_only_region_scalarized() {
    let region_in = Expr::var("region_3_u32", arr_sort());
    let region_out = Expr::var("region_3_u32__out", arr_sort());
    let ov_in = Expr::var("obj_valid", obj_valid_sort());
    let ov_out = Expr::var("obj_valid__out", obj_valid_sort());
    let x = Expr::var("x", bv32_sort());
    let x_out = Expr::var("x__out", bv32_sort());
    let ov_read = Expr::var("ov_read", bool_sort());

    // Region store: constant concat index
    let region_addr = heap_addr(3, 0);
    let region_store =
        region_out.clone().eq(region_in.clone().store(region_addr.clone(), x.clone()));
    // Region select: constant index (prevents write-only elimination)
    let region_select = x_out.clone().eq(region_in.clone().select(region_addr));
    // obj_valid store: symbolic index (from dealloc)
    let symbolic_ptr = Expr::var("dealloc_ptr", bv32_sort());
    let ov_store =
        ov_out.clone().eq(ov_in.clone().store(symbolic_ptr.clone(), Expr::bool_const(false)));
    // obj_valid select: symbolic index (prevents write-only elimination)
    let ov_select = ov_read.clone().eq(ov_in.clone().select(symbolic_ptr));

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("region_3_u32", arr_sort()));
    vc.add_var(VarDecl::new("region_3_u32__out", arr_sort()));
    vc.add_var(VarDecl::new("obj_valid", obj_valid_sort()));
    vc.add_var(VarDecl::new("obj_valid__out", obj_valid_sort()));
    vc.add_var(VarDecl::new("x", bv32_sort()));
    vc.add_var(VarDecl::new("x__out", bv32_sort()));
    vc.add_var(VarDecl::new("dealloc_ptr", bv32_sort()));
    vc.add_var(VarDecl::new("ov_read", bool_sort()));

    let body_args = vec![region_in.clone(), ov_in.clone(), x.clone()];
    let head_args = vec![region_out.clone(), ov_out.clone(), x_out.clone()];
    let body_sorts: Vec<Sort> = body_args.iter().map(|a| a.sort().clone()).collect();
    let head_sorts: Vec<Sort> = head_args.iter().map(|a| a.sort().clone()).collect();
    vc.add_relation(RelationDecl::new("bb0", body_sorts));
    vc.add_relation(RelationDecl::new("bb1", head_sorts));

    let body = RuleBody::new(
        Some(RelationApp::new("bb0", body_args)),
        vec![region_store, region_select, ov_store, ov_select],
    );
    let head = RelationApp::new("bb1", head_args);
    vc.add_rule(Rule::new(body, head));

    scalarize_vc(&mut vc);

    // obj_valid should NOT be scalarized (symbolic index)
    let has_obj_valid_array =
        vc.vars().iter().any(|v| v.name.as_ref() == "obj_valid" && v.sort.is_array());
    assert!(has_obj_valid_array, "obj_valid should remain as array (symbolic index)");

    // region_3_u32 should be scalarized
    let _has_region_array =
        vc.vars().iter().any(|v| v.name.as_ref() == "region_3_u32" && v.sort.is_array());
    // The original array var decl remains, but scalar vars are added
    let has_scalar = vc
        .vars()
        .iter()
        .any(|v| v.name.as_ref().starts_with("region_3_u32_at_") && !v.sort.is_array());
    assert!(has_scalar, "region_3_u32 should have scalar replacements");

    // Check that relation args now have the scalar instead of array for region
    let rule = &vc.rules[0];
    let head_arr_count = rule.head.args.iter().filter(|a| a.sort().is_array()).count();
    assert_eq!(head_arr_count, 1, "only obj_valid should remain as array in head");
}

#[test]
fn test_carry_rhs_scalarized_lane_survives_local_and_final_prune() {
    let lane = Expr::var("src_at_0x0_bv64", bv64_sort());
    let lane_out = Expr::var("src_at_0x0_bv64__out", bv64_sort());
    let dst_out = Expr::var("dst_at_0x0_bv64__out", bv64_sort());

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("src_at_0x0_bv64", bv64_sort()));
    vc.add_var(VarDecl::new("src_at_0x0_bv64__out", bv64_sort()));
    vc.add_var(VarDecl::new("dst_at_0x0_bv64", bv64_sort()));
    vc.add_var(VarDecl::new("dst_at_0x0_bv64__out", bv64_sort()));
    vc.add_relation(RelationDecl::new("bb0", Vec::new()));
    vc.add_relation(RelationDecl::new("bb1", Vec::new()));
    vc.add_relation(RelationDecl::new("bb2", vec![bv64_sort()]));

    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![lane_out.clone().eq(bv64_const(1))]),
        RelationApp::new("bb0", Vec::new()),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", Vec::new())), Vec::new()),
        RelationApp::new("bb1", Vec::new()),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", Vec::new())),
            vec![dst_out.clone().eq(lane.clone())],
        ),
        RelationApp::new("bb2", vec![dst_out]),
    ));

    assert_eq!(super::protect_lanes::carry_rhs_scalarized_lanes(&mut vc), 4);
    super::prune_dead_scalars::prune_dead_scalars(&mut vc);
    vc.prune_dead_vars_and_constraints();

    let bb0 = vc.relations.iter().find(|rel| rel.name == "bb0").expect("bb0 relation");
    assert_eq!(bb0.arg_sorts, vec![bv64_sort()]);
    let bb1 = vc.relations.iter().find(|rel| rel.name == "bb1").expect("bb1 relation");
    assert_eq!(bb1.arg_sorts, vec![bv64_sort()]);

    assert_eq!(vc.rules[0].head.args.len(), 1);
    assert!(expr_is_var(&vc.rules[0].head.args[0], "src_at_0x0_bv64__out"));
    assert_eq!(vc.rules[1].body.relation.as_ref().expect("body relation").args.len(), 1);
    assert!(expr_is_var(
        &vc.rules[1].body.relation.as_ref().expect("body relation").args[0],
        "src_at_0x0_bv64"
    ));
    assert_eq!(vc.rules[1].head.args.len(), 1);
    assert!(expr_is_var(&vc.rules[1].head.args[0], "src_at_0x0_bv64"));
    assert_eq!(vc.rules[2].body.relation.as_ref().expect("body relation").args.len(), 1);
    assert!(expr_is_var(
        &vc.rules[2].body.relation.as_ref().expect("body relation").args[0],
        "src_at_0x0_bv64"
    ));

    assert!(
        vc.rules[0]
            .body
            .constraints
            .iter()
            .any(|constraint| { expr_is_var_eq_bv(constraint, "src_at_0x0_bv64__out", 1, 64) }),
        "the predecessor lane definition must survive final dead-variable pruning",
    );
    assert!(
        vc.rules[2].body.constraints.iter().any(|constraint| {
            expr_is_var_eq_var(constraint, "dst_at_0x0_bv64__out", "src_at_0x0_bv64")
        }),
        "the consuming lane copy must remain tied to the carried lane",
    );
}
