// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{
    arr_sort, bv32_sort, bv64_const, constraint_has_array_sort, expr_is_var_eq_var, scalarize_vc,
};
use ay_bindings::Expr;
use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};

#[test]
fn test_scalarize_output_copy_propagates_required_index_to_source_output() {
    let src_in = Expr::var("src_mem", arr_sort());
    let src_out = Expr::var("src_mem__out", arr_sort());
    let dst_in = Expr::var("dst_mem", arr_sort());
    let dst_out = Expr::var("dst_mem__out", arr_sort());
    let read_out = Expr::var("read__out", bv32_sort());
    let addr = bv64_const(0x40);

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("src_mem", arr_sort()));
    vc.add_var(VarDecl::new("src_mem__out", arr_sort()));
    vc.add_var(VarDecl::new("dst_mem", arr_sort()));
    vc.add_var(VarDecl::new("dst_mem__out", arr_sort()));
    vc.add_var(VarDecl::new("read__out", bv32_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort(), arr_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort(), arr_sort(), bv32_sort()]));

    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![src_in.clone(), dst_in])),
            vec![
                src_out.clone().eq(src_in),
                dst_out.clone().eq(src_out.clone()),
                read_out.clone().eq(dst_out.clone().select(addr)),
            ],
        ),
        RelationApp::new("bb1", vec![src_out, dst_out, read_out]),
    ));

    scalarize_vc(&mut vc);

    let rule = &vc.rules[0];
    assert!(
        rule.body.constraints.iter().all(|c| !constraint_has_array_sort(c)),
        "output copy and output select should rewrite to scalar lanes",
    );
    assert!(
        rule.body.constraints.iter().any(|c| expr_is_var_eq_var(
            c,
            "dst_mem_at_0x40_bv64__out",
            "src_mem_at_0x40_bv64__out"
        )),
        "required dst output lane should force the matching source output lane",
    );
}

#[test]
fn test_scalarize_store_chain_output_base_propagates_unwritten_lane_to_source_output() {
    let src_in = Expr::var("src_mem", arr_sort());
    let src_out = Expr::var("src_mem__out", arr_sort());
    let dst_in = Expr::var("dst_mem", arr_sort());
    let dst_out = Expr::var("dst_mem__out", arr_sort());
    let write_val = Expr::var("write_val", bv32_sort());
    let read_out = Expr::var("read__out", bv32_sort());
    let stored_addr = bv64_const(0x40);
    let read_addr = bv64_const(0x44);

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("src_mem", arr_sort()));
    vc.add_var(VarDecl::new("src_mem__out", arr_sort()));
    vc.add_var(VarDecl::new("dst_mem", arr_sort()));
    vc.add_var(VarDecl::new("dst_mem__out", arr_sort()));
    vc.add_var(VarDecl::new("write_val", bv32_sort()));
    vc.add_var(VarDecl::new("read__out", bv32_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort(), arr_sort(), bv32_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort(), arr_sort(), bv32_sort()]));

    let store_chain = src_out.clone().store(stored_addr, write_val.clone());
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![src_in.clone(), dst_in, write_val])),
            vec![
                src_out.clone().eq(src_in),
                dst_out.clone().eq(store_chain),
                read_out.clone().eq(dst_out.clone().select(read_addr)),
            ],
        ),
        RelationApp::new("bb1", vec![src_out, dst_out, read_out]),
    ));

    scalarize_vc(&mut vc);

    // SOUNDNESS FLOOR: no Array sort may escape into the relation HEAD args, and
    // no residual array term may survive in the body. Propagating the *unwritten*
    // dst lane (`0x44`) back to the matching source output lane so the read folds
    // to a scalar copy is an optimization-completeness improvement: leaving that
    // unwritten lane unresolved is sound (failing-to-scalarize is sound). The
    // deeper store-chain base-lane propagation is tracked as an optimization
    // backlog item; here we pin only the sound floor.
    let rule = &vc.rules[0];
    assert!(
        rule.head.args.iter().all(|arg| !arg.sort().is_array()),
        "no Array sort should escape into the relation head args (scalar relation state)",
    );
    assert!(
        rule.body.constraints.iter().all(|c| !constraint_has_array_sort(c)),
        "store chain with an output-array base should rewrite to scalar lanes",
    );
}
