// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{arr_sort, bv32_sort, bv64_sort};
use ay_bindings::Expr;
use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};

#[test]
fn test_const_fold_skips_const_array_when_whole_value_escapes_live_output_copy() {
    let source = Expr::var("source", arr_sort());
    let source_out = Expr::var("source__out", arr_sort());
    let sink_out = Expr::var("sink__out", arr_sort());

    let mut vc = ChcVc::new();
    vc.add_var(VarDecl::new("source", arr_sort()));
    vc.add_var(VarDecl::new("source__out", arr_sort()));
    vc.add_var(VarDecl::new("sink__out", arr_sort()));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort()]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort(), arr_sort()]));

    vc.add_rule(Rule::new(
        RuleBody::new(
            None,
            vec![source.clone().eq(Expr::const_array(bv64_sort(), Expr::bitvec_const(7, 32)))],
        ),
        RelationApp::new("bb0", vec![source.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![source.clone()])),
            vec![source_out.clone().eq(source.clone()), sink_out.clone().eq(source.clone())],
        ),
        RelationApp::new("bb1", vec![source_out, sink_out]),
    ));

    let fold_infos =
        crate::codegen_ay::chc::scalarize_arrays::const_fold::identify_const_foldable_arrays(&vc);
    assert!(
        fold_infos.iter().all(|info| info.input_name != "source"),
        "source escapes as the whole value of a live output array copy",
    );
}

/// A symbolic-index `select` against a `const_array(K, 7)` folds to the uniform
/// default 7 (#4097): every element of a const-array is the same value, so the
/// fold is sound for ANY index, constant or symbolic. This test was originally
/// written to pin the PRE-#4097 conservative behavior (keep such arrays out of
/// folding); it now asserts the strictly-more-precise (and sound) outcome that
/// `arr` IS const-foldable with `uniform_default == 7`.
#[test]
fn test_const_fold_folds_symbolic_select_against_uniform_default() {
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
            Some(RelationApp::new("bb0", vec![arr.clone(), idx.clone()])),
            vec![arr_out.clone().eq(arr.clone()), read_out.clone().eq(arr.select(idx))],
        ),
        RelationApp::new("bb1", vec![arr_out, read_out]),
    ));

    let fold_infos =
        crate::codegen_ay::chc::scalarize_arrays::const_fold::identify_const_foldable_arrays(&vc);
    let arr_info = fold_infos
        .iter()
        .find(|info| info.input_name == "arr")
        .expect("const_array(K, 7) array should be const-foldable via its uniform default");
    assert_eq!(
        arr_info.uniform_default,
        Some(Expr::bitvec_const(7, 32)),
        "symbolic-index select against const_array(K, 7) should fold to uniform default 7",
    );
}
