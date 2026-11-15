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

/// entry: `arr = const_array(7)`; bb0 -> bb1 HAVOCS the array (the head carries
/// `arr__out` and no constraint of that rule defines it); bb1 then reads
/// `arr[0]`. The read may see any value, so folding it to the entry constant 7
/// would undo the havoc before the solver sees it. The same VC with the INPUT
/// variable in bb1's head (an unchanged frame) stays foldable.
#[test]
fn test_const_fold_refuses_array_havocked_by_unbound_head_output() {
    fn vc_with_bb1_head(havoc: bool) -> ChcVc {
        let arr = Expr::var("arr", arr_sort());
        let arr_out = Expr::var("arr__out", arr_sort());
        let read_out = Expr::var("read__out", bv32_sort());
        let mut vc = ChcVc::new();
        vc.add_var(VarDecl::new("arr", arr_sort()));
        vc.add_var(VarDecl::new("arr__out", arr_sort()));
        vc.add_var(VarDecl::new("read__out", bv32_sort()));
        vc.add_relation(RelationDecl::new("bb0", vec![arr_sort()]));
        vc.add_relation(RelationDecl::new("bb1", vec![arr_sort()]));
        vc.add_relation(RelationDecl::new("bb2", vec![bv32_sort()]));
        vc.add_rule(Rule::new(
            RuleBody::new(
                None,
                vec![arr.clone().eq(Expr::const_array(bv64_sort(), Expr::bitvec_const(7, 32)))],
            ),
            RelationApp::new("bb0", vec![arr.clone()]),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::new("bb0", vec![arr.clone()])), vec![]),
            RelationApp::new("bb1", vec![if havoc { arr_out } else { arr.clone() }]),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("bb1", vec![arr.clone()])),
                vec![read_out.clone().eq(arr.select(Expr::bitvec_const(0, 64)))],
            ),
            RelationApp::new("bb2", vec![read_out]),
        ));
        vc
    }
    let identify =
        crate::codegen_ay::chc::scalarize_arrays::const_fold::identify_const_foldable_arrays;

    let havocked = identify(&vc_with_bb1_head(true));
    assert!(
        havocked.iter().all(|info| info.input_name != "arr"),
        "an array a transition rule havocs is not read-only; folding arr[0] to 7 undoes the havoc",
    );

    let unchanged = identify(&vc_with_bb1_head(false));
    assert!(
        unchanged.iter().any(|info| info.input_name == "arr"),
        "with the input variable in bb1's head the array is read-only and still folds",
    );
}

/// Criterion 3 matches a havoc by the NAME `arr__out`. A head can also set the
/// slot the readers call `arr` to a value the entry rule does not describe
/// under another spelling: a large-step `arr__mid_bb1` no constraint binds (a
/// composed chain's last block carries the middle block's name for a var it
/// did not touch), or the array expression emit-time constant propagation
/// substituted for `arr__out`. Folding bb1's `arr[0]` to the entry constant 7
/// would read neither. The slot is judged by position; an identity alias
/// `(= arr__mid_bb1 arr)` is still an unchanged frame.
#[test]
fn test_const_fold_refuses_array_slot_set_under_another_spelling() {
    enum Bb1Head {
        UnboundMid,
        SubstitutedStore,
        MidEqualsInput,
    }
    fn vc_with(head: Bb1Head) -> ChcVc {
        let arr = Expr::var("arr", arr_sort());
        let arr_mid = Expr::var("arr__mid_bb1", arr_sort());
        let read_out = Expr::var("read__out", bv32_sort());
        let mut vc = ChcVc::new();
        vc.add_var(VarDecl::new("arr", arr_sort()));
        vc.add_var(VarDecl::new("arr__out", arr_sort()));
        vc.add_var(VarDecl::new("read__out", bv32_sort()));
        vc.add_relation(RelationDecl::new("bb0", vec![arr_sort()]));
        vc.add_relation(RelationDecl::new("bb1", vec![arr_sort()]));
        vc.add_relation(RelationDecl::new("bb2", vec![bv32_sort()]));
        vc.add_rule(Rule::new(
            RuleBody::new(
                None,
                vec![arr.clone().eq(Expr::const_array(bv64_sort(), Expr::bitvec_const(7, 32)))],
            ),
            RelationApp::new("bb0", vec![arr.clone()]),
        ));
        let (constraints, head_arg) = match head {
            Bb1Head::UnboundMid => (vec![], arr_mid),
            Bb1Head::SubstitutedStore => (
                vec![],
                Expr::const_array(bv64_sort(), Expr::bitvec_const(7, 32))
                    .store(Expr::bitvec_const(0, 64), Expr::bitvec_const(9, 32)),
            ),
            Bb1Head::MidEqualsInput => (vec![arr_mid.clone().eq(arr.clone())], arr_mid),
        };
        vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::new("bb0", vec![arr.clone()])), constraints),
            RelationApp::new("bb1", vec![head_arg]),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("bb1", vec![arr.clone()])),
                vec![read_out.clone().eq(arr.select(Expr::bitvec_const(0, 64)))],
            ),
            RelationApp::new("bb2", vec![read_out]),
        ));
        vc
    }
    let identify =
        crate::codegen_ay::chc::scalarize_arrays::const_fold::identify_const_foldable_arrays;
    let folds = |vc: ChcVc| identify(&vc).iter().any(|info| info.input_name == "arr");

    assert!(
        !folds(vc_with(Bb1Head::UnboundMid)),
        "an unbound arr__mid_bb1 in bb1's head havocs the slot bb1 reads as arr",
    );
    assert!(
        !folds(vc_with(Bb1Head::SubstitutedStore)),
        "a substituted store in bb1's head sets arr[0] to 9; folding it to 7 is wrong",
    );
    assert!(
        folds(vc_with(Bb1Head::MidEqualsInput)),
        "a mid alias equal to arr is an unchanged frame and still folds",
    );
}
