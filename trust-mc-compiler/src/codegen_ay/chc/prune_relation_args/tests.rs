// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::prune_dead_array_relation_args;
use ay_bindings::{Expr, ExprValue, Sort};
use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};

#[test]
fn prunes_closed_dead_array_relation_arg_after_scalarization() {
    let arr_sort = Sort::array(Sort::bv32(), Sort::bool());
    let state = Expr::var("_test_box_alloc_symbolic_1", Sort::bv64());
    let obj_size = Expr::var("obj_size_at_0x3b_bv32", Sort::bv32());
    let closed_valid = Expr::const_array(Sort::bv32(), Expr::bool_const(true))
        .store(Expr::bitvec_const(0x3bu128, 32), Expr::bool_const(false));
    let pad_name = "__pad_test_box_alloc_symbolic__bb23_1";
    let pad = Expr::var(pad_name, arr_sort.clone());

    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new(
        "test_box_alloc_symbolic__bb23",
        vec![Sort::bv64(), arr_sort.clone(), Sort::bv32()],
    ));
    vc.add_relation(RelationDecl::new(
        "test_box_alloc_symbolic__bb12",
        vec![Sort::bv64(), Sort::bv32()],
    ));
    vc.add_var(VarDecl::new(pad_name, arr_sort.clone()));
    vc.add_rule(Rule::new(
        RuleBody::empty(),
        RelationApp::new(
            "test_box_alloc_symbolic__bb23",
            vec![state.clone(), closed_valid, obj_size.clone()],
        ),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new(
                "test_box_alloc_symbolic__bb23",
                vec![state.clone(), pad, obj_size.clone()],
            )),
            vec![obj_size.clone().eq(Expr::bitvec_const(4u128, 32))],
        ),
        RelationApp::new("test_box_alloc_symbolic__bb12", vec![state, obj_size]),
    ));

    let pruned = prune_dead_array_relation_args(&mut vc);

    assert_eq!(pruned, 1);
    let bb23 = vc
        .relations
        .iter()
        .find(|rel| rel.name == "test_box_alloc_symbolic__bb23")
        .expect("bb23 relation");
    assert_eq!(bb23.arg_sorts, vec![Sort::bv64(), Sort::bv32()]);
    assert_eq!(vc.rules[0].head.args.len(), 2);
    let body_rel = vc.rules[1].body.relation.as_ref().expect("body relation");
    assert_eq!(body_rel.args.len(), 2);
    assert!(body_rel.args.iter().all(|arg| !arg.sort().is_array()));
    assert!(!vc.vars().iter().any(|var| var.name.as_ref() == pad_name));
}

#[test]
fn prunes_compound_array_producer_when_relation_slot_is_pad_only() {
    let arr_sort = Sort::array(Sort::bv32(), Sort::bool());
    let state = Expr::var("state", Sort::bv64());
    let obj_valid = Expr::var("obj_valid", arr_sort.clone());
    let obj_id = Expr::var("obj_id", Sort::bv32());
    let updated_valid = obj_valid.store(obj_id.clone(), Expr::bool_const(false));
    let pad_name = "__pad_bb_drop_1";
    let pad = Expr::var(pad_name, arr_sort.clone());

    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("bb_drop", vec![Sort::bv64(), arr_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb_next", vec![Sort::bv64(), Sort::bv32()]));
    vc.add_var(VarDecl::new(pad_name, arr_sort));
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![obj_id.clone().eq(Expr::bitvec_const(0x3bu128, 32))]),
        RelationApp::new("bb_drop", vec![state.clone(), updated_valid]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb_drop", vec![state.clone(), pad])), vec![]),
        RelationApp::new("bb_next", vec![state, obj_id]),
    ));

    let pruned = prune_dead_array_relation_args(&mut vc);

    assert_eq!(pruned, 1);
    let bb_drop = vc.relations.iter().find(|rel| rel.name == "bb_drop").expect("bb_drop relation");
    assert_eq!(bb_drop.arg_sorts, vec![Sort::bv64()]);
    assert_eq!(vc.rules[0].head.args.len(), 1);
    assert_eq!(vc.rules[1].body.relation.as_ref().expect("body relation").args.len(), 1);
}

#[test]
fn prunes_closed_scalar_relation_arg_when_later_slot_is_pad_only() {
    let state = Expr::var("state", Sort::bv32());
    let obj_size = Expr::var("obj_size_at_0x3b_bv32", Sort::bv32());
    let closed_ptr = Expr::bitvec_const(0x0000_003b_0000_0000u128, 64);
    let pad_name = "__pad_test_box_alloc_symbolic__bb23_1";
    let pad = Expr::var(pad_name, Sort::bv64());

    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new(
        "test_box_alloc_symbolic__bb23",
        vec![Sort::bv32(), Sort::bv64(), Sort::bv32()],
    ));
    vc.add_relation(RelationDecl::new(
        "test_box_alloc_symbolic__bb12",
        vec![Sort::bv32(), Sort::bv32()],
    ));
    vc.add_var(VarDecl::new(pad_name, Sort::bv64()));
    vc.add_rule(Rule::new(
        RuleBody::empty(),
        RelationApp::new(
            "test_box_alloc_symbolic__bb23",
            vec![state.clone(), closed_ptr, obj_size.clone()],
        ),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new(
                "test_box_alloc_symbolic__bb23",
                vec![state.clone(), pad, obj_size.clone()],
            )),
            vec![],
        ),
        RelationApp::new("test_box_alloc_symbolic__bb12", vec![state, obj_size]),
    ));

    let pruned = prune_dead_array_relation_args(&mut vc);

    assert_eq!(pruned, 1);
    let bb23 = vc
        .relations
        .iter()
        .find(|rel| rel.name == "test_box_alloc_symbolic__bb23")
        .expect("bb23 relation");
    assert_eq!(bb23.arg_sorts, vec![Sort::bv32(), Sort::bv32()]);
    assert_eq!(vc.rules[0].head.args.len(), 2);
    assert_eq!(vc.rules[1].body.relation.as_ref().expect("body relation").args.len(), 2);
    assert!(!vc.vars().iter().any(|var| var.name.as_ref() == pad_name));
}

#[test]
fn keeps_scalar_relation_arg_when_non_pad_var_flows() {
    let state = Expr::var("state", Sort::bv32());
    let obj_size = Expr::var("obj_size_at_0x3b_bv32", Sort::bv32());
    let closed_ptr = Expr::bitvec_const(0x0000_003b_0000_0000u128, 64);
    let live_ptr = Expr::var("live_ptr", Sort::bv64());

    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new(
        "test_box_alloc_symbolic__bb23",
        vec![Sort::bv32(), Sort::bv64(), Sort::bv32()],
    ));
    vc.add_relation(RelationDecl::new(
        "test_box_alloc_symbolic__bb12",
        vec![Sort::bv32(), Sort::bv64(), Sort::bv32()],
    ));
    vc.add_rule(Rule::new(
        RuleBody::empty(),
        RelationApp::new(
            "test_box_alloc_symbolic__bb23",
            vec![state.clone(), closed_ptr, obj_size.clone()],
        ),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new(
                "test_box_alloc_symbolic__bb23",
                vec![state.clone(), live_ptr.clone(), obj_size.clone()],
            )),
            vec![],
        ),
        RelationApp::new("test_box_alloc_symbolic__bb12", vec![state, live_ptr, obj_size]),
    ));

    let pruned = prune_dead_array_relation_args(&mut vc);

    assert_eq!(pruned, 0);
    let bb23 = vc
        .relations
        .iter()
        .find(|rel| rel.name == "test_box_alloc_symbolic__bb23")
        .expect("bb23 relation");
    assert_eq!(
        bb23.arg_sorts,
        vec![Sort::bv32(), Sort::bv64(), Sort::bv32()],
        "bare non-pad scalar variables must keep the relation slot live"
    );
    assert_eq!(vc.rules[0].head.args.len(), 3);
    assert_eq!(vc.rules[1].body.relation.as_ref().expect("body relation").args.len(), 3);
}

#[test]
fn keeps_array_relation_arg_when_non_pad_var_flows() {
    let arr_sort = Sort::array(Sort::bv32(), Sort::bool());
    let state = Expr::var("state", Sort::bv64());
    let obj_valid = Expr::var("obj_valid", arr_sort.clone());
    let idx = Expr::bitvec_const(7u128, 32);

    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bv64(), arr_sort.clone()]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::new(
        RuleBody::empty(),
        RelationApp::new("bb1", vec![state.clone(), obj_valid.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![state, obj_valid.clone()])),
            vec![obj_valid.select(idx).not()],
        ),
        RelationApp::nullary("error"),
    ));

    let pruned = prune_dead_array_relation_args(&mut vc);

    assert_eq!(pruned, 0);
    let bb1 = vc.relations.iter().find(|rel| rel.name == "bb1").expect("bb1 relation");
    assert_eq!(bb1.arg_sorts, vec![Sort::bv64(), arr_sort]);
}

#[test]
fn prunes_array_relation_arg_when_only_threaded_by_copy() {
    let arr_sort = Sort::array(Sort::bv64(), Sort::bv8());
    let state = Expr::var("state", Sort::bv32());
    let data = Expr::var("iter_data", arr_sort.clone());
    let data_out = Expr::var("iter_data__out", arr_sort.clone());

    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bv32(), arr_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bv32(), arr_sort]));
    vc.add_rule(Rule::new(
        RuleBody::empty(),
        RelationApp::new("bb0", vec![state.clone(), data.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![state.clone(), data.clone()])),
            vec![data_out.clone().eq(data)],
        ),
        RelationApp::new("bb1", vec![state, data_out]),
    ));

    let pruned = prune_dead_array_relation_args(&mut vc);

    assert_eq!(pruned, 2);
    for rel in &vc.relations {
        assert_eq!(rel.arg_sorts, vec![Sort::bv32()]);
    }
    assert_eq!(vc.rules[0].head.args.len(), 1);
    assert_eq!(vc.rules[1].body.relation.as_ref().expect("body relation").args.len(), 1);
    assert_eq!(vc.rules[1].head.args.len(), 1);
}

#[test]
fn keeps_copied_array_relation_arg_when_later_selected() {
    let arr_sort = Sort::array(Sort::bv64(), Sort::bv8());
    let state = Expr::var("state", Sort::bv32());
    let data = Expr::var("iter_data", arr_sort.clone());
    let data_out = Expr::var("iter_data__out", arr_sort.clone());
    let idx = Expr::bitvec_const(0u128, 64);

    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bv32(), arr_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bv32(), arr_sort.clone()]));
    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_rule(Rule::new(
        RuleBody::empty(),
        RelationApp::new("bb0", vec![state.clone(), data.clone()]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![state.clone(), data.clone()])),
            vec![data_out.clone().eq(data.clone())],
        ),
        RelationApp::new("bb1", vec![state.clone(), data_out]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![state, data.clone()])),
            vec![data.select(idx).eq(Expr::bitvec_const(1u128, 8))],
        ),
        RelationApp::nullary("error"),
    ));

    let pruned = prune_dead_array_relation_args(&mut vc);

    assert_eq!(pruned, 0);
    for rel in vc.relations.iter().filter(|rel| rel.name != "error") {
        assert_eq!(rel.arg_sorts, vec![Sort::bv32(), arr_sort.clone()]);
    }
}

#[test]
fn prunes_embedded_closed_dead_array_relation_apps() {
    let arr_sort = Sort::array(Sort::bv32(), Sort::bool());
    let state = Expr::var("state", Sort::bv64());
    let closed_valid = Expr::const_array(Sort::bv32(), Expr::bool_const(true));
    let pad_name = "__pad_bb_embedded_1";
    let pad = Expr::var(pad_name, arr_sort.clone());

    let mut vc = ChcVc::new();
    vc.add_relation(RelationDecl::new("bb_embedded", vec![Sort::bv64(), arr_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb_next", vec![Sort::bv64()]));
    vc.add_var(VarDecl::new(pad_name, arr_sort));
    vc.add_rule(Rule::new(
        RuleBody::empty(),
        RelationApp::new("bb_embedded", vec![state.clone(), closed_valid]),
    ));
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![Expr::func_app("bb_embedded", vec![state.clone(), pad])]),
        RelationApp::new("bb_next", vec![state]),
    ));

    let pruned = prune_dead_array_relation_args(&mut vc);

    assert_eq!(pruned, 1);
    let constraint = vc.rules[1].body.constraints.iter().next().expect("constraint");
    match constraint.value() {
        ExprValue::FuncApp { name, args } => {
            assert_eq!(name, "bb_embedded");
            assert_eq!(args.len(), 1);
            assert_eq!(*args[0].sort(), Sort::bv64());
        }
        other => panic!("expected embedded relation app, got {other:?}"),
    }
}
