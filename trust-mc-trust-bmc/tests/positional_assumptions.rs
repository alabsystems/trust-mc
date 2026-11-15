// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An assumption filters the remaining execution, never an earlier charge.

use ay_bindings::{AYProgram, Expr, execute_direct};
use trust_ir::inst::AllocOrigin;
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;
use trust_mc_core::decl::Decl;
use trust_mc_core::violation::PropertyKind;
use trust_mc_trust_bmc::{TranslateOptions, trust_ir_to_bmc_vc};

// Solve the actual public BMC query: all generated constraints AND the
// disjunction of every generated violation. Incomplete solver outcomes fail.
fn has_query(module: &Module, refusal: bool) -> bool {
    let vcs = trust_ir_to_bmc_vc(module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1);
    let vc = &vcs[0];
    let mut query = AYProgram::new();
    query.set_logic("QF_BV");
    for declaration in &vc.decls {
        let Decl::Const { name, sort } = declaration else {
            panic!("fixture unexpectedly needs a nonconstant declaration");
        };
        let _ = query.declare_const(name.clone(), sort.clone());
    }
    for constraint in &vc.constraints {
        query.assert(constraint.clone());
    }
    let has_unsupported = vc.violations.iter().any(|v| v.kind == PropertyKind::Other);
    assert_eq!(has_unsupported, refusal, "unexpected unsupported-semantic population");
    let failures = vc
        .violations
        .iter()
        .filter(|v| !refusal || v.kind == PropertyKind::Other)
        .map(|v| v.condition.clone())
        .collect::<Vec<_>>();
    query.assert(if failures.is_empty() { Expr::false_() } else { Expr::or_many(failures) });
    query.check_sat();
    match execute_direct::execute(&query).expect("actual in-process AY query executes") {
        execute_direct::ExecuteResult::Counterexample { .. } => true,
        execute_direct::ExecuteResult::Verified => false,
        result => panic!("BMC query did not finish: {result:?}"),
    }
}

fn has_counterexample(module: &Module) -> bool {
    has_query(module, false)
}

fn has_refusal(module: &Module) -> bool {
    has_query(module, true)
}

fn straight(assumption_first: bool, symbolic: bool) -> Module {
    let mut builder = ModuleBuilder::new("assumption_position");
    let signature = builder.add_func_type(if symbolic { vec![Ty::Bool] } else { vec![] }, vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    let input = symbolic.then(|| function.add_block_param(entry, Ty::Bool));
    function.switch_to_block(entry);
    let condition = input.unwrap_or_else(|| function.bool_const(false));
    if assumption_first {
        function.assume(condition);
        function.assert(condition);
    } else {
        function.assert(condition);
        function.assume(condition);
    }
    function.ret(vec![]);
    function.build();
    builder.build().expect("valid typed fixture")
}

#[test]
fn later_false_assumption_does_not_erase_an_earlier_assertion() {
    assert!(has_counterexample(&straight(false, false)));
}

#[test]
fn later_symbolic_assumption_does_not_erase_an_earlier_assertion() {
    assert!(has_counterexample(&straight(false, true)));
}

#[test]
fn earlier_false_and_symbolic_assumptions_filter_later_assertions() {
    for symbolic in [false, true] {
        assert!(!has_counterexample(&straight(true, symbolic)));
    }
}

#[test]
fn assumptions_in_every_successor_do_not_erase_a_failing_prefix() {
    let mut builder = ModuleBuilder::new("failing_prefix");
    let signature = builder.add_func_type(vec![Ty::Bool], vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    let branch = function.add_block_param(entry, Ty::Bool);
    let left = function.create_block();
    let right = function.create_block();
    function.switch_to_block(entry);
    let no = function.bool_const(false);
    function.assert(no);
    function.condbr(branch, left, vec![], right, vec![]);
    for block in [left, right] {
        function.switch_to_block(block);
        function.assume(no);
        function.ret(vec![]);
    }
    function.build();
    assert!(has_counterexample(&builder.build().unwrap()));
}

#[test]
fn false_assumption_filters_the_outgoing_edge() {
    let mut builder = ModuleBuilder::new("filtered_edge");
    let signature = builder.add_func_type(vec![], vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    let next = function.create_block();
    function.switch_to_block(entry);
    let no = function.bool_const(false);
    function.assume(no);
    function.br(next, vec![]);
    function.switch_to_block(next);
    function.assert(no);
    function.ret(vec![]);
    function.build();
    assert!(!has_counterexample(&builder.build().unwrap()));
}

#[test]
fn a_filtered_arm_does_not_reach_a_join_or_hide_the_other_arm() {
    for live_value in [true, false] {
        let mut builder = ModuleBuilder::new("filtered_join");
        let signature = builder.add_func_type(vec![Ty::Bool], vec![]);
        let mut function = builder.function("subject", signature);
        let entry = function.create_block();
        let branch = function.add_block_param(entry, Ty::Bool);
        let left = function.create_block();
        let right = function.create_block();
        let join = function.create_block();
        let joined = function.add_block_param(join, Ty::Bool);
        function.switch_to_block(entry);
        let no = function.bool_const(false);
        let live = function.bool_const(live_value);
        function.condbr(branch, left, vec![], right, vec![]);
        function.switch_to_block(left);
        function.assume(no);
        function.br(join, vec![no]);
        function.switch_to_block(right);
        function.br(join, vec![live]);
        function.switch_to_block(join);
        function.assert(joined);
        function.ret(vec![]);
        function.build();
        assert_eq!(has_counterexample(&builder.build().unwrap()), !live_value);
    }
}

#[test]
fn later_false_assumption_does_not_hide_an_unsupported_operation() {
    let mut builder = ModuleBuilder::new("unsupported_prefix");
    let signature = builder.add_func_type(vec![], vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    function.heap_alloc(Ty::U8, None, None, AllocOrigin::RustHeap);
    let no = function.bool_const(false);
    function.assume(no);
    function.ret(vec![]);
    function.build();
    assert!(has_refusal(&builder.build().unwrap()));
}

#[test]
fn an_unreachable_blocks_assumption_cannot_filter_the_legacy_entry_block() {
    let mut builder = ModuleBuilder::new("legacy_block_order");
    let signature = builder.add_func_type(vec![], vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    let dead = function.create_block();
    function.switch_to_block(entry);
    function.br(entry, vec![]);
    function.switch_to_block(dead);
    let no = function.bool_const(false);
    function.assume(no);
    function.ret(vec![]);
    function.build();
    let mut module = builder.build().unwrap();
    // Block storage order is not execution order. The entry remains the loop.
    module.functions[0].blocks.reverse();
    assert!(has_refusal(&module), "the reachable loop remains unsupported");
}

#[test]
fn an_assumption_does_not_suppress_the_unsupported_control_flow_boundary() {
    let mut builder = ModuleBuilder::new("filtered_loop");
    let signature = builder.add_func_type(vec![], vec![]);
    let mut function = builder.function("subject", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let no = function.bool_const(false);
    function.assume(no);
    function.br(entry, vec![]);
    function.build();
    assert!(has_refusal(&builder.build().unwrap()));
}

#[test]
fn malformed_control_flow_is_refused_even_after_a_false_assumption() {
    use trust_ir::inst::Inst;
    use trust_ir::value::BlockId;
    for shape in 0..7 {
        let mut module = straight(true, false);
        let function = &mut module.functions[0];
        match shape {
            0 => function.blocks.clear(),
            1 => function.entry = BlockId::new(999),
            2 => function.blocks[0].body.clear(),
            3 => function.blocks.push(function.blocks[0].clone()),
            4 => {
                function.blocks[0].body.last_mut().unwrap().inst =
                    Inst::Br { target: BlockId::new(999), args: vec![] }
            }
            5 => {
                let terminator = function.blocks[0].body.last().unwrap().clone();
                function.blocks[0].body.insert(0, terminator);
            }
            6 => {
                function.blocks[0].body.pop();
            }
            _ => unreachable!(),
        }
        assert!(has_refusal(&module), "malformed control-flow shape {shape}");
    }
}
