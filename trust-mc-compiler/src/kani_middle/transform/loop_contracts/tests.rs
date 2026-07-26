// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Tests for loop contract transformation and SMT-LIB2 formula extraction.

use super::*;
use crate::rustc_public_bridge::IndexedVal;
use rustc_public::mir::{
    BasicBlock, BinOp, Operand, Place, Rvalue, Terminator, TerminatorKind, UnwindAction,
};
use rustc_public::ty::Span;
use std::collections::HashMap;

#[test]
fn test_binop_comparison_operators() {
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Ge), Some(">="));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Gt), Some(">"));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Le), Some("<="));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Lt), Some("<"));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Eq), Some("="));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Ne), Some("distinct"));
}

#[test]
fn test_binop_arithmetic_operators() {
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Add), Some("+"));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::AddUnchecked), Some("+"));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Sub), Some("-"));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::SubUnchecked), Some("-"));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Mul), Some("*"));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::MulUnchecked), Some("*"));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Div), Some("div"));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Rem), Some("mod"));
}

#[test]
fn test_binop_logical_operators() {
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::BitAnd), Some("and"));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::BitOr), Some("or"));
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::BitXor), Some("xor"));
}

#[test]
fn test_binop_unsupported_returns_none() {
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Shl), None);
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::Shr), None);
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::ShlUnchecked), None);
    assert_eq!(LoopContractPass::binop_to_smt2(BinOp::ShrUnchecked), None);
}

#[test]
fn test_find_return_value_formula_empty_statements() {
    let statements: Vec<rustc_public::mir::Statement> = Vec::new();
    let captured_vars: Vec<usize> = vec![5];
    let result = LoopContractPass::find_return_value_formula(&statements, &captured_vars);
    assert!(result.is_none());
}

// test_rvalue_to_smt2_binary_comparison deleted per #2391 / rule #2312:
// only constructed a HashMap and asserted on it, never called rvalue_to_smt2.

#[test]
#[allow(clippy::useless_conversion)]
fn test_rvalue_to_smt2_unary_not_from_local() {
    let mut local_exprs: HashMap<usize, String> = HashMap::new();
    local_exprs.insert(1, "captured_0".to_string());
    let operand = Operand::Copy(Place { local: 1usize.into(), projection: vec![] });
    let rvalue = Rvalue::UnaryOp(rustc_public::mir::UnOp::Not, operand);
    let result = LoopContractPass::rvalue_to_smt2(&rvalue, &local_exprs);
    assert_eq!(result, Some("(not captured_0)".to_string()));
}

#[test]
#[allow(clippy::useless_conversion)]
fn test_rvalue_to_smt2_binary_shift_returns_none() {
    let mut local_exprs: HashMap<usize, String> = HashMap::new();
    local_exprs.insert(1, "captured_0".to_string());
    local_exprs.insert(2, "captured_1".to_string());
    let lhs = Operand::Copy(Place { local: 1usize.into(), projection: vec![] });
    let rhs = Operand::Copy(Place { local: 2usize.into(), projection: vec![] });
    let rvalue = Rvalue::BinaryOp(BinOp::Shl, lhs, rhs);
    let result = LoopContractPass::rvalue_to_smt2(&rvalue, &local_exprs);
    assert!(result.is_none());
}

// Trivial tests deleted per #2391 / rule #2312:
// - test_smt2_formula_format: only asserted on hardcoded string literals
// - test_captured_var_naming: only tested format! macro output
// - test_extracted_loop_invariant_creation: struct construction readback
// - test_extracted_loop_invariant_without_formula: struct construction readback

#[test]
fn test_loop_invariant_registry_empty() {
    let result = get_loop_invariants("nonexistent_function");
    assert!(result.is_none(), "unregistered function should return None");
}

#[test]
fn test_loop_invariant_registry_register_and_get() {
    let test_fn = "test_registry_fn_12345";
    let invariants = vec![ExtractedLoopInvariant {
        loop_head_bb: 1,
        loop_latch_bb: Some(5),
        chc_loop_head_bb: None,
        captured_vars: vec![2],
        closure_def_index: Some(100),
        formula_smt2: Some("(>= captured_0 0)".to_string()),
        captured_rel_arg_positions: None,
    }];
    register_loop_invariants(test_fn.to_string(), invariants);
    let retrieved = get_loop_invariants(test_fn);
    assert!(retrieved.is_some());
    let retrieved_invariants = retrieved.expect("invariants should be present");
    assert_eq!(retrieved_invariants.len(), 1);
    assert_eq!(retrieved_invariants[0].loop_head_bb, 1);
    assert_eq!(retrieved_invariants[0].formula_smt2, Some("(>= captured_0 0)".to_string()));
}

#[test]
fn test_loop_invariant_registry_empty_list_not_registered() {
    let test_fn = "test_empty_invariants_fn";
    let empty: Vec<ExtractedLoopInvariant> = Vec::new();
    register_loop_invariants(test_fn.to_string(), empty);
    assert!(
        get_loop_invariants(test_fn).is_none(),
        "empty invariant list should not be stored in registry"
    );
}

fn mk_call_terminator(dest_local: usize, target: usize) -> Terminator {
    Terminator {
        kind: TerminatorKind::Call {
            func: Operand::Move(Place { local: 100, projection: vec![] }),
            args: vec![],
            destination: Place { local: dest_local, projection: vec![] },
            target: Some(target),
            unwind: UnwindAction::Terminate,
        },
        span: Span::to_val(0),
    }
}

fn mk_goto_terminator(target: usize) -> Terminator {
    Terminator { kind: TerminatorKind::Goto { target }, span: Span::to_val(0) }
}

#[test]
fn test_terminator_of_new_destination_updates_call_destination() {
    let updated = LoopContractPass::terminator_of_new_destination(mk_call_terminator(1, 7), 9);
    assert!(matches!(&updated.kind, TerminatorKind::Call { .. }), "expected Call terminator");
    if let TerminatorKind::Call { destination, target, .. } = updated.kind {
        assert_eq!(destination.local, 9);
        assert_eq!(target, Some(7));
    }
}

#[test]
fn test_terminator_of_new_destination_leaves_non_call_unchanged() {
    let updated = LoopContractPass::terminator_of_new_destination(mk_goto_terminator(3), 9);
    assert!(matches!(&updated.kind, TerminatorKind::Goto { .. }), "expected Goto terminator");
    if let TerminatorKind::Goto { target } = updated.kind {
        assert_eq!(target, 3);
    }
}

#[test]
fn test_block_of_new_target_updates_call_target_and_preserves_source() {
    let original = BasicBlock { statements: vec![], terminator: mk_call_terminator(4, 5) };
    let updated = LoopContractPass::block_of_new_target(&original, 11);

    assert!(
        matches!(&updated.terminator.kind, TerminatorKind::Call { .. }),
        "expected Call terminator"
    );
    if let TerminatorKind::Call { destination, target, .. } = &updated.terminator.kind {
        assert_eq!(destination.local, 4);
        assert_eq!(*target, Some(11));
    }

    assert!(
        matches!(&original.terminator.kind, TerminatorKind::Call { .. }),
        "expected original Call terminator"
    );
    if let TerminatorKind::Call { target, .. } = &original.terminator.kind {
        assert_eq!(*target, Some(5));
    }
}

#[test]
fn test_block_of_new_target_leaves_non_call_unchanged() {
    let original = BasicBlock { statements: vec![], terminator: mk_goto_terminator(2) };
    let updated = LoopContractPass::block_of_new_target(&original, 11);

    assert!(
        matches!(&updated.terminator.kind, TerminatorKind::Goto { .. }),
        "expected Goto terminator"
    );
    if let TerminatorKind::Goto { target } = updated.terminator.kind {
        assert_eq!(target, 2);
    }
}

// === get_associated_loop_head tests ===
// Tests the pure function that maps block indices to their containing loop head.

fn mk_pass() -> LoopContractPass {
    // LoopContractPass fields are not used by get_associated_loop_head;
    // construct with defaults sufficient for this helper.
    LoopContractPass::default()
}

#[test]
fn test_get_associated_loop_head_empty_positions() {
    let pass = mk_pass();
    let positions: Vec<(usize, usize)> = vec![];
    assert_eq!(pass.get_associated_loop_head(5, &positions), None);
}

#[test]
fn test_get_associated_loop_head_before_loop() {
    let pass = mk_pass();
    let positions = vec![(10, 20)];
    // block_idx 5 is before the loop (10..=20)
    assert_eq!(pass.get_associated_loop_head(5, &positions), None);
}

#[test]
fn test_get_associated_loop_head_at_loop_head() {
    let pass = mk_pass();
    let positions = vec![(10, 20)];
    // block_idx == loop_head_idx is NOT inside (condition is block_idx > loop_head_idx)
    assert_eq!(pass.get_associated_loop_head(10, &positions), None);
}

#[test]
fn test_get_associated_loop_head_inside_loop() {
    let pass = mk_pass();
    let positions = vec![(10, 20)];
    assert_eq!(pass.get_associated_loop_head(15, &positions), Some(10));
}

#[test]
fn test_get_associated_loop_head_at_latch() {
    let pass = mk_pass();
    let positions = vec![(10, 20)];
    // block_idx == loop_latch_idx is inside (condition is block_idx <= loop_latch_idx)
    assert_eq!(pass.get_associated_loop_head(20, &positions), Some(10));
}

#[test]
fn test_get_associated_loop_head_after_loop() {
    let pass = mk_pass();
    let positions = vec![(10, 20)];
    assert_eq!(pass.get_associated_loop_head(21, &positions), None);
}

#[test]
fn test_get_associated_loop_head_nested_loops_returns_innermost() {
    let pass = mk_pass();
    // Outer loop: 5..=30, Inner loop: 10..=20
    let positions = vec![(5, 30), (10, 20)];
    // Block 15 is inside both loops — last match wins (inner loop)
    assert_eq!(pass.get_associated_loop_head(15, &positions), Some(10));
}

#[test]
fn test_get_associated_loop_head_between_loops() {
    let pass = mk_pass();
    let positions = vec![(5, 10), (20, 30)];
    // Block 15 is between the two loops
    assert_eq!(pass.get_associated_loop_head(15, &positions), None);
}

#[test]
fn test_get_associated_loop_head_second_loop() {
    let pass = mk_pass();
    let positions = vec![(5, 10), (20, 30)];
    assert_eq!(pass.get_associated_loop_head(25, &positions), Some(20));
}
