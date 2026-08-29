// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for the constant-trip-count analysis.
//!
//! MIR constants can only be built inside a rustc session (`MirConst::from_bool`
//! and friends all go through `with(|cx| ..)`), so the tests here cover the two
//! halves that are reachable without one:
//!
//! * the exact integer semantics the recurrence evaluator relies on
//!   (`eval_binop`, `to_signed`, `truncate`) — including the `>>=` shape from
//!   `tests/expected/test2` and the `/` shape from `tests/expected/test4`;
//! * the abstract store's invalidation rules and the CFG-level fail-open paths.
//!
//! End-to-end derivation is covered by the `tests/expected` harnesses
//! (test1..test4) and by the explicit-`--unwind` controls.

#![allow(clippy::panic)] // Tests use panic! for assertion failures

use super::*;
use rustc_public::mir::{
    BasicBlock, Body, LocalDecl, Mutability, Operand, Place, Statement, Terminator, TerminatorKind,
};

/// Create dummy Span/Ty handles for unit tests that run without a rustc session.
///
/// SAFETY: opaque handles (internally integer indices) that are never
/// dereferenced or handed back to the compiler. Mirrors `loop_unroll/tests.rs`.
fn dummy_span() -> rustc_public::ty::Span {
    unsafe { std::mem::zeroed() }
}

fn dummy_ty() -> rustc_public::ty::Ty {
    unsafe { std::mem::zeroed() }
}

fn i32_val(v: i32) -> Val {
    Val::Int { bits: truncate(v as i128 as u128, 32), width: 32, signed: true }
}

fn u8_val(v: u8) -> Val {
    Val::Int { bits: u128::from(v), width: 8, signed: false }
}

// ---------------------------------------------------------------------------
// Integer semantics
// ---------------------------------------------------------------------------

#[test]
fn to_signed_round_trips_negative_i32() {
    let bits = truncate(-1i128 as u128, 32);
    assert_eq!(bits, 0xFFFF_FFFF);
    assert_eq!(to_signed(bits, 32), -1);
    assert_eq!(to_signed(truncate(i32::MIN as i128 as u128, 32), 32), i128::from(i32::MIN));
}

#[test]
fn test1_recurrence_counts_ten_iterations() {
    // tests/expected/test1: i = 10; while i != 0 { i -= 1 }
    let mut i = i32_val(10);
    let mut trips = 0u32;
    while i != i32_val(0) {
        i = eval_binop(BinOp::Sub, i, i32_val(1)).expect("i32 sub stays in range");
        trips += 1;
        assert!(trips < 100, "recurrence must terminate");
    }
    assert_eq!(trips, 10);
}

#[test]
fn test2_shr_recurrence_counts_two_iterations() {
    // tests/expected/test2: a = 4; while a != 1 { a >>= 1 }
    let mut a = i32_val(4);
    let mut trips = 0u32;
    while a != i32_val(1) {
        a = eval_binop(BinOp::Shr, a, i32_val(1)).expect("i32 shr by 1 is representable");
        trips += 1;
        assert!(trips < 100, "recurrence must terminate");
    }
    assert_eq!(trips, 2);
}

#[test]
fn test4_div_recurrence_counts_two_iterations() {
    // tests/expected/test4: a = 4; while a != 1 { a = div(a, 2) }
    let mut a = i32_val(4);
    let mut trips = 0u32;
    while a != i32_val(1) {
        a = eval_binop(BinOp::Div, a, i32_val(2)).expect("i32 div by 2 is representable");
        trips += 1;
        assert!(trips < 100, "recurrence must terminate");
    }
    assert_eq!(trips, 2);
}

#[test]
fn arithmetic_shift_right_is_signed_for_signed_types() {
    // -8 >> 1 == -4 (arithmetic), not 2147483644 (logical).
    assert_eq!(eval_binop(BinOp::Shr, i32_val(-8), i32_val(1)), Some(i32_val(-4)));
    // The unsigned twin shifts in zeros.
    let u = Val::Int { bits: 0xF8, width: 8, signed: false };
    assert_eq!(eval_binop(BinOp::Shr, u, u8_val(1)), Some(u8_val(0x7C)));
}

#[test]
fn overflowing_arithmetic_is_unknown_not_wrapped() {
    // A trapping `+` must not be modelled as a wrap: that would let the
    // simulator invent a trip count for an execution that never runs.
    assert_eq!(eval_binop(BinOp::Add, i32_val(i32::MAX), i32_val(1)), None);
    assert_eq!(eval_binop(BinOp::Sub, i32_val(i32::MIN), i32_val(1)), None);
    assert_eq!(eval_binop(BinOp::Sub, u8_val(0), u8_val(1)), None);
    assert_eq!(eval_binop(BinOp::Add, u8_val(255), u8_val(1)), None);
}

#[test]
fn division_and_shift_edge_cases_are_unknown() {
    assert_eq!(eval_binop(BinOp::Div, i32_val(1), i32_val(0)), None);
    assert_eq!(eval_binop(BinOp::Rem, i32_val(1), i32_val(0)), None);
    // i32::MIN / -1 overflows.
    assert_eq!(eval_binop(BinOp::Div, i32_val(i32::MIN), i32_val(-1)), None);
    // Shift amount >= width is UB in Rust and reported as a check.
    assert_eq!(eval_binop(BinOp::Shr, i32_val(4), i32_val(32)), None);
    assert_eq!(eval_binop(BinOp::Shl, i32_val(4), i32_val(-1)), None);
}

#[test]
fn signed_and_unsigned_comparisons_differ() {
    // 0xFF as i8 is -1 (< 0); as u8 it is 255 (> 0).
    let neg = Val::Int { bits: 0xFF, width: 8, signed: true };
    let zero_s = Val::Int { bits: 0, width: 8, signed: true };
    assert_eq!(eval_binop(BinOp::Lt, neg, zero_s), Some(Val::Bool(true)));
    assert_eq!(eval_binop(BinOp::Lt, u8_val(0xFF), u8_val(0)), Some(Val::Bool(false)));
}

#[test]
fn mismatched_operand_shapes_are_unknown() {
    // Only shifts may mix widths; everything else must match exactly.
    assert_eq!(eval_binop(BinOp::Add, i32_val(1), u8_val(1)), None);
}

#[test]
fn switch_bits_use_the_two_complement_pattern() {
    // `switchInt` case values are raw bit patterns, so -1_i32 must match
    // 0xFFFF_FFFF, not `-1` reinterpreted as a huge u128.
    assert_eq!(i32_val(-1).switch_bits(), (0xFFFF_FFFF, 32));
    assert_eq!(Val::Bool(true).switch_bits(), (1, 8));
    assert_eq!(Val::Bool(false).switch_bits(), (0, 8));
}

#[test]
fn a_sign_extended_switch_case_still_matches() {
    // MIR writes a negative case value sign-extended to the full u128 (the
    // `Ordering::Less == -1` shape). Masking it to the discriminant width is
    // what makes the simulation take the right edge instead of `otherwise`.
    let (bits, width) = i32_val(-1).switch_bits();
    assert_eq!(truncate(-1i128 as u128, width), bits);
    // Unmasked, the two do NOT compare equal — that is the bug being prevented.
    assert_ne!(-1i128 as u128, bits);
}

// ---------------------------------------------------------------------------
// Abstract store
// ---------------------------------------------------------------------------

fn local_place(local: usize) -> Place {
    Place { local, projection: vec![] }
}

fn field_place(local: usize, idx: usize) -> Place {
    Place { local, projection: vec![ProjectionElem::Field(idx, dummy_ty())] }
}

fn deref_place(local: usize) -> Place {
    Place { local, projection: vec![ProjectionElem::Deref] }
}

#[test]
fn store_reads_back_a_whole_local_write() {
    let mut store = Store::default();
    let clean = vec![false; 8];
    store.write(&local_place(1), Some(i32_val(7)));
    assert_eq!(store.get(&local_place(1), &clean), Some(i32_val(7)));
}

#[test]
fn store_reads_back_a_tuple_field_write() {
    // This is the `_5 = CheckedAdd(..)` / `_1 = move (_5.0: i32)` shape.
    let mut store = Store::default();
    let clean = vec![false; 8];
    store.write(&field_place(5, 0), Some(i32_val(3)));
    assert_eq!(store.get(&field_place(5, 0), &clean), Some(i32_val(3)));
    // The whole-local view of a partially written local stays unknown.
    assert_eq!(store.get(&local_place(5), &clean), None);
}

#[test]
fn whole_local_write_invalidates_stale_field_views() {
    let mut store = Store::default();
    let clean = vec![false; 8];
    store.write(&field_place(5, 0), Some(i32_val(3)));
    store.write(&local_place(5), Some(i32_val(9)));
    assert_eq!(store.get(&field_place(5, 0), &clean), None);
    assert_eq!(store.get(&local_place(5), &clean), Some(i32_val(9)));
}

#[test]
fn unknown_write_erases_the_previous_value() {
    let mut store = Store::default();
    let clean = vec![false; 8];
    store.write(&local_place(1), Some(i32_val(7)));
    store.write(&local_place(1), None);
    assert_eq!(store.get(&local_place(1), &clean), None);
}

#[test]
fn deref_write_forgets_the_whole_base_local() {
    let mut store = Store::default();
    let clean = vec![false; 8];
    store.write(&local_place(1), Some(i32_val(7)));
    store.write(&field_place(1, 0), Some(i32_val(8)));
    store.write(&deref_place(1), Some(i32_val(9)));
    assert_eq!(store.get(&local_place(1), &clean), None);
    assert_eq!(store.get(&field_place(1, 0), &clean), None);
}

#[test]
fn poisoned_locals_never_read_back() {
    let mut store = Store::default();
    let mut poisoned = vec![false; 8];
    store.write(&local_place(2), Some(i32_val(7)));
    assert_eq!(store.get(&local_place(2), &poisoned), Some(i32_val(7)));
    poisoned[2] = true;
    assert_eq!(store.get(&local_place(2), &poisoned), None);
}

#[test]
fn out_of_range_locals_read_as_unknown() {
    let store = Store::default();
    let poisoned = vec![false; 2];
    assert_eq!(store.get(&local_place(9), &poisoned), None);
}

// ---------------------------------------------------------------------------
// Address-taken poisoning
// ---------------------------------------------------------------------------

fn body_from(blocks: Vec<BasicBlock>, local_count: usize) -> Body {
    let span = dummy_span();
    let ty = dummy_ty();
    let locals = vec![LocalDecl { ty, span, mutability: Mutability::Mut }; local_count];
    Body::new(blocks, locals, 0, Vec::new(), None, span)
}

fn stmt(kind: StatementKind) -> Statement {
    Statement { kind, span: dummy_span() }
}

fn block(statements: Vec<Statement>, kind: TerminatorKind) -> BasicBlock {
    BasicBlock { statements, terminator: Terminator { kind, span: dummy_span() } }
}

#[test]
fn taking_a_reference_poisons_the_referent() {
    // `_2 = &mut _1` means a later write through the reference is invisible to
    // the simulator, so `_1` must never be trusted.
    let body = body_from(
        vec![block(
            vec![stmt(StatementKind::Assign(
                local_place(2),
                Rvalue::Ref(
                    rustc_public::ty::Region { kind: rustc_public::ty::RegionKind::ReErased },
                    rustc_public::mir::BorrowKind::Shared,
                    local_place(1),
                ),
            ))],
            TerminatorKind::Return,
        )],
        3,
    );
    let poisoned = poisoned_locals(&body);
    assert!(poisoned[1], "referent must be poisoned");
    assert!(!poisoned[2], "the reference local itself carries no modelled value");
}

#[test]
fn copy_for_deref_poisons_the_source() {
    let body = body_from(
        vec![block(
            vec![stmt(StatementKind::Assign(local_place(2), Rvalue::CopyForDeref(local_place(1))))],
            TerminatorKind::Return,
        )],
        3,
    );
    assert!(poisoned_locals(&body)[1]);
}

#[test]
fn writing_through_a_deref_poisons_the_pointer_local() {
    let body = body_from(
        vec![block(
            vec![stmt(StatementKind::Assign(deref_place(1), Rvalue::CopyForDeref(local_place(2))))],
            TerminatorKind::Return,
        )],
        3,
    );
    let poisoned = poisoned_locals(&body);
    assert!(poisoned[1]);
    assert!(poisoned[2]);
}

// ---------------------------------------------------------------------------
// Fail-open control flow
// ---------------------------------------------------------------------------

#[test]
fn acyclic_body_derives_nothing() {
    // No loop, nothing to bound: the caller must keep today's depth.
    let body = body_from(vec![block(vec![], TerminatorKind::Return)], 1);
    assert_eq!(derive_const_trip_unroll_depth(&body), None);
}

#[test]
fn non_terminating_goto_loop_derives_nothing() {
    // `loop {}` — the simulation runs out of steps INSIDE the loop, so the
    // count is incomplete and nothing is derived. This is the fail-open case
    // that keeps `function-contract/diverging_loop` on today's behaviour.
    let body = body_from(vec![block(vec![], TerminatorKind::Goto { target: 0 })], 1);
    assert_eq!(derive_const_trip_unroll_depth(&body), None);

    let loops = single_loop_map(&body);
    let counts = simulate(&body, &loops);
    match counts.outcome {
        SimOutcome::Bailed { inside } => assert_eq!(inside, vec![0]),
        other => panic!("expected a bail inside the loop, got {other:?}"),
    }
    // It DID observe a long run — the run is simply not trustworthy.
    assert!(counts.max_run[&0] > 0);
}

#[test]
fn switch_on_an_unknown_value_inside_a_loop_derives_nothing() {
    // bb0 -> bb1; bb1 switches on an unmodelled local -> {bb1, bb2}.
    // The header's exit condition is symbolic, so no bound may be derived.
    let body = body_from(
        vec![
            block(vec![], TerminatorKind::Goto { target: 1 }),
            block(
                vec![],
                TerminatorKind::SwitchInt {
                    discr: Operand::Copy(local_place(1)),
                    targets: rustc_public::mir::SwitchTargets::new(vec![(0, 2)], 1),
                },
            ),
            block(vec![], TerminatorKind::Return),
        ],
        2,
    );
    assert_eq!(derive_const_trip_unroll_depth(&body), None);
}

#[test]
fn inline_asm_inside_a_loop_derives_nothing() {
    // Inline asm can mutate anything the store models, so the run is discarded.
    let body = body_from(
        vec![
            block(vec![], TerminatorKind::Goto { target: 1 }),
            block(
                vec![],
                TerminatorKind::InlineAsm {
                    template: String::new(),
                    operands: Vec::new(),
                    options: String::new(),
                    line_spans: String::new(),
                    destination: Some(1),
                    unwind: rustc_public::mir::UnwindAction::Unreachable,
                },
            ),
        ],
        1,
    );
    assert_eq!(derive_const_trip_unroll_depth(&body), None);
}

fn single_loop_map(body: &Body) -> HashMap<usize, Vec<bool>> {
    let cfg = Cfg::from_body(body);
    let headers = find_loop_headers(&cfg).expect("reducible cfg");
    let mut loops = HashMap::new();
    for (header, mut latches) in headers {
        latches.sort_unstable();
        latches.dedup();
        loops.insert(header, natural_loop(&cfg, header, &latches).in_loop);
    }
    loops
}
