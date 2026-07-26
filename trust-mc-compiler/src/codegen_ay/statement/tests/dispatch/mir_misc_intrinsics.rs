// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven misc intrinsic dispatch tests: noop intrinsics (forget, black_box),
//! bit manipulation, primitive comparison codegen.
//!
//! Split from dispatch.rs per #3678.

use super::super::*;
use super::mir_alloc_kani_mem::codegen_matching_call_destination;
use super::{assert_semantic_return_equals, build_codegen_for_fn, build_codegen_for_fn_info};
use std::collections::BTreeMap;

// =============================================================================

/// Probe source for no-op intrinsics.
const NOOP_DISPATCH_PROBE: &str = r#"
pub fn forget_probe(x: Vec<i32>) {
    core::mem::forget(x);
}

pub fn black_box_probe(x: u32) -> u32 {
    core::hint::black_box(x)
}
"#;

const TYPED_SWAP_DISPATCH_PROBE: &str = r#"
#![feature(core_intrinsics)]
#![allow(internal_features)]

pub fn typed_swap_return_x(a: u32, b: u32) -> u32 {
    let mut x = a;
    let mut y = b;
    unsafe {
        core::intrinsics::typed_swap_nonoverlapping(&mut x, &mut y);
    }
    x
}

pub fn typed_swap_return_y(a: u32, b: u32) -> u32 {
    let mut x = a;
    let mut y = b;
    unsafe {
        core::intrinsics::typed_swap_nonoverlapping(&mut x, &mut y);
    }
    y
}

pub fn typed_swap_raw_deref_return_pointer_read(a: u32, b: u32) -> u32 {
    let mut x = a;
    let mut y = b;
    let r: &mut u32 = &mut x;
    let p: *mut u32 = &raw mut *r;
    let q: *mut u32 = &raw mut y;
    unsafe {
        core::intrinsics::typed_swap_nonoverlapping(p, q);
        *p
    }
}

pub fn typed_swap_ref_arg_raw_deref_return_ref(r: &mut u32, b: u32) -> u32 {
    let mut y = b;
    let p: *mut u32 = &raw mut *r;
    let q: *mut u32 = &raw mut y;
    unsafe {
        core::intrinsics::typed_swap_nonoverlapping(p, q);
    }
    *r
}

pub unsafe fn typed_swap_raw_identity_return_p(p: *mut u32, q: *mut u32) -> *mut u32 {
    let p2: *mut u32 = &raw mut *p;
    unsafe {
        core::intrinsics::typed_swap_nonoverlapping(p2, q);
    }
    p
}
"#;

fn typed_swap_codegen_result(
    ctx: &mut AYCtx<'_, 'static>,
    fn_suffix: &str,
) -> (Vec<String>, BTreeMap<usize, Expr>, Expr) {
    let instance = find_instance_by_suffix(ctx, fn_suffix);
    let body = instance.body().expect("body");
    ctx.set_current_fn(instance);
    let tuple_usage = TupleUsageAnalysis::run(&body);
    let mut codegen = StatementCodegen::new(ctx, &body, tuple_usage);
    let mut call_paths = Vec::new();

    for bb in &body.blocks {
        for stmt in &bb.statements {
            codegen.codegen_statement(stmt);
        }
        if let rustc_public::mir::TerminatorKind::Call { func, .. } = &bb.terminator.kind
            && let Some(path) = codegen.resolve_callee_path(func)
        {
            call_paths.push(path);
        }
        let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
    }

    let local_exprs = body
        .arg_locals()
        .iter()
        .enumerate()
        .filter_map(|(idx, _)| {
            let local_idx = idx + 1;
            let base = codegen.ssa_base_name(&local_place(local_idx));
            codegen.env_lookup(&base).cloned().map(|expr| (local_idx, expr))
        })
        .collect();
    let ret_base = codegen.ssa_base_name(&local_place(0));
    let ret_expr = codegen.env_lookup(&ret_base).cloned().expect("return local should be assigned");
    (call_paths, local_exprs, ret_expr)
}

/// Test mem::forget dispatches as no-op through the intrinsic pipeline.
/// forget(x: Vec<i32>) is a no-op: it returns unit and should not assign the return local.
#[test]
fn test_mir_forget_dispatch() {
    with_test_ay_ctx_for_source(NOOP_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "forget_probe");
        assert!(info.call_count >= 1, "forget should have Call, got {}", info.call_count);
        // forget returns (): no bitvec return expected
        assert_eq!(info.ret_bitvec_width, None, "forget() returns unit, no bitvec return");
        assert!(!info.ret_is_bool, "forget() returns unit, not bool");
    });
}

/// Test hint::black_box dispatches as identity through the intrinsic pipeline.
/// Exercises both the inlined path (rustc may eliminate the call) and the
/// non-inlined path (call terminator dispatches through noop intrinsics).
#[test]
fn test_mir_black_box_dispatch() {
    with_test_ay_ctx_for_source(NOOP_DISPATCH_PROBE, |mut ctx| {
        // Always run full codegen to verify the function processes without panic.
        let (call_count, block_count) = build_codegen_for_fn(&mut ctx, "black_box_probe");
        assert!(block_count >= 1, "black_box_probe must have at least 1 basic block");

        // Also probe via callee matching to verify dispatch when the call exists.
        let (call_paths, matched_path, assigned, successor_count) =
            codegen_matching_call_destination(&mut ctx, "black_box_probe", "black_box");

        if matched_path.is_some() {
            // Non-inlined: call terminator present, verify dispatch result.
            assert!(
                successor_count.unwrap_or(0) > 0,
                "black_box identity dispatch should continue execution, paths: {call_paths:?}"
            );
            let ret = assigned.expect("black_box call destination should be assigned");
            assert_eq!(
                ret.sort().bitvec_width(),
                Some(32),
                "expected u32 return, got {:?}",
                ret.sort()
            );
        } else {
            // Inlined: rustc eliminated the call. Verify we saw no unexpected callees
            // and that the function still had Call terminators processed (e.g. drop glue).
            assert!(
                call_paths.is_empty() || call_paths.iter().all(|p| !p.contains("black_box")),
                "no black_box match but black_box appears in call paths: {call_paths:?}"
            );
            // The function returns u32 — inlined black_box is identity, so at minimum
            // the MIR has a return block. call_count may be 0 if fully inlined.
            assert!(
                block_count >= 2 || call_count == 0,
                "inlined black_box should have return block or no calls, \
                 got blocks={block_count} calls={call_count}"
            );
        }
    });
}

#[test]
fn test_mir_typed_swap_updates_first_pointee_local() {
    with_test_ay_ctx_for_source(TYPED_SWAP_DISPATCH_PROBE, |mut ctx| {
        let (call_paths, local_exprs, ret) =
            typed_swap_codegen_result(&mut ctx, "typed_swap_return_x");
        assert!(
            call_paths.iter().any(|path| path.contains("typed_swap_nonoverlapping")),
            "expected typed_swap_nonoverlapping call path, got {:?}",
            call_paths
        );
        let original_b = local_exprs.get(&2).expect("argument b should be tracked").clone();
        assert_semantic_return_equals(&ctx, ret, original_b, "typed_swap_return_x_is_old_b");
    });
}

#[test]
fn test_mir_typed_swap_updates_second_pointee_local() {
    with_test_ay_ctx_for_source(TYPED_SWAP_DISPATCH_PROBE, |mut ctx| {
        let (call_paths, local_exprs, ret) =
            typed_swap_codegen_result(&mut ctx, "typed_swap_return_y");
        assert!(
            call_paths.iter().any(|path| path.contains("typed_swap_nonoverlapping")),
            "expected typed_swap_nonoverlapping call path, got {:?}",
            call_paths
        );
        let original_a = local_exprs.get(&1).expect("argument a should be tracked").clone();
        assert_semantic_return_equals(&ctx, ret, original_a, "typed_swap_return_y_is_old_a");
    });
}

#[test]
fn test_mir_typed_swap_refreshes_raw_deref_alias() {
    with_test_ay_ctx_for_source(TYPED_SWAP_DISPATCH_PROBE, |mut ctx| {
        let (call_paths, local_exprs, ret) =
            typed_swap_codegen_result(&mut ctx, "typed_swap_raw_deref_return_pointer_read");
        assert!(
            call_paths.iter().any(|path| path.contains("typed_swap_nonoverlapping")),
            "expected typed_swap_nonoverlapping call path, got {:?}",
            call_paths
        );
        let original_b = local_exprs.get(&2).expect("argument b should be tracked").clone();
        assert_semantic_return_equals(
            &ctx,
            ret,
            original_b,
            "typed_swap_raw_deref_pointer_read_is_old_b",
        );
    });
}

#[test]
fn test_mir_typed_swap_updates_ref_arg_pointee_through_raw_deref() {
    with_test_ay_ctx_for_source(TYPED_SWAP_DISPATCH_PROBE, |mut ctx| {
        let (call_paths, local_exprs, ret) =
            typed_swap_codegen_result(&mut ctx, "typed_swap_ref_arg_raw_deref_return_ref");
        assert!(
            call_paths.iter().any(|path| path.contains("typed_swap_nonoverlapping")),
            "expected typed_swap_nonoverlapping call path, got {:?}",
            call_paths
        );
        let original_b = local_exprs.get(&2).expect("argument b should be tracked").clone();
        assert_semantic_return_equals(
            &ctx,
            ret,
            original_b,
            "typed_swap_ref_arg_raw_deref_return_ref_is_old_b",
        );
    });
}

#[test]
fn test_mir_typed_swap_raw_identity_does_not_clobber_pointer_local() {
    with_test_ay_ctx_for_source(TYPED_SWAP_DISPATCH_PROBE, |mut ctx| {
        let (call_paths, local_exprs, ret) =
            typed_swap_codegen_result(&mut ctx, "typed_swap_raw_identity_return_p");
        assert!(
            call_paths.iter().any(|path| path.contains("typed_swap_nonoverlapping")),
            "expected typed_swap_nonoverlapping call path, got {:?}",
            call_paths
        );
        let original_p = local_exprs.get(&1).expect("argument p should be tracked").clone();
        assert_semantic_return_equals(
            &ctx,
            ret,
            original_p,
            "typed_swap_raw_identity_keeps_pointer_local",
        );
    });
}

// =============================================================================
// MIR-driven tests: bit manipulation intrinsic dispatch
// Part of #2016: exercise dispatch_bit_ops → rotate, ctlz, cttz, bswap, etc.
// =============================================================================

/// Probe source for bit manipulation intrinsics.
const BIT_OPS_DISPATCH_PROBE: &str = r#"
pub fn rotate_left_probe(x: u32) -> u32 {
    x.rotate_left(7)
}

pub fn rotate_right_probe(x: u32) -> u32 {
    x.rotate_right(3)
}

pub fn leading_zeros_probe(x: u32) -> u32 {
    x.leading_zeros()
}

pub fn trailing_zeros_probe(x: u32) -> u32 {
    x.trailing_zeros()
}

pub fn count_ones_probe(x: u32) -> u32 {
    x.count_ones()
}

pub fn swap_bytes_probe(x: u32) -> u32 {
    x.swap_bytes()
}

pub fn reverse_bits_probe(x: u32) -> u32 {
    x.reverse_bits()
}
"#;

/// Test rotate_left dispatches through the bit-ops intrinsic pipeline.
#[test]
fn test_mir_rotate_left_dispatch() {
    with_test_ay_ctx_for_source(BIT_OPS_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "rotate_left_probe");
        assert!(info.call_count >= 1, "rotate_left should have Call, got {}", info.call_count);
        assert_eq!(info.ret_bitvec_width, Some(32), "rotate_left(u32) should return 32-bit");
        assert!(info.any_dest_assigned, "rotate_left should assign call destination");
    });
}

/// Test rotate_right dispatches through the bit-ops intrinsic pipeline.
#[test]
fn test_mir_rotate_right_dispatch() {
    with_test_ay_ctx_for_source(BIT_OPS_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "rotate_right_probe");
        assert!(info.call_count >= 1, "rotate_right should have Call, got {}", info.call_count);
        assert_eq!(info.ret_bitvec_width, Some(32), "rotate_right(u32) should return 32-bit");
        assert!(info.any_dest_assigned, "rotate_right should assign call destination");
    });
}

/// Test leading_zeros (ctlz) dispatches through the bit-ops intrinsic pipeline.
/// Returns u32, but MIR may inline the intrinsic — verify call path routing.
#[test]
fn test_mir_leading_zeros_dispatch() {
    with_test_ay_ctx_for_source(BIT_OPS_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "leading_zeros_probe");
        assert!(info.call_count >= 1, "leading_zeros should have Call, got {}", info.call_count);
        assert!(
            info.call_paths.iter().any(|p| p.contains("leading_zeros") || p.contains("ctlz")),
            "expected leading_zeros/ctlz in call paths, got {:?}",
            info.call_paths
        );
    });
}

/// Test trailing_zeros (cttz) dispatches through the bit-ops intrinsic pipeline.
#[test]
fn test_mir_trailing_zeros_dispatch() {
    with_test_ay_ctx_for_source(BIT_OPS_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "trailing_zeros_probe");
        assert!(info.call_count >= 1, "trailing_zeros should have Call, got {}", info.call_count);
        assert!(
            info.call_paths.iter().any(|p| p.contains("trailing_zeros") || p.contains("cttz")),
            "expected trailing_zeros/cttz in call paths, got {:?}",
            info.call_paths
        );
    });
}

/// Test count_ones (ctpop) dispatches through the bit-ops intrinsic pipeline.
#[test]
fn test_mir_count_ones_dispatch() {
    with_test_ay_ctx_for_source(BIT_OPS_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "count_ones_probe");
        assert!(info.call_count >= 1, "count_ones should have Call, got {}", info.call_count);
        assert!(
            info.call_paths.iter().any(|p| p.contains("count_ones") || p.contains("ctpop")),
            "expected count_ones/ctpop in call paths, got {:?}",
            info.call_paths
        );
    });
}

/// Test swap_bytes (bswap) dispatches through the bit-ops intrinsic pipeline.
#[test]
fn test_mir_swap_bytes_dispatch() {
    with_test_ay_ctx_for_source(BIT_OPS_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "swap_bytes_probe");
        assert!(info.call_count >= 1, "swap_bytes should have Call, got {}", info.call_count);
        assert!(
            info.call_paths.iter().any(|p| p.contains("swap_bytes") || p.contains("bswap")),
            "expected swap_bytes/bswap in call paths, got {:?}",
            info.call_paths
        );
    });
}

/// Test reverse_bits (bitreverse) dispatches through the bit-ops intrinsic pipeline.
#[test]
fn test_mir_reverse_bits_dispatch() {
    with_test_ay_ctx_for_source(BIT_OPS_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "reverse_bits_probe");
        assert!(info.call_count >= 1, "reverse_bits should have Call, got {}", info.call_count);
        assert!(
            info.call_paths.iter().any(|p| p.contains("reverse_bits") || p.contains("bitreverse")),
            "expected reverse_bits/bitreverse in call paths, got {:?}",
            info.call_paths
        );
    });
}

// =============================================================================
// MIR-driven tests: primitive comparison codegen
// Part of #2016: exercise `Rvalue::BinaryOp` comparison lowering in codegen_statement.
// =============================================================================

/// Probe source for primitive comparison codegen (BinaryOp lowering).
const COMPARISON_CODEGEN_PROBE: &str = r#"
pub fn partial_ord_lt_probe(a: u32, b: u32) -> bool {
    a < b
}

pub fn partial_ord_le_probe(a: u32, b: u32) -> bool {
    a <= b
}

pub fn partial_ord_gt_probe(a: u32, b: u32) -> bool {
    a > b
}

pub fn partial_ord_ge_probe(a: u32, b: u32) -> bool {
    a >= b
}
"#;

/// Test comparison codegen through the MIR pipeline.
///
/// For primitive u32, rustc lowers `a < b` to `Rvalue::BinaryOp(Lt)` in a
/// single basic block — NOT a Call to `PartialOrd::lt`. These tests exercise
/// the rvalue comparison codegen path in `codegen_statement`, not
/// `dispatch_partial_ord` (which handles trait method calls on non-primitive
/// types). We verify the codegen pipeline completes without panic and that the
/// function body contains exactly 1 basic block (the optimized
/// compare-and-return pattern) with 0 calls (BinaryOp, not trait dispatch).
#[test]
fn test_mir_comparison_lt_codegen() {
    with_test_ay_ctx_for_source(COMPARISON_CODEGEN_PROBE, |mut ctx| {
        let (call_count, block_count) = build_codegen_for_fn(&mut ctx, "partial_ord_lt_probe");
        assert_eq!(block_count, 1, "lt: expected 1 BB (compare+return), got {block_count}");
        assert_eq!(call_count, 0, "lt: expected 0 calls (BinaryOp, not trait), got {call_count}");
    });
}

#[test]
fn test_mir_comparison_le_codegen() {
    with_test_ay_ctx_for_source(COMPARISON_CODEGEN_PROBE, |mut ctx| {
        let (call_count, block_count) = build_codegen_for_fn(&mut ctx, "partial_ord_le_probe");
        assert_eq!(block_count, 1, "le: expected 1 BB (compare+return), got {block_count}");
        assert_eq!(call_count, 0, "le: expected 0 calls (BinaryOp, not trait), got {call_count}");
    });
}

#[test]
fn test_mir_comparison_gt_codegen() {
    with_test_ay_ctx_for_source(COMPARISON_CODEGEN_PROBE, |mut ctx| {
        let (call_count, block_count) = build_codegen_for_fn(&mut ctx, "partial_ord_gt_probe");
        assert_eq!(block_count, 1, "gt: expected 1 BB (compare+return), got {block_count}");
        assert_eq!(call_count, 0, "gt: expected 0 calls (BinaryOp, not trait), got {call_count}");
    });
}

#[test]
fn test_mir_comparison_ge_codegen() {
    with_test_ay_ctx_for_source(COMPARISON_CODEGEN_PROBE, |mut ctx| {
        let (call_count, block_count) = build_codegen_for_fn(&mut ctx, "partial_ord_ge_probe");
        assert_eq!(block_count, 1, "ge: expected 1 BB (compare+return), got {block_count}");
        assert_eq!(call_count, 0, "ge: expected 0 calls (BinaryOp, not trait), got {call_count}");
    });
}

// -----------------------------------------------------------------------------
