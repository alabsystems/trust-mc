// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven helper-path tests: resolve_callee_path, transmute, pointer offset,
//! closure dispatch, extract_element_type_layout.
//!
//! Split from dispatch.rs per #3678.

use super::super::*;
use super::{assert_semantic_return_equals, build_codegen_for_fn_info};

// -----------------------------------------------------------------------------
// resolve_callee_path: MIR-driven test
// -----------------------------------------------------------------------------

/// Probe source: simple function call to exercise resolve_callee_path.
const CALLEE_RESOLVE_PROBE: &str = r#"
pub fn callee_resolve_probe(_x: i32) -> usize {
    let v: Vec<i32> = Vec::new();
    v.len()
}
"#;

/// Test that resolve_callee_path resolves Vec::new and Vec::len paths.
#[test]
fn test_mir_resolve_callee_path() {
    with_test_ay_ctx_for_source(CALLEE_RESOLVE_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "callee_resolve_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Find Call terminators and resolve their callee paths
        let mut resolved_paths = Vec::new();
        for bb in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &bb.terminator.kind
                && let Some(path) = codegen.resolve_callee_path(func)
            {
                resolved_paths.push(path);
            }
        }

        // Should resolve at least one path (Vec::new or Vec::len)
        assert!(!resolved_paths.is_empty(), "resolve_callee_path should find at least one path");

        // At least one should contain "Vec"
        let has_vec_path = resolved_paths.iter().any(|p| p.contains("Vec") || p.contains("vec"));
        assert!(has_vec_path, "should resolve Vec-related paths, got: {:?}", resolved_paths);
    });
}

// -----------------------------------------------------------------------------
// codegen_transmute_intrinsic: MIR-driven test
// -----------------------------------------------------------------------------

/// Probe source: transmute between compatible types.
const TRANSMUTE_PROBE: &str = r#"
#![allow(unnecessary_transmutes)]
pub fn transmute_i32_to_u32(x: i32) -> u32 {
    unsafe { core::mem::transmute(x) }
}

pub fn transmute_u8_to_bool(x: u8) -> bool {
    unsafe { core::mem::transmute(x) }
}
"#;

/// Test transmute dispatch through the full pipeline.
/// Note: rustc lowers `core::mem::transmute` to `CastKind::Transmute` (a Rvalue),
/// not a function Call terminator. The test verifies the return sort matches
/// the expected output type.
#[test]
fn test_mir_transmute_dispatch() {
    with_test_ay_ctx_for_source(TRANSMUTE_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "transmute_i32_to_u32");
        assert!(info.block_count >= 1, "should have at least 1 basic block");
        // transmute(i32) → u32: return should be 32-bit bitvec
        assert_eq!(
            info.ret_bitvec_width,
            Some(32),
            "transmute i32→u32 should produce 32-bit return"
        );
    });
}

/// Test transmute u8→bool dispatch (narrowing transmute).
#[test]
fn test_mir_transmute_u8_to_bool_dispatch() {
    with_test_ay_ctx_for_source(TRANSMUTE_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "transmute_u8_to_bool");
        assert!(info.block_count >= 1, "should have at least 1 basic block");
        // transmute(u8) → bool: return sort should be bool or 8-bit bitvec
        assert!(
            info.ret_is_bool || info.ret_bitvec_width == Some(8),
            "transmute u8→bool should produce bool or 8-bit return, got bv={:?} bool={}",
            info.ret_bitvec_width,
            info.ret_is_bool
        );
    });
}

// -----------------------------------------------------------------------------
// codegen_ptr_offset_intrinsic: MIR-driven test
// -----------------------------------------------------------------------------

/// Probe source: pointer offset arithmetic.
const PTR_OFFSET_PROBE: &str = r#"
pub fn ptr_offset_probe(p: *const i32, n: isize) -> *const i32 {
    unsafe { p.offset(n) }
}

pub fn ptr_add_probe(p: *const u64, n: usize) -> *const u64 {
    unsafe { p.add(n) }
}
"#;

/// Test pointer offset dispatch through MIR pipeline.
#[test]
fn test_mir_ptr_offset_dispatch() {
    with_test_ay_ctx_for_source(PTR_OFFSET_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "ptr_offset_probe");
        assert!(info.call_count >= 1, "ptr.offset should have Call, got {}", info.call_count);
        // ptr.offset returns *const i32 — pointer-width bitvec
        assert_eq!(
            info.ret_bitvec_width,
            Some(POINTER_WIDTH),
            "ptr.offset return should be pointer-width"
        );
    });
}

/// Test pointer add dispatch (unsigned offset variant).
#[test]
fn test_mir_ptr_add_dispatch() {
    with_test_ay_ctx_for_source(PTR_OFFSET_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "ptr_add_probe");
        assert!(info.call_count >= 1, "ptr.add should have Call, got {}", info.call_count);
        assert_eq!(
            info.ret_bitvec_width,
            Some(POINTER_WIDTH),
            "ptr.add return should be pointer-width"
        );
    });
}

// -----------------------------------------------------------------------------
// codegen_closure_call: MIR-driven test
// -----------------------------------------------------------------------------

/// Probe source: closure calls exercising codegen_closure_call.
const CLOSURE_PROBE: &str = r#"
pub fn closure_probe(x: i32) -> i32 {
    let add_one = |v: i32| v + 1;
    add_one(x)
}

pub fn closure_with_capture(x: i32, y: i32) -> i32 {
    let add_y = |v: i32| v + y;
    add_y(x)
}

pub fn closure_const() -> i32 {
    let add_one = |v: i32| v + 1;
    add_one(4)
}

pub fn closure_with_capture_const() -> i32 {
    let y = 3;
    let add_y = |v: i32| v + y;
    add_y(4)
}
"#;

const INLINE_AND_FN_PTR_PROBE: &str = r#"
fn add_one(x: u32) -> u32 {
    x + 1
}

pub fn fn_inline_const() -> u32 {
    add_one(4)
}

pub fn fn_ptr_const() -> u32 {
    let f: fn(u32) -> u32 = add_one;
    f(4)
}
"#;

/// Test closure call dispatch — verifies MIR structure, not return values (#2440).
#[test]
fn test_mir_closure_call_dispatch() {
    with_test_ay_ctx_for_source(CLOSURE_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "closure_probe");
        assert!(info.call_count >= 1, "closure call should have Call, got {}", info.call_count);
        assert!(
            info.call_paths.iter().any(|p| p.contains("closure")),
            "closure probe should resolve to a closure path, got {:?}",
            info.call_paths
        );
    });
}

/// Test closure with capture — verifies MIR structure, not return values (#2440).
#[test]
fn test_mir_closure_with_capture_dispatch() {
    with_test_ay_ctx_for_source(CLOSURE_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "closure_with_capture");
        assert!(info.call_count >= 1, "captured closure should have Call, got {}", info.call_count);
        assert!(
            info.call_paths.iter().any(|p| p.contains("closure")),
            "captured closure should resolve to a closure path, got {:?}",
            info.call_paths
        );
    });
}

/// The BMC closure pilot should execute a simple non-capturing closure body.
#[test]
fn test_mir_closure_call_semantic_return_is_five() {
    with_test_ay_ctx_for_source(CLOSURE_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "closure_const");
        let ret_expr = info.ret_expr.expect("closure_const should assign return local");
        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            Expr::bitvec_const(5u64, 32),
            "closure_const_is_five",
        );
    });
}

/// Captured closures should also use the mini-inline path when the body is linear.
#[test]
fn test_mir_closure_with_capture_semantic_return_is_seven() {
    with_test_ay_ctx_for_source(CLOSURE_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "closure_with_capture_const");
        let ret_expr =
            info.ret_expr.expect("closure_with_capture_const should assign return local");
        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            Expr::bitvec_const(7u64, 32),
            "closure_with_capture_const_is_seven",
        );
    });
}

/// Direct `FnDef` calls should use the BMC mini-inline path for small callees.
#[test]
fn test_mir_fn_inline_semantic_return_is_five() {
    with_test_ay_ctx_for_source(INLINE_AND_FN_PTR_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "fn_inline_const");
        let ret_expr = info.ret_expr.expect("fn_inline_const should assign return local");
        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            Expr::bitvec_const(5u64, 32),
            "fn_inline_const_is_five",
        );
    });
}

/// Reified function pointers should resolve to a concrete callee body in BMC.
#[test]
fn test_mir_fn_ptr_semantic_return_is_five() {
    with_test_ay_ctx_for_source(INLINE_AND_FN_PTR_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "fn_ptr_const");
        let ret_expr = info.ret_expr.expect("fn_ptr_const should assign return local");
        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            Expr::bitvec_const(5u64, 32),
            "fn_ptr_const_is_five",
        );
    });
}

// -----------------------------------------------------------------------------
