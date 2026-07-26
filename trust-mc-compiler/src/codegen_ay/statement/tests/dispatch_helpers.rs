// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for dispatch/helpers.rs — transmute, pointer offset,
//! closure calls, and abstracted fallback.
//!
//! Part of #2016: test coverage for dispatch/helpers.rs (492 lines, 0 tests).

use super::*;

/// Run MIR statement+terminator codegen for one probe function and invoke callback
/// with:
/// - number of Call terminators
/// - resolved call paths (best-effort via resolve_callee_path)
/// - whether any Call destination was assigned in the SSA env
/// - return-local expression (if available)
fn with_probe_codegen<F>(source: &str, fn_suffix: &str, callback: F)
where
    F: FnOnce(usize, Vec<String>, bool, Option<ay_bindings::Expr>) + Send,
{
    with_test_ay_ctx_for_source(source, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, fn_suffix);
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }

        let mut call_count = 0;
        let mut call_paths = Vec::new();
        let mut call_dest_assigned = false;
        for bb in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, destination, .. } =
                &bb.terminator.kind
            {
                call_count += 1;
                if let Some(path) = codegen.resolve_callee_path(func) {
                    call_paths.push(path);
                }
                let dest_base = codegen.ssa_base_name(destination);
                let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
                call_dest_assigned |= codegen.env_lookup(&dest_base).is_some();
            } else {
                let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
            }
        }

        let ret_place = local_place(0);
        let ret_base = codegen.ssa_base_name(&ret_place);
        let ret_expr = codegen.env_lookup(&ret_base).cloned();
        callback(call_count, call_paths, call_dest_assigned, ret_expr);
    });
}

// =============================================================================
// Transmute intrinsic
// =============================================================================

const TRANSMUTE_PROBE: &str = r#"
#![allow(unnecessary_transmutes)]
pub fn transmute_u32_to_i32(x: u32) -> i32 {
    unsafe { core::mem::transmute(x) }
}

pub fn transmute_u8_to_bool(x: u8) -> bool {
    unsafe { core::mem::transmute(x) }
}
"#;

/// Test transmute from u32 to i32 through the codegen pipeline.
#[test]
fn test_mir_transmute_u32_to_i32() {
    with_probe_codegen(
        TRANSMUTE_PROBE,
        "transmute_u32_to_i32",
        |call_count, _call_paths, _call_dest_assigned, ret_expr| {
            assert_eq!(call_count, 0, "transmute should lower as Cast, not Call terminators");
            let ret_expr = ret_expr.expect("transmute_u32_to_i32 should assign return local");
            assert_eq!(ret_expr.sort().bitvec_width(), Some(32), "i32 return should be bv32");
        },
    );
}

/// Test transmute from u8 to bool through the codegen pipeline.
#[test]
fn test_mir_transmute_u8_to_bool() {
    with_probe_codegen(
        TRANSMUTE_PROBE,
        "transmute_u8_to_bool",
        |call_count, _call_paths, _call_dest_assigned, ret_expr| {
            assert_eq!(call_count, 0, "transmute should lower as Cast, not Call terminators");
            let ret_expr = ret_expr.expect("transmute_u8_to_bool should assign return local");
            let sort = ret_expr.sort();
            let width = sort.bitvec_width();
            assert!(
                sort.is_bool() || matches!(width, Some(1) | Some(8)),
                "bool transmute should produce bool-like sort, got {:?}",
                sort
            );
        },
    );
}

// =============================================================================
// Pointer offset intrinsic
// =============================================================================

const PTR_OFFSET_PROBE: &str = r#"
pub fn ptr_add_u32(p: *const u32, n: usize) -> *const u32 {
    unsafe { p.add(n) }
}

pub fn ptr_add_u8(p: *mut u8, n: usize) -> *mut u8 {
    unsafe { p.add(n) }
}

pub fn ptr_sub_u32(p: *const u32, n: usize) -> *const u32 {
    unsafe { p.sub(n) }
}
"#;

/// Test pointer add with u32 elements (4-byte stride).
#[test]
fn test_mir_ptr_add_u32() {
    with_probe_codegen(
        PTR_OFFSET_PROBE,
        "ptr_add_u32",
        |call_count, _call_paths, call_dest_assigned, ret_expr| {
            assert!(call_count >= 1, "ptr.add should lower with at least one Call terminator");
            assert!(call_dest_assigned, "ptr.add call should assign its destination");
            let ret_expr = ret_expr.expect("ptr_add_u32 should assign return local");
            assert_eq!(
                ret_expr.sort().bitvec_width(),
                Some(POINTER_WIDTH),
                "pointer add result should be pointer width"
            );
        },
    );
}

/// Test pointer add with u8 elements (1-byte stride).
#[test]
fn test_mir_ptr_add_u8() {
    with_probe_codegen(
        PTR_OFFSET_PROBE,
        "ptr_add_u8",
        |call_count, _call_paths, call_dest_assigned, ret_expr| {
            assert!(call_count >= 1, "ptr.add should lower with at least one Call terminator");
            assert!(call_dest_assigned, "ptr.add call should assign its destination");
            let ret_expr = ret_expr.expect("ptr_add_u8 should assign return local");
            assert_eq!(
                ret_expr.sort().bitvec_width(),
                Some(POINTER_WIDTH),
                "pointer add result should be pointer width"
            );
        },
    );
}

/// Test pointer sub (offset with negative direction).
#[test]
fn test_mir_ptr_sub_u32() {
    with_probe_codegen(
        PTR_OFFSET_PROBE,
        "ptr_sub_u32",
        |call_count, call_paths, _call_dest_assigned, ret_expr| {
            assert!(call_count >= 1, "ptr.sub should lower with at least one Call terminator");
            assert!(
                call_paths.iter().any(|p| p.contains("::sub") || p.contains("offset")),
                "ptr.sub probe should resolve a sub/offset-like call path, got {call_paths:?}"
            );
            if let Some(ret_expr) = ret_expr {
                assert_eq!(
                    ret_expr.sort().bitvec_width(),
                    Some(POINTER_WIDTH),
                    "pointer sub result should be pointer width when return local is materialized"
                );
            }
        },
    );
}

/// Test ptr.offset with isize argument — verifies sign-extension of count operand.
///
/// Part of #2467: codegen_ptr_offset_intrinsic must sign-extend isize count,
/// not zero-extend. A negative offset like -1 in narrow width must preserve
/// its sign when widened to pointer width.
#[test]
fn test_mir_ptr_offset_isize() {
    const PTR_OFFSET_ISIZE_PROBE: &str = r#"
pub fn ptr_offset_isize(p: *const u32, n: isize) -> *const u32 {
    unsafe { p.offset(n) }
}
"#;
    with_probe_codegen(
        PTR_OFFSET_ISIZE_PROBE,
        "ptr_offset_isize",
        |call_count, _call_paths, call_dest_assigned, ret_expr| {
            assert!(call_count >= 1, "ptr.offset should lower with at least one Call terminator");
            assert!(call_dest_assigned, "ptr.offset call should assign its destination");
            let ret_expr = ret_expr.expect("ptr_offset_isize should assign return local");
            assert_eq!(
                ret_expr.sort().bitvec_width(),
                Some(POINTER_WIDTH),
                "pointer offset result should be pointer width"
            );
        },
    );
}

// =============================================================================
// Pointer offset_from intrinsic
// =============================================================================

const PTR_OFFSET_FROM_PROBE: &str = r#"
pub fn offset_from_u32(a: *const u32, b: *const u32) -> isize {
    unsafe { a.offset_from(b) }
}
"#;

/// Test ptr::offset_from through the codegen pipeline.
#[test]
fn test_mir_ptr_offset_from() {
    with_probe_codegen(
        PTR_OFFSET_FROM_PROBE,
        "offset_from_u32",
        |call_count, _call_paths, call_dest_assigned, ret_expr| {
            assert!(call_count >= 1, "offset_from should lower with at least one Call terminator");
            assert!(call_dest_assigned, "offset_from call should assign its destination");
            let ret_expr = ret_expr.expect("offset_from_u32 should assign return local");
            assert_eq!(
                ret_expr.sort().bitvec_width(),
                Some(POINTER_WIDTH),
                "offset_from result should be pointer width (isize)"
            );
        },
    );
}

// =============================================================================
// Closure call dispatch
// =============================================================================

const CLOSURE_PROBE: &str = r#"
#[inline(never)]
pub fn call_via_trait(f: &dyn Fn(u32) -> u32, x: u32) -> u32 {
    f(x)
}

pub fn apply_closure(x: u32) -> u32 {
    let f = |v: u32| v + 1;
    call_via_trait(&f, x)
}

pub fn apply_captured_closure(x: u32, y: u32) -> u32 {
    let add_y = |v: u32| v + y;
    call_via_trait(&add_y, x)
}
"#;

/// Test simple closure call (no captured env) through codegen.
#[test]
fn test_mir_closure_simple() {
    with_probe_codegen(
        CLOSURE_PROBE,
        "apply_closure",
        |call_count, call_paths, _call_dest_assigned, _ret_expr| {
            assert!(call_count >= 1, "closure probe should retain at least one call terminator");
            assert!(
                call_paths.iter().any(|p| p.contains("call_via_trait")),
                "closure probe should resolve call_via_trait path, got {call_paths:?}"
            );
        },
    );
}

/// Test closure with captured environment through codegen.
#[test]
fn test_mir_closure_captured_env() {
    with_probe_codegen(
        CLOSURE_PROBE,
        "apply_captured_closure",
        |call_count, call_paths, _call_dest_assigned, _ret_expr| {
            assert!(
                call_count >= 1,
                "captured closure probe should retain at least one call terminator"
            );
            assert!(
                call_paths.iter().any(|p| p.contains("call_via_trait")),
                "captured closure probe should resolve call_via_trait path, got {call_paths:?}"
            );
        },
    );
}

// =============================================================================
// Dispatch helper prechecks (#2897)
// =============================================================================

const ABSTRACTED_FALLBACK_PROBE: &str = r#"
#[allow(non_snake_case)]
mod Utf8Chunk {
    #[inline(never)]
    pub fn next_chunk() -> u32 {
        7
    }
}

pub fn abstracted_fallback_probe() -> u32 {
    Utf8Chunk::next_chunk()
}
"#;

/// MIR-backed regression for `try_codegen_abstracted_fallback`.
#[test]
fn test_mir_try_codegen_abstracted_fallback_assigns_symbolic() {
    with_test_ay_ctx_for_source(ABSTRACTED_FALLBACK_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "abstracted_fallback_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }

        let mut observed_paths = Vec::new();
        let mut saw_expected_call = false;
        for bb in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, destination, target, .. } =
                &bb.terminator.kind
            else {
                continue;
            };
            let Some(callee_path) = codegen.resolve_callee_path(func) else {
                continue;
            };
            observed_paths.push(callee_path.clone());
            if !callee_path.contains("Utf8Chunk::next_chunk") {
                continue;
            }
            saw_expected_call = true;
            let handled = codegen.try_codegen_abstracted_fallback(func, destination, *target);
            assert_eq!(
                handled, *target,
                "abstracted fallback should handle Utf8Chunk path and continue to target"
            );
            let dest_base = codegen.ssa_base_name(destination);
            let assigned = codegen
                .env_lookup(&dest_base)
                .cloned()
                .expect("abstracted fallback should assign symbolic destination");
            assert!(
                matches!(assigned.value(), ExprValue::Var { .. }),
                "abstracted fallback should assign symbolic var, got {:?}",
                assigned.value()
            );
            break;
        }

        assert!(
            saw_expected_call,
            "expected Utf8Chunk::next_chunk call in MIR; observed paths: {observed_paths:?}"
        );
    });
}

const COW_TOSTRING_PRECHECK_PROBE: &str = r#"
use std::borrow::Cow;

pub fn cow_tostring_precheck_probe(input: &str) -> String {
    let cow: Cow<'_, str> = Cow::Borrowed(input);
    cow.to_string()
}
"#;

/// MIR-backed regression for `try_codegen_cow_tostring_precheck`.
#[test]
fn test_mir_try_codegen_cow_tostring_precheck_routes_to_string_stub() {
    with_test_ay_ctx_for_source(COW_TOSTRING_PRECHECK_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cow_tostring_precheck_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }

        let mut observed_paths = Vec::new();
        let mut saw_tostring_call = false;
        for bb in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &bb.terminator.kind
            else {
                continue;
            };
            let Some(callee_path) = codegen.resolve_callee_path(func) else {
                continue;
            };
            observed_paths.push(callee_path.clone());
            if !callee_path.contains("to_string") {
                continue;
            }
            saw_tostring_call = true;
            let handled = codegen.try_codegen_cow_tostring_precheck(
                func,
                &callee_path,
                args,
                destination,
                *target,
            );
            assert_eq!(
                handled,
                Some(*target),
                "Cow<str>::to_string precheck should handle to_string call via string stub"
            );
            let dest_base = codegen.ssa_base_name(destination);
            let assigned = codegen
                .env_lookup(&dest_base)
                .cloned()
                .expect("Cow precheck should assign destination through CowToString stub");
            let dest_ty = destination
                .ty(codegen.body.locals())
                .into_option()
                .expect("Cow precheck destination should have a type");
            assert!(
                format!("{dest_ty:?}").contains("String"),
                "Cow precheck destination should be String-like, got {dest_ty:?}"
            );
            if let Some(sort_name) = assigned.sort().datatype_name() {
                assert_eq!(
                    sort_name,
                    crate::codegen_ay::names::RUST_STRING_SORT,
                    "Cow precheck datatype assignment should use RustString sort"
                );
            }
            break;
        }

        assert!(
            saw_tostring_call,
            "expected to_string call in MIR; observed paths: {observed_paths:?}"
        );
    });
}

const EXTRACT_LAYOUT_FALLBACK_PROBE: &str = r#"
#[inline(never)]
fn nongeneric_call_target(x: u32) -> u32 {
    x + 1
}

pub fn layout_fallback_probe(x: u32) -> u32 {
    nongeneric_call_target(x)
}
"#;

/// MIR-backed regression for `extract_element_type_layout` fallback path.
#[test]
fn test_mir_extract_element_type_layout_nongeneric_falls_back_to_pointer_width() {
    with_test_ay_ctx_for_source(EXTRACT_LAYOUT_FALLBACK_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "layout_fallback_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let mut observed_paths = Vec::new();
        let mut saw_target_call = false;
        for bb in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
                continue;
            };
            let Some(callee_path) = codegen.resolve_callee_path(func) else {
                continue;
            };
            observed_paths.push(callee_path.clone());
            if !callee_path.contains("nongeneric_call_target") {
                continue;
            }
            saw_target_call = true;
            let (size, align) = codegen.extract_element_type_layout(func);
            assert_eq!((size, align), (8, 8), "nongeneric calls should use (8,8) fallback");
            break;
        }

        assert!(
            saw_target_call,
            "expected nongeneric_call_target call in MIR; observed paths: {observed_paths:?}"
        );
    });
}
