// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven arithmetic intrinsic dispatch tests: wrapping, checked,
//! saturating, overflowing arithmetic.
//!
//! Split from dispatch.rs per #3678.

use super::super::*;
use super::build_codegen_for_fn_info;

// =============================================================================

/// Probe source for arithmetic intrinsics dispatched via try_codegen_std_intrinsic.
/// These trigger dispatch_arithmetic for wrapping, checked, saturating, and
/// overflowing variants.
const ARITH_DISPATCH_PROBE: &str = r#"
pub fn wrapping_add_probe(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

pub fn wrapping_sub_probe(a: u32, b: u32) -> u32 {
    a.wrapping_sub(b)
}

pub fn wrapping_mul_probe(a: u32, b: u32) -> u32 {
    a.wrapping_mul(b)
}

pub fn checked_add_probe(a: u32, b: u32) -> Option<u32> {
    a.checked_add(b)
}

pub fn checked_sub_probe(a: u32, b: u32) -> Option<u32> {
    a.checked_sub(b)
}

pub fn saturating_add_probe(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}

pub fn overflowing_add_probe(a: u32, b: u32) -> (u32, bool) {
    a.overflowing_add(b)
}

pub fn overflowing_mul_probe(a: u64, b: u64) -> (u64, bool) {
    a.overflowing_mul(b)
}

pub fn signed_wrapping_add_probe(a: i32, b: i32) -> i32 {
    a.wrapping_add(b)
}

pub fn signed_saturating_sub_probe(a: i32, b: i32) -> i32 {
    a.saturating_sub(b)
}
"#;

/// Test wrapping_add dispatches through the arithmetic intrinsic pipeline.
#[test]
fn test_mir_wrapping_add_dispatch() {
    with_test_ay_ctx_for_source(ARITH_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "wrapping_add_probe");
        assert!(info.call_count >= 1, "wrapping_add should have Call, got {}", info.call_count);
        // wrapping_add(u32, u32) -> u32: return should be 32-bit bitvec
        assert_eq!(info.ret_bitvec_width, Some(32), "wrapping_add(u32) should return 32-bit");
        assert!(info.any_dest_assigned, "wrapping_add should assign call destination");
    });
}

/// Test wrapping_sub dispatches through the arithmetic intrinsic pipeline.
#[test]
fn test_mir_wrapping_sub_dispatch() {
    with_test_ay_ctx_for_source(ARITH_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "wrapping_sub_probe");
        assert!(info.call_count >= 1, "wrapping_sub should have Call, got {}", info.call_count);
        assert_eq!(info.ret_bitvec_width, Some(32), "wrapping_sub(u32) should return 32-bit");
        assert!(info.any_dest_assigned, "wrapping_sub should assign call destination");
    });
}

/// Test wrapping_mul dispatches through the arithmetic intrinsic pipeline.
#[test]
fn test_mir_wrapping_mul_dispatch() {
    with_test_ay_ctx_for_source(ARITH_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "wrapping_mul_probe");
        assert!(info.call_count >= 1, "wrapping_mul should have Call, got {}", info.call_count);
        assert_eq!(info.ret_bitvec_width, Some(32), "wrapping_mul(u32) should return 32-bit");
        assert!(info.any_dest_assigned, "wrapping_mul should assign call destination");
    });
}

/// Test checked_add dispatches through the arithmetic intrinsic pipeline.
/// Returns Option<u32>, exercising both the dispatch path and Option packing.
#[test]
fn test_mir_checked_add_dispatch() {
    with_test_ay_ctx_for_source(ARITH_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "checked_add_probe");
        assert!(info.call_count >= 1, "checked_add should have Call, got {}", info.call_count);
        // checked_add returns Option<u32> (datatype, not flat bitvec) — verify routing
        assert!(
            info.call_paths.iter().any(|p| p.contains("checked_add")),
            "expected checked_add in call paths, got {:?}",
            info.call_paths
        );
    });
}

/// Test checked_sub dispatches through the arithmetic intrinsic pipeline.
/// Returns Option<u32> — verify dispatch routing to checked_sub method.
#[test]
fn test_mir_checked_sub_dispatch() {
    with_test_ay_ctx_for_source(ARITH_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "checked_sub_probe");
        assert!(info.call_count >= 1, "checked_sub should have Call, got {}", info.call_count);
        assert!(
            info.call_paths.iter().any(|p| p.contains("checked_sub")),
            "expected checked_sub in call paths, got {:?}",
            info.call_paths
        );
    });
}

/// Test saturating_add dispatches through the arithmetic intrinsic pipeline.
#[test]
fn test_mir_saturating_add_dispatch() {
    with_test_ay_ctx_for_source(ARITH_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "saturating_add_probe");
        assert!(info.call_count >= 1, "saturating_add should have Call, got {}", info.call_count);
        assert_eq!(info.ret_bitvec_width, Some(32), "saturating_add(u32) should return 32-bit");
        assert!(info.any_dest_assigned, "saturating_add should assign call destination");
    });
}

/// Test overflowing_add dispatches — returns (u32, bool) tuple, exercises
/// both dispatch_arithmetic and tuple packing in the codegen.
#[test]
fn test_mir_overflowing_add_dispatch() {
    with_test_ay_ctx_for_source(ARITH_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "overflowing_add_probe");
        assert!(info.call_count >= 1, "overflowing_add should have Call, got {}", info.call_count);
        // Returns (u32, bool) — compound type, verify routing
        assert!(
            info.call_paths.iter().any(|p| p.contains("overflowing_add")),
            "expected overflowing_add in call paths, got {:?}",
            info.call_paths
        );
    });
}

/// Test overflowing_mul dispatches with wider type (u64) to exercise
/// different bitvec widths through the arithmetic pipeline.
#[test]
fn test_mir_overflowing_mul_u64_dispatch() {
    with_test_ay_ctx_for_source(ARITH_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "overflowing_mul_probe");
        assert!(info.call_count >= 1, "overflowing_mul should have Call, got {}", info.call_count);
        // Returns (u64, bool) — compound type, verify routing
        assert!(
            info.call_paths.iter().any(|p| p.contains("overflowing_mul")),
            "expected overflowing_mul in call paths, got {:?}",
            info.call_paths
        );
    });
}

/// Test signed wrapping_add dispatches (exercises signed operand path).
#[test]
fn test_mir_signed_wrapping_add_dispatch() {
    with_test_ay_ctx_for_source(ARITH_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "signed_wrapping_add_probe");
        assert!(
            info.call_count >= 1,
            "signed wrapping_add should have Call, got {}",
            info.call_count
        );
        assert_eq!(
            info.ret_bitvec_width,
            Some(32),
            "signed wrapping_add(i32) should return 32-bit"
        );
        assert!(info.any_dest_assigned, "signed wrapping_add should assign call destination");
    });
}

/// Test signed saturating_sub dispatches (exercises signed saturating path).
#[test]
fn test_mir_signed_saturating_sub_dispatch() {
    with_test_ay_ctx_for_source(ARITH_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "signed_saturating_sub_probe");
        assert!(
            info.call_count >= 1,
            "signed saturating_sub should have Call, got {}",
            info.call_count
        );
        assert_eq!(
            info.ret_bitvec_width,
            Some(32),
            "signed saturating_sub(i32) should return 32-bit"
        );
        assert!(info.any_dest_assigned, "signed saturating_sub should assign call destination");
    });
}

// =============================================================================
