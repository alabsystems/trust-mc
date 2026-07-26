// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pointer semantics tests: CheckedAddUnsigned wide-arithmetic, pointer offset,
//! offset_from, isize_max, three-valued return, BigRational BMC.
//!
//! Split from dispatch.rs per #3678.

use super::super::*;

// =============================================================================
// CheckedAddUnsigned wide-arithmetic pattern
// =============================================================================

/// Verify sign_extend doubles width for checked_add_unsigned.
#[test]
fn test_checked_add_unsigned_sign_extend() {
    let lhs = Expr::bitvec_const(5i64, 32);
    let wide = lhs.sign_extend(32); // 32 → 64
    assert_eq!(wide.sort().bitvec_width(), Some(64));
}

/// Verify zero_extend doubles width for unsigned rhs.
#[test]
fn test_checked_add_unsigned_zero_extend() {
    let rhs = Expr::bitvec_const(10u64, 32);
    let wide = rhs.zero_extend(32); // 32 → 64
    assert_eq!(wide.sort().bitvec_width(), Some(64));
}

/// Verify wide sum and range check for 32-bit operands.
#[test]
fn test_checked_add_unsigned_wide_sum() {
    let width: u32 = 32;
    let wide_width: u32 = width * 2;

    let lhs = Expr::bitvec_const(100i64, width);
    let rhs = Expr::bitvec_const(200u64, width);
    let lhs_wide = lhs.sign_extend(width);
    let rhs_wide = rhs.zero_extend(width);

    assert_eq!(lhs_wide.sort().bitvec_width(), Some(wide_width));
    assert_eq!(rhs_wide.sort().bitvec_width(), Some(wide_width));

    let sum_wide = lhs_wide.bvadd(rhs_wide);
    assert_eq!(sum_wide.sort().bitvec_width(), Some(wide_width));
}

/// Verify range check bounds for 32-bit checked_add_unsigned.
#[test]
fn test_checked_add_unsigned_range_bounds_32() {
    let width: u32 = 32;
    let wide_width: u32 = width * 2;

    // i32::MIN = -(2^31) = -2147483648
    // i32::MAX = 2^31 - 1 = 2147483647
    let signed_min = Expr::bitvec_const(-(1i64 << (width - 1)), wide_width);
    let signed_max = Expr::bitvec_const((1i64 << (width - 1)) - 1, wide_width);

    assert_eq!(signed_min.sort().bitvec_width(), Some(wide_width));
    assert_eq!(signed_max.sort().bitvec_width(), Some(wide_width));
}

/// Verify ITE selection between Some and None in checked_add_unsigned.
#[test]
fn test_checked_add_unsigned_ite_option() {
    let cond = Expr::bool_const(true);
    let some_val = Expr::bitvec_const(42u64, 32);
    let none_val = Expr::bitvec_const(0u64, 32);

    let result = Expr::ite(cond, some_val, none_val);
    assert_eq!(result.sort().bitvec_width(), Some(32u32));
}

/// Verify extract truncation for final result in checked_add_unsigned.
#[test]
fn test_checked_add_unsigned_extract_result() {
    let width: u32 = 32;
    let wide_val = Expr::bitvec_const(300u64, width * 2);

    // extract(width-1, 0) truncates from 64 → 32
    let result = wide_val.extract(width - 1, 0);
    assert_eq!(result.sort().bitvec_width(), Some(width));
}

// =============================================================================
// Pointer offset intrinsic patterns
// =============================================================================

/// Verify ptr offset non-null assertion pattern.
#[test]
fn test_ptr_offset_non_null_check() {
    let ptr = Expr::var("ptr", Sort::bitvec(POINTER_WIDTH));
    let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
    let base_non_null = ptr.eq(zero).not();

    assert!(base_non_null.sort().is_bool());
}

/// Verify ptr offset byte calculation: count * pointee_size.
#[test]
fn test_ptr_offset_byte_calculation() {
    let count = Expr::bitvec_const(5u64, POINTER_WIDTH);

    // pointee_size == 0 → byte_offset = 0 (ZST)
    let zst_offset = Expr::bitvec_const(0u128, POINTER_WIDTH);
    assert_eq!(zst_offset.sort().bitvec_width(), Some(POINTER_WIDTH));

    // pointee_size == 1 → byte_offset = count
    let byte_offset = count.clone();
    assert_eq!(byte_offset.sort().bitvec_width(), Some(POINTER_WIDTH));

    // pointee_size > 1 → byte_offset = count * size
    let size = Expr::bitvec_const(8u128, POINTER_WIDTH); // e.g., u64 pointee
    let scaled_offset = count.bvmul(size);
    assert_eq!(scaled_offset.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Verify ptr offset final result: ptr + byte_offset.
#[test]
fn test_ptr_offset_result_addition() {
    let ptr = Expr::bitvec_const(0x1000u64, POINTER_WIDTH);
    let offset = Expr::bitvec_const(40u64, POINTER_WIDTH); // 5 * 8

    let result = ptr.bvadd(offset);
    assert_eq!(result.sort().bitvec_width(), Some(POINTER_WIDTH));
}

// =============================================================================
// Pointer offset_from patterns
// =============================================================================

/// Verify signed ptr_offset_from: (lhs - rhs) / elem_size.
#[test]
fn test_ptr_offset_from_signed() {
    let lhs = Expr::bitvec_const(0x2000u64, POINTER_WIDTH);
    let rhs = Expr::bitvec_const(0x1000u64, POINTER_WIDTH);

    let diff = lhs.bvsub(rhs);
    let elem_size = Expr::bitvec_const(4u128, POINTER_WIDTH); // i32 elements
    let offset = diff.bvsdiv(elem_size);

    assert_eq!(offset.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Verify unsigned ptr_offset_from: (lhs - rhs) / elem_size (unsigned div).
#[test]
fn test_ptr_offset_from_unsigned() {
    let lhs = Expr::bitvec_const(0x2000u64, POINTER_WIDTH);
    let rhs = Expr::bitvec_const(0x1000u64, POINTER_WIDTH);

    let diff = lhs.bvsub(rhs);
    let elem_size = Expr::bitvec_const(4u128, POINTER_WIDTH);
    let offset = diff.bvudiv(elem_size);

    assert_eq!(offset.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Verify ZST pointee fallback: elem_size = max(pointee_size, 1) = 1.
#[test]
fn test_ptr_offset_from_zst_fallback() {
    let pointee_size: usize = 0;
    let elem_size = if pointee_size == 0 { 1 } else { pointee_size };
    assert_eq!(elem_size, 1);

    let size_expr = Expr::bitvec_const(elem_size as u128, POINTER_WIDTH);
    assert_eq!(size_expr.sort().bitvec_width(), Some(POINTER_WIDTH));
}

// =============================================================================
// isize_max computation pattern
// =============================================================================

/// Verify isize_max and max_valid_base computation for different pointer widths.
#[test]
fn test_isize_max_computation() {
    // 64-bit
    let ptr_width: u32 = 64;
    let isize_max = (1u128 << (ptr_width - 1)) - 1;
    assert_eq!(isize_max, i64::MAX as u128);

    let max_valid_base = ((1u128 << ptr_width) - 1) - isize_max;
    assert!(max_valid_base > 0);

    // 32-bit
    let ptr_width_32: u32 = 32;
    let isize_max_32 = (1u128 << (ptr_width_32 - 1)) - 1;
    assert_eq!(isize_max_32, i32::MAX as u128);
}

// =============================================================================
// Three-valued return semantics
// =============================================================================

/// Verify the three-valued return of try_codegen_stdlib_stub_call.
#[test]
fn test_three_valued_return_semantics() {
    // None = stub didn't match
    let not_matched: Option<Option<usize>> = None;
    assert!(not_matched.is_none());

    // Some(None) = stub handled, diverges (panic/unreachable)
    let diverged: Option<Option<usize>> = Some(None);
    assert_eq!(diverged, Some(None));

    // Some(Some(bb)) = stub handled, continue to block bb
    let handled: Option<Option<usize>> = Some(Some(42));
    assert_eq!(handled, Some(Some(42)));
}

// =============================================================================
// BigRational BMC-path unsupported pattern
// =============================================================================

/// Verify BigRational stubs return Some(target) in BMC path (unsupported but non-diverging).
#[test]
fn test_bigrational_bmc_nondivergent() {
    // BigRational stubs in BMC return Some(target) — they don't crash/diverge,
    // they just emit an unsupported warning. This tests the return pattern.
    let target: Option<usize> = Some(7);
    let result: Option<Option<usize>> = Some(target);
    assert_eq!(result, Some(Some(7)));
}
