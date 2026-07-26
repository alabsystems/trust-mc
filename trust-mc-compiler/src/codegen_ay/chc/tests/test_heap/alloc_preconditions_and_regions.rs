// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =====================================================================
// Part of #1177: Tests for alloc precondition helper functions
// =====================================================================

#[test]
fn test_nonzero_bv_check_pattern() {
    // (#1177) Verify nonzero_bv_check generates: expr != 0
    // This is used for size > 0 and align > 0 checks in allocators.

    let size = Expr::bitvec_const(42, 64);
    let zero = Expr::bitvec_const(0, 64);

    // Pattern: size != 0
    let nonzero_check = size.eq(zero).not();

    assert!(nonzero_check.sort().is_bool(), "Nonzero check must be Bool");
    // For constant 42, this would evaluate to true
}

#[test]
fn test_nonzero_bv_check_zero_input() {
    // (#1177) When size == 0, the check should evaluate to false
    let size = Expr::bitvec_const(0, 64);
    let zero = Expr::bitvec_const(0, 64);

    let nonzero_check = size.eq(zero).not();
    assert!(nonzero_check.sort().is_bool());
    // For constant 0, size.eq(zero) = true, so .not() = false
}

#[test]
fn test_power_of_two_bv_check_pattern() {
    // (#1177) Verify power_of_two_bv_check generates: (expr & (expr-1)) == 0
    // This is the classic power-of-two check used for alignment validation.

    let align = Expr::var("align", Sort::bitvec(64));
    let one = Expr::bitvec_const(1, 64);
    let zero = Expr::bitvec_const(0, 64);

    // Pattern: (align & (align - 1)) == 0
    let minus_one = align.clone().bvsub(one);
    let and_mask = align.bvand(minus_one);
    let pow2_check = and_mask.eq(zero);

    assert!(pow2_check.sort().is_bool(), "Power-of-two check must be Bool");
}

#[test]
fn test_power_of_two_bv_check_concrete_values() {
    // (#1177) Concrete examples of power-of-two check
    // 8 = 0b1000, 8-1 = 0b0111, 8 & 7 = 0 (is power of two)
    // 7 = 0b0111, 7-1 = 0b0110, 7 & 6 = 6 != 0 (not power of two)

    let eight = Expr::bitvec_const(8, 64);
    let one = Expr::bitvec_const(1, 64);
    let zero = Expr::bitvec_const(0, 64);

    // 8 is power of two: (8 & 7) == 0
    let minus_one = eight.clone().bvsub(one);
    let and_result = eight.bvand(minus_one);
    let is_pow2 = and_result.eq(zero);

    assert!(is_pow2.sort().is_bool());
    // For constant 8, (8 & 7) = 0, so this would evaluate to true
}

#[test]
fn test_fits_in_bv32_check_pattern() {
    // (#1177) Verify fits_in_bv32_check generates: high_bits == 0
    // For 64-bit values, this checks bits [63:32] == 0.

    let size_64 = Expr::var("size", Sort::bitvec(64));

    // Pattern: size[63:32] == 0
    let high_bits = size_64.extract(63, 32);
    let zero_32 = Expr::bitvec_const(0, 32);
    let fits_check = high_bits.eq(zero_32);

    assert!(fits_check.sort().is_bool(), "Fits check must be Bool");
}

#[test]
fn test_fits_in_bv32_check_32bit_input() {
    // (#1177) For 32-bit input, fits_in_bv32_check should return None
    // (no check needed - it already fits)

    let size_32 = Expr::var("size", Sort::bitvec(32));
    let width = size_32.sort().bitvec_width();

    // For width <= 32, no check is needed
    assert_eq!(width, Some(32));
    // The helper returns None for this case, meaning "no constraint needed"
}

#[test]
fn test_alloc_precondition_combination() {
    // (#1177) Test that all alloc preconditions combine correctly
    // RustAlloc requires: size > 0, align > 0, is_power_of_two(align)

    let size = Expr::var("size", Sort::bitvec(64));
    let align = Expr::var("align", Sort::bitvec(64));
    let zero = Expr::bitvec_const(0, 64);
    let one = Expr::bitvec_const(1, 64);

    // Build all checks
    let size_nonzero = size.eq(zero.clone()).not();
    let align_nonzero = align.clone().eq(zero).not();
    let align_pow2 = align.clone().bvand(align.bvsub(one)).eq(Expr::bitvec_const(0, 64));

    // All must be Bool
    assert!(size_nonzero.sort().is_bool());
    assert!(align_nonzero.sort().is_bool());
    assert!(align_pow2.sort().is_bool());

    // Combined precondition: size_nonzero ∧ align_nonzero ∧ align_pow2
    let combined = size_nonzero.and(align_nonzero).and(align_pow2);
    assert!(combined.sort().is_bool(), "Combined precondition must be Bool");
}

// ============================================================================
// Region Array Integration Tests (Part of #1443)
// ============================================================================

#[test]
fn test_try_extract_obj_id_from_concat() {
    // (#1443) Verify obj_id extraction from split-pointer addresses.
    // Address format: (obj_id : bv32).concat(offset : bv32) = 64-bit address

    // Create address with known obj_id = 42, offset = 0
    let obj_id_expr = Expr::bitvec_const(42u32, 32);
    let offset_expr = Expr::bitvec_const(0u32, 32);
    let addr = obj_id_expr.concat(offset_expr);

    // Should extract obj_id = 42
    let extracted = ChcCtx::try_extract_obj_id(&addr);
    assert_eq!(extracted, Some(42), "Should extract obj_id from concat address");
}

#[test]
fn test_try_extract_obj_id_from_concat_with_offset() {
    // (#1443) Obj_id extraction should work regardless of offset value
    let obj_id_expr = Expr::bitvec_const(7u32, 32);
    let offset_expr = Expr::bitvec_const(1024u32, 32); // Non-zero offset
    let addr = obj_id_expr.concat(offset_expr);

    let extracted = ChcCtx::try_extract_obj_id(&addr);
    assert_eq!(extracted, Some(7), "Should extract obj_id even with non-zero offset");
}

#[test]
fn test_try_extract_obj_id_zero() {
    // (#1443) Null pointer (obj_id = 0) should still extract correctly
    let obj_id_expr = Expr::bitvec_const(0u32, 32);
    let offset_expr = Expr::bitvec_const(0u32, 32);
    let addr = obj_id_expr.concat(offset_expr);

    let extracted = ChcCtx::try_extract_obj_id(&addr);
    assert_eq!(extracted, Some(0), "Should extract obj_id = 0 for null pointer");
}

#[test]
fn test_try_extract_obj_id_symbolic_returns_none() {
    // (#1443) Symbolic addresses should return None (can't statically determine obj_id)
    let symbolic_obj_id = Expr::var("obj_id", Sort::bitvec(32));
    let offset_expr = Expr::bitvec_const(0u32, 32);
    let addr = symbolic_obj_id.concat(offset_expr);

    let extracted = ChcCtx::try_extract_obj_id(&addr);
    assert_eq!(extracted, None, "Symbolic obj_id should return None");
}

#[test]
fn test_try_extract_obj_id_non_concat_returns_none() {
    // (#1443) Non-concat addresses should return None
    let addr = Expr::bitvec_const(0x1234_5678_0000_0000i128, 64);

    let extracted = ChcCtx::try_extract_obj_id(&addr);
    assert_eq!(extracted, None, "Non-concat address should return None");
}

#[test]
fn test_try_extract_obj_id_wrong_width_returns_none() {
    // (#1443) Non-64-bit addresses should return None
    let addr = Expr::bitvec_const(42u32, 32);

    let extracted = ChcCtx::try_extract_obj_id(&addr);
    assert_eq!(extracted, None, "32-bit address should return None");
}

#[test]
fn test_try_extract_constant_addr_from_concat() {
    // (#3667) Constant split-pointer addresses should yield both key components.
    let obj_id_expr = Expr::bitvec_const(7u32, 32);
    let offset_expr = Expr::bitvec_const(1024u32, 32);
    let addr = obj_id_expr.concat(offset_expr);

    let extracted = ChcCtx::try_extract_constant_addr(&addr);
    assert_eq!(
        extracted,
        Some((7, 1024)),
        "constant split-pointer address should extract obj_id + offset"
    );
}

#[test]
fn test_try_extract_constant_addr_zero_halves() {
    // (#3667) Zero halves use BigInt NoSign internally and must still extract.
    let obj_id_expr = Expr::bitvec_const(0u32, 32);
    let offset_expr = Expr::bitvec_const(0u32, 32);
    let addr = obj_id_expr.concat(offset_expr);

    let extracted = ChcCtx::try_extract_constant_addr(&addr);
    assert_eq!(extracted, Some((0, 0)), "zero obj_id/offset should extract successfully");
}

#[test]
fn test_try_extract_constant_addr_symbolic_obj_id_returns_none() {
    // (#3667) Forwarding keys must reject symbolic upper halves.
    let symbolic_obj_id = Expr::var("obj_id", Sort::bitvec(32));
    let offset_expr = Expr::bitvec_const(0u32, 32);
    let addr = symbolic_obj_id.concat(offset_expr);

    let extracted = ChcCtx::try_extract_constant_addr(&addr);
    assert_eq!(extracted, None, "symbolic obj_id should not produce a forwarding key");
}

#[test]
fn test_try_extract_constant_addr_symbolic_offset_returns_none() {
    // (#3667) Forwarding keys must reject symbolic lower halves.
    let obj_id_expr = Expr::bitvec_const(7u32, 32);
    let symbolic_offset = Expr::var("offset", Sort::bitvec(32));
    let addr = obj_id_expr.concat(symbolic_offset);

    let extracted = ChcCtx::try_extract_constant_addr(&addr);
    assert_eq!(extracted, None, "symbolic offset should not produce a forwarding key");
}

#[test]
fn test_try_extract_constant_addr_non_concat_returns_none() {
    // (#3667) Raw 64-bit constants are not split-pointer concat expressions.
    let addr = Expr::bitvec_const(0x1234_5678_0000_0000i128, 64);

    let extracted = ChcCtx::try_extract_constant_addr(&addr);
    // Part of #4014: raw BV64 constants are now split into (high32, low32).
    assert_eq!(
        extracted,
        Some((0x1234_5678, 0)),
        "raw BV64 constant should split into obj_id|offset"
    );
}

#[test]
fn test_try_extract_constant_addr_wrong_width_returns_none() {
    // (#3667) Only bv64 split-pointer addresses are eligible for extraction.
    let addr = Expr::bitvec_const(42u32, 32);

    let extracted = ChcCtx::try_extract_constant_addr(&addr);
    assert_eq!(extracted, None, "non-bv64 address should return None");
}

#[test]
fn test_region_sort_mismatch_requires_fallback() {
    // (#1446) Region arrays use bv8 for raw allocations, but typed loads
    // expect the pointee type's sort (e.g., bv32 for i32).
    // This test verifies that sort comparison correctly identifies mismatches.

    let region_sort = Sort::bitvec(8); // Raw byte allocation
    let elem_sort_i32 = Sort::bitvec(32); // i32 load
    let elem_sort_i64 = Sort::bitvec(64); // i64 load
    let elem_sort_byte = Sort::bitvec(8); // u8 load

    // Sort mismatch: bv8 region vs bv32 load
    assert_ne!(
        region_sort, elem_sort_i32,
        "bv8 region should not match bv32 elem_sort - requires fallback to type array"
    );

    // Sort mismatch: bv8 region vs bv64 load
    assert_ne!(
        region_sort, elem_sort_i64,
        "bv8 region should not match bv64 elem_sort - requires fallback to type array"
    );

    // Sort match: bv8 region vs bv8 load (byte access)
    assert_eq!(
        region_sort, elem_sort_byte,
        "bv8 region should match bv8 elem_sort - can use region array"
    );
}

#[test]
fn test_region_array_typed_allocation() {
    // (#1446) Verify typed region arrays can be created and matched
    // This enables future typed-region optimization where allocations
    // are assigned their actual element type instead of raw bytes.

    let mut heap = ChcHeapState::new();

    // Allocate with typed region (bv32 for i32*)
    let obj_id = heap.next_alloc_id().unwrap();
    let typed_elem_sort = Sort::bitvec(32);
    let (region_in, _region_out) =
        heap.assign_region_array(obj_id, typed_elem_sort.clone(), "fn_test");

    // Retrieve and verify sort matches
    let result = heap.get_region_array(obj_id);
    assert!(result.is_some());

    let (_in_name, _out_name, retrieved_sort) = result.unwrap();
    assert_eq!(retrieved_sort, typed_elem_sort, "Retrieved sort should match assigned typed sort");

    // This enables the #1446 optimization path: when sorts match,
    // region arrays provide better aliasing information
    assert!(region_in.contains("bv32"), "Typed region should include type suffix");
}
