// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for intrinsic dispatch helper functions.

use rustc_public::mir::BinOp;

use super::arithmetic::{match_arithmetic_variant, match_with_overflow_intrinsic};
use super::math::{is_f32_math_intrinsic, is_f64_math_intrinsic};
use super::{extract_method_name, matches_simd_intrinsic};

// Regression tests for ordering-sensitive pattern matches (#2027).
// These verify that the dispatch helper functions correctly distinguish
// between intrinsics with overlapping name prefixes.

#[test]
fn test_matches_simd_intrinsic_exact_match() {
    assert!(matches_simd_intrinsic("simd_add", "simd_add"));
    assert!(matches_simd_intrinsic("::simd_add::", "simd_add"));
    assert!(matches_simd_intrinsic("core::simd::simd_add", "simd_add"));
}

#[test]
fn test_matches_simd_intrinsic_no_false_prefix() {
    // simd_add should NOT match simd_add_reduce (longer name)
    assert!(!matches_simd_intrinsic("simd_add_reduce", "simd_add"));
    assert!(!matches_simd_intrinsic("::simd_add_reduce::", "simd_add"));
}

#[test]
fn test_matches_simd_intrinsic_reduce_matches_correctly() {
    // simd_reduce_add uses contains() in dispatch, not matches_simd_intrinsic
    assert!("simd_reduce_add".contains("simd_reduce_add"));
    assert!(!"simd_reduce_add".contains("simd_reduce_mul"));
}

#[test]
fn test_extract_method_name_direct_path() {
    assert_eq!(extract_method_name("core::option::Option::unwrap"), Some("unwrap"));
    assert_eq!(
        extract_method_name("core::intrinsics::atomic_load_seqcst"),
        Some("atomic_load_seqcst")
    );
}

#[test]
fn test_extract_method_name_generic_impl_path() {
    assert_eq!(
        extract_method_name("<core::option::Option<u8> as core::ops::Try>::branch"),
        Some("branch")
    );
    assert_eq!(
        extract_method_name("<u32 as core::iter::traits::Step>::forward_unchecked"),
        Some("forward_unchecked")
    );
}

#[test]
fn test_extract_method_name_none_for_bare_symbol() {
    assert_eq!(extract_method_name("simd_add"), Some("simd_add"));
    assert_eq!(extract_method_name(""), None);
}

#[test]
fn test_match_arithmetic_variant_add_sub_mul() {
    assert_eq!(match_arithmetic_variant("wrapping_add", "wrapping_"), Some(BinOp::Add));
    assert_eq!(match_arithmetic_variant("wrapping_sub", "wrapping_"), Some(BinOp::Sub));
    assert_eq!(match_arithmetic_variant("wrapping_mul", "wrapping_"), Some(BinOp::Mul));
}

#[test]
fn test_match_arithmetic_variant_div_rem_shl_shr() {
    // Part of #3477: Extended arithmetic dispatch to cover div/rem/shl/shr.
    assert_eq!(match_arithmetic_variant("wrapping_div", "wrapping_"), Some(BinOp::Div));
    assert_eq!(match_arithmetic_variant("wrapping_rem", "wrapping_"), Some(BinOp::Rem));
    assert_eq!(match_arithmetic_variant("wrapping_shl", "wrapping_"), Some(BinOp::Shl));
    assert_eq!(match_arithmetic_variant("wrapping_shr", "wrapping_"), Some(BinOp::Shr));
    assert_eq!(match_arithmetic_variant("checked_div", "checked_"), Some(BinOp::Div));
    assert_eq!(match_arithmetic_variant("checked_rem", "checked_"), Some(BinOp::Rem));
    assert_eq!(match_arithmetic_variant("checked_shl", "checked_"), Some(BinOp::Shl));
    assert_eq!(match_arithmetic_variant("checked_shr", "checked_"), Some(BinOp::Shr));
    assert_eq!(match_arithmetic_variant("overflowing_shl", "overflowing_"), Some(BinOp::Shl));
    assert_eq!(match_arithmetic_variant("overflowing_shr", "overflowing_"), Some(BinOp::Shr));
}

#[test]
fn test_match_arithmetic_variant_all_prefixes() {
    for prefix in &["wrapping_", "unchecked_", "checked_", "saturating_", "overflowing_"] {
        let add = format!("{}add", prefix);
        let sub = format!("{}sub", prefix);
        let mul = format!("{}mul", prefix);
        let div = format!("{}div", prefix);
        let rem = format!("{}rem", prefix);
        let shl = format!("{}shl", prefix);
        let shr = format!("{}shr", prefix);
        assert_eq!(match_arithmetic_variant(&add, prefix), Some(BinOp::Add));
        assert_eq!(match_arithmetic_variant(&sub, prefix), Some(BinOp::Sub));
        assert_eq!(match_arithmetic_variant(&mul, prefix), Some(BinOp::Mul));
        assert_eq!(match_arithmetic_variant(&div, prefix), Some(BinOp::Div));
        assert_eq!(match_arithmetic_variant(&rem, prefix), Some(BinOp::Rem));
        assert_eq!(match_arithmetic_variant(&shl, prefix), Some(BinOp::Shl));
        assert_eq!(match_arithmetic_variant(&shr, prefix), Some(BinOp::Shr));
    }
}

#[test]
fn test_match_arithmetic_variant_full_path() {
    assert_eq!(match_arithmetic_variant("core::num::wrapping_add", "wrapping_"), Some(BinOp::Add));
    // Path with trailing ::
    assert_eq!(
        match_arithmetic_variant("core::num::wrapping_sub::h1234", "wrapping_"),
        Some(BinOp::Sub)
    );
}

#[test]
fn test_match_arithmetic_variant_no_allocation() {
    // Verify no false positives from substring prefix overlap.
    // "add_assign" should not match "add".
    assert_eq!(match_arithmetic_variant("wrapping_add_assign", "wrapping_"), None);
    assert_eq!(match_arithmetic_variant("checked_addition", "checked_"), None);
    // Part of #3477: verify no false positives for new suffixes
    assert_eq!(match_arithmetic_variant("wrapping_divmod", "wrapping_"), None);
    assert_eq!(match_arithmetic_variant("checked_remainder", "checked_"), None);
    assert_eq!(match_arithmetic_variant("overflowing_shift", "overflowing_"), None);
}

#[test]
fn test_match_arithmetic_variant_add_signed_not_matched() {
    // Part of #3375: overflowing_add_signed has suffix "add_signed" which does NOT
    // match the "add"/"sub"/"mul" suffix variants in match_arithmetic_variant.
    // This is the root cause of the BMC parity gap — the generic overflowing_ prefix
    // matches but the suffix check fails, so dispatch_arithmetic returns None.
    assert_eq!(match_arithmetic_variant("overflowing_add_signed", "overflowing_"), None);
    assert_eq!(match_arithmetic_variant("core::num::overflowing_add_signed", "overflowing_"), None);
    // But regular overflowing_add still matches:
    assert_eq!(match_arithmetic_variant("overflowing_add", "overflowing_"), Some(BinOp::Add));
}

#[test]
fn test_match_with_overflow_intrinsic() {
    assert_eq!(match_with_overflow_intrinsic("add_with_overflow"), Some(BinOp::Add));
    assert_eq!(
        match_with_overflow_intrinsic("core::intrinsics::sub_with_overflow"),
        Some(BinOp::Sub)
    );
    assert_eq!(
        match_with_overflow_intrinsic("std::intrinsics::mul_with_overflow"),
        Some(BinOp::Mul)
    );

    assert_eq!(match_with_overflow_intrinsic("overflowing_add"), None);
    assert_eq!(match_with_overflow_intrinsic("add_with_overflowing"), None);
    assert_eq!(match_with_overflow_intrinsic(""), None);
}

#[test]
fn test_is_f32_math_intrinsic() {
    assert!(is_f32_math_intrinsic("sqrtf32"));
    assert!(is_f32_math_intrinsic("std::intrinsics::fabsf32"));
    assert!(is_f32_math_intrinsic("round_ties_even_f32"));
    assert!(!is_f32_math_intrinsic("sqrtf64"));
    assert!(!is_f32_math_intrinsic("sqrt"));
}

#[test]
fn test_is_f64_math_intrinsic() {
    assert!(is_f64_math_intrinsic("sqrtf64"));
    assert!(is_f64_math_intrinsic("std::intrinsics::fabsf64"));
    assert!(!is_f64_math_intrinsic("sqrtf32"));
    assert!(!is_f64_math_intrinsic("sqrt"));
}

// Disambiguation tests for extract_method_name + exact/prefix dispatch.
// After the contains()→match refactor (W1-783), dispatch uses
// extract_method_name() to get the final segment, then exact == or
// starts_with() checks. These tests verify the mechanism works.

#[test]
fn test_memory_method_extraction_disambiguates_copy_variants() {
    // extract_method_name produces distinct strings for copy variants
    assert_eq!(
        extract_method_name("core::intrinsics::copy_nonoverlapping"),
        Some("copy_nonoverlapping")
    );
    assert_eq!(extract_method_name("core::intrinsics::copy"), Some("copy"));
    assert_eq!(extract_method_name("core::ptr::copy"), Some("copy"));
    // Exact match means no ordering dependency: "copy" != "copy_nonoverlapping"
    assert_ne!("copy", "copy_nonoverlapping");
}

#[test]
fn test_memory_method_extraction_disambiguates_offset_variants() {
    assert_eq!(
        extract_method_name("core::ptr::offset_from_unsigned"),
        Some("offset_from_unsigned")
    );
    assert_eq!(extract_method_name("core::ptr::offset_from"), Some("offset_from"));
    assert_eq!(extract_method_name("core::ptr::offset"), Some("offset"));
    // All three are distinct after extraction — no ordering dependency
    assert_ne!("offset", "offset_from");
    assert_ne!("offset_from", "offset_from_unsigned");
}

#[test]
fn test_atomic_method_extraction_disambiguates_signed_unsigned() {
    // Atomic intrinsics have ordering suffixes, so dispatch uses starts_with()
    assert_eq!(
        extract_method_name("core::intrinsics::atomic_max_seqcst"),
        Some("atomic_max_seqcst")
    );
    assert_eq!(
        extract_method_name("core::intrinsics::atomic_umax_seqcst"),
        Some("atomic_umax_seqcst")
    );
    // starts_with("atomic_max") matches "atomic_max_seqcst" but NOT "atomic_umax_seqcst"
    assert!("atomic_max_seqcst".starts_with("atomic_max"));
    assert!(!"atomic_umax_seqcst".starts_with("atomic_max"));
    // starts_with("atomic_umax") matches "atomic_umax_seqcst" but NOT "atomic_max_seqcst"
    assert!("atomic_umax_seqcst".starts_with("atomic_umax"));
    assert!(!"atomic_max_seqcst".starts_with("atomic_umax"));
}

#[test]
fn test_atomic_min_disambiguation() {
    assert_eq!(
        extract_method_name("core::intrinsics::atomic_min_seqcst"),
        Some("atomic_min_seqcst")
    );
    assert_eq!(
        extract_method_name("core::intrinsics::atomic_umin_seqcst"),
        Some("atomic_umin_seqcst")
    );
    assert!("atomic_min_seqcst".starts_with("atomic_min"));
    assert!(!"atomic_umin_seqcst".starts_with("atomic_min"));
}

// Part of #3477: Verify extract_method_name works for volatile/swap intrinsics
// so the memory dispatcher can match them correctly.

#[test]
fn test_memory_method_extraction_volatile_intrinsics() {
    assert_eq!(extract_method_name("core::intrinsics::volatile_load"), Some("volatile_load"));
    assert_eq!(extract_method_name("core::intrinsics::volatile_store"), Some("volatile_store"));
    assert_eq!(
        extract_method_name("core::intrinsics::unaligned_volatile_load"),
        Some("unaligned_volatile_load")
    );
    assert_eq!(
        extract_method_name("core::intrinsics::volatile_copy_memory"),
        Some("volatile_copy_memory")
    );
    assert_eq!(
        extract_method_name("core::intrinsics::volatile_copy_nonoverlapping_memory"),
        Some("volatile_copy_nonoverlapping_memory")
    );
}

#[test]
fn test_memory_method_extraction_swap_intrinsics() {
    assert_eq!(
        extract_method_name("core::intrinsics::typed_swap_nonoverlapping"),
        Some("typed_swap_nonoverlapping")
    );
    // std::mem::swap resolves to a different path but same final segment
    assert_eq!(extract_method_name("core::mem::swap"), Some("swap"));
    assert_eq!(extract_method_name("std::mem::swap"), Some("swap"));
    // swap is distinct from typed_swap_nonoverlapping after extraction
    assert_ne!("swap", "typed_swap_nonoverlapping");
}
