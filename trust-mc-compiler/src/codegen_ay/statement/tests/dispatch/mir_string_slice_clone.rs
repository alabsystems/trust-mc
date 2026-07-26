// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven String, slice, ZST parity, and collection clone dispatch tests.
//!
//! Split from dispatch.rs per #3678.

use super::super::*;
use super::{assert_semantic_return_equals, build_codegen_for_fn_info};

// Extended String dispatch: MIR-driven tests
// =============================================================================

/// Probe source: extended String operations beyond push+len.
const STRING_EXTENDED_DISPATCH_PROBE: &str = r#"
pub fn string_push_str_clear() -> usize {
    let mut s = String::new();
    s.push_str("hello");
    s.push_str(" world");
    let len_before = s.len();
    s.clear();
    len_before
}

pub fn string_from_clone() -> bool {
    let s = String::from("test");
    let t = s.clone();
    s == t
}

pub fn string_is_empty() -> bool {
    let s = String::new();
    s.is_empty()
}
"#;

/// Test String::push_str + clear dispatches through stub pipeline.
#[test]
fn test_mir_string_push_str_clear_dispatch() {
    with_test_ay_ctx_for_source(STRING_EXTENDED_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "string_push_str_clear");
        assert!(
            info.call_count >= 3,
            "String push_str+push_str+len+clear should have >=3 Calls, got {}",
            info.call_count
        );
        // Returns usize
        assert!(
            info.ret_bitvec_width.is_some(),
            "string_push_str_clear should return bitvec (usize), got {:?}",
            info.ret_bitvec_width
        );
    });
}

/// Test String::from + clone + PartialEq dispatches through stub pipeline.
#[test]
fn test_mir_string_from_clone_eq_dispatch() {
    with_test_ay_ctx_for_source(STRING_EXTENDED_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "string_from_clone");
        assert!(
            info.call_count >= 2,
            "String from+clone+eq should have >=2 Calls, got {}",
            info.call_count
        );
        assert!(info.ret_is_bool, "string_from_clone should return bool");
    });
}

/// Test String::is_empty dispatches through stub pipeline.
#[test]
fn test_mir_string_is_empty_dispatch() {
    with_test_ay_ctx_for_source(STRING_EXTENDED_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "string_is_empty");
        // is_empty may be inlined to len == 0
        assert!(
            info.call_count >= 1 || info.block_count >= 1,
            "String::is_empty should have calls or blocks, got calls={}, blocks={}",
            info.call_count,
            info.block_count
        );
        assert!(info.ret_is_bool, "string_is_empty should return bool");
    });
}

/// Critical semantic stub #5 (#2250): String::new().is_empty() must return true.
#[test]
fn test_mir_string_is_empty_semantic_true() {
    with_test_ay_ctx_for_source(STRING_EXTENDED_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "string_is_empty");
        let ret_expr = info.ret_expr.expect("string_is_empty should assign return local");
        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            Expr::bool_const(true),
            "string_is_empty_true",
        );
    });
}

// =============================================================================
// Slice dispatch: MIR-driven tests
// =============================================================================

/// Probe source: slice operations — triggers SlicePartialEqEqual and indexing.
const SLICE_DISPATCH_PROBE: &str = r#"
pub fn slice_eq(a: &[i32], b: &[i32]) -> bool {
    a == b
}

pub fn slice_index(s: &[i32]) -> i32 {
    s[0]
}

pub fn vec_as_slice_eq() -> bool {
    let a = vec![1i32, 2, 3];
    let b = vec![1i32, 2, 3];
    a.as_slice() == b.as_slice()
}
"#;

/// Probe source for #408 dispatch-layer parity coverage:
/// - zero-length non-ZST array (`[u8; 0]`)
/// - non-empty ZST array (`[(); 10]`)
/// - `first(&array)`, equality, and indexed access semantics.
const SLICE_ZST_PARITY_PROBE: &str = r#"
pub fn zero_len_non_zst_first_is_none() -> bool {
    let empty: [u8; 0] = [];
    empty.first().is_none()
}

pub fn non_empty_zst_first_is_some() -> bool {
    let zst: [(); 10] = [(); 10];
    zst.first().is_some()
}

pub fn non_empty_zst_eq_true() -> bool {
    let lhs: [(); 10] = [(); 10];
    let rhs: [(); 10] = [(); 10];
    lhs == rhs
}

pub fn non_empty_zst_index_eq_unit() -> bool {
    let zst: [(); 10] = [(); 10];
    zst[0] == ()
}
"#;

/// Test slice equality (PartialEq) dispatches through stub pipeline.
#[test]
fn test_mir_slice_eq_dispatch() {
    with_test_ay_ctx_for_source(SLICE_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "slice_eq");
        // PartialEq on slices involves length check + element comparison
        assert!(info.block_count >= 2, "slice_eq should have >=2 BBs, got {}", info.block_count);
        assert!(info.ret_is_bool, "slice_eq should return bool");
    });
}

/// Test slice indexing dispatches through stub pipeline.
#[test]
fn test_mir_slice_index_dispatch() {
    with_test_ay_ctx_for_source(SLICE_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "slice_index");
        // s[0] goes through Index trait
        assert!(
            info.call_count >= 1 || info.block_count >= 2,
            "slice_index should have calls or multiple BBs, got calls={}, blocks={}",
            info.call_count,
            info.block_count
        );
        assert_eq!(
            info.ret_bitvec_width,
            Some(32),
            "slice_index should return bv32, got {:?}",
            info.ret_bitvec_width
        );
    });
}

/// Test Vec::as_slice + slice eq dispatches through stub pipeline.
#[test]
fn test_mir_vec_as_slice_eq_dispatch() {
    with_test_ay_ctx_for_source(SLICE_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "vec_as_slice_eq");
        assert!(
            info.call_count >= 2,
            "vec_as_slice_eq should have >=2 Calls, got {}",
            info.call_count
        );
        assert!(info.ret_is_bool, "vec_as_slice_eq should return bool");
    });
}

#[test]
fn test_mir_zero_len_non_zst_first_is_none_dispatch() {
    with_test_ay_ctx_for_source(SLICE_ZST_PARITY_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "zero_len_non_zst_first_is_none");
        assert!(
            info.call_count >= 1 || info.block_count >= 1,
            "zero_len_non_zst_first_is_none should have calls or blocks, got calls={}, blocks={}",
            info.call_count,
            info.block_count
        );
        assert!(info.ret_is_bool, "zero_len_non_zst_first_is_none should return bool");
        assert!(
            info.ret_expr.is_some(),
            "zero_len_non_zst_first_is_none should assign return local"
        );
    });
}

#[test]
fn test_mir_non_empty_zst_first_is_some_dispatch() {
    with_test_ay_ctx_for_source(SLICE_ZST_PARITY_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "non_empty_zst_first_is_some");
        assert!(
            info.call_count >= 1 || info.block_count >= 1,
            "non_empty_zst_first_is_some should have calls or blocks, got calls={}, blocks={}",
            info.call_count,
            info.block_count
        );
        assert!(info.ret_is_bool, "non_empty_zst_first_is_some should return bool");
        assert!(info.ret_expr.is_some(), "non_empty_zst_first_is_some should assign return local");
    });
}

#[test]
fn test_mir_non_empty_zst_eq_semantic_true() {
    with_test_ay_ctx_for_source(SLICE_ZST_PARITY_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "non_empty_zst_eq_true");
        assert!(info.ret_is_bool, "non_empty_zst_eq_true should return bool");
        let ret_expr = info.ret_expr.expect("non_empty_zst_eq_true should assign return local");
        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            Expr::bool_const(true),
            "slice_non_empty_zst_eq_true",
        );
    });
}

#[test]
fn test_mir_non_empty_zst_index_eq_unit_semantic_true() {
    with_test_ay_ctx_for_source(SLICE_ZST_PARITY_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "non_empty_zst_index_eq_unit");
        assert!(info.ret_is_bool, "non_empty_zst_index_eq_unit should return bool");
        let ret_expr =
            info.ret_expr.expect("non_empty_zst_index_eq_unit should assign return local");
        assert_semantic_return_equals(
            &ctx,
            ret_expr,
            Expr::bool_const(true),
            "slice_non_empty_zst_index_eq_unit_true",
        );
    });
}

// =============================================================================
// Collection clone dispatch: MIR-driven tests
// =============================================================================

/// Probe source: collection clone operations — triggers VecClone, StringClone.
const COLLECTION_CLONE_DISPATCH_PROBE: &str = r#"
pub fn vec_clone_eq() -> bool {
    let v = vec![1i32, 2, 3];
    let w = v.clone();
    v.len() == w.len()
}

pub fn string_clone_eq() -> bool {
    let s = String::from("hello");
    let t = s.clone();
    s == t
}
"#;

/// Test Vec::clone dispatches through stub pipeline.
#[test]
fn test_mir_vec_clone_dispatch() {
    with_test_ay_ctx_for_source(COLLECTION_CLONE_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "vec_clone_eq");
        assert!(
            info.call_count >= 2,
            "Vec clone+len+len should have >=2 Calls, got {}",
            info.call_count
        );
        assert!(info.ret_is_bool, "vec_clone_eq should return bool");
    });
}

/// Test String::clone dispatches through stub pipeline.
#[test]
fn test_mir_string_clone_dispatch() {
    with_test_ay_ctx_for_source(COLLECTION_CLONE_DISPATCH_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "string_clone_eq");
        assert!(
            info.call_count >= 2,
            "String clone+eq should have >=2 Calls, got {}",
            info.call_count
        );
        assert!(info.ret_is_bool, "string_clone_eq should return bool");
    });
}
