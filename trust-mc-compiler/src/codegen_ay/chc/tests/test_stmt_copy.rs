// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_stmt_copy.rs — CopyNonOverlapping intrinsic encoding,
//! Bool-to-bitvec coercion, expression coercion to target sorts, and copy index
//! guard construction.
//!
//! Part of #2231 (zero test coverage for codegen_stmt_copy.rs, 321 LOC).

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// coerce_bool_to_bitvec_assignment (static method, pure logic)
// =============================================================================

#[test]
fn test_coerce_bool_to_bitvec_assignment_bool_to_bv8() {
    let bool_expr = Expr::bool_const(true);
    let target = Sort::bitvec(8);

    let result = ChcCtx::coerce_bool_to_bitvec_assignment(bool_expr, &target);
    assert!(result.is_some(), "Bool to bv8 coercion should succeed");

    let expr = result.unwrap();
    // Should be ite(true, bv8(1), bv8(0))
    assert!(expr.sort().is_bitvec(), "Result should be bitvec");
    assert_eq!(expr.sort().bitvec_width(), Some(8), "Result should be 8-bit bitvec");
}

#[test]
fn test_coerce_bool_to_bitvec_assignment_bool_to_bv32() {
    let bool_expr = Expr::var("flag", Sort::bool());
    let target = Sort::bitvec(32);

    let result = ChcCtx::coerce_bool_to_bitvec_assignment(bool_expr, &target);
    assert!(result.is_some(), "Bool to bv32 coercion should succeed");

    let expr = result.unwrap();
    assert_eq!(expr.sort().bitvec_width(), Some(32), "Result should be 32-bit bitvec");
}

#[test]
fn test_coerce_bool_to_bitvec_assignment_non_bool_returns_none() {
    let bv_expr = Expr::bitvec_const(42, 32);
    let target = Sort::bitvec(32);

    let result = ChcCtx::coerce_bool_to_bitvec_assignment(bv_expr, &target);
    assert!(result.is_none(), "Non-bool input should return None");
}

#[test]
fn test_coerce_bool_to_bitvec_assignment_bool_to_non_bv_returns_none() {
    let bool_expr = Expr::bool_const(true);
    let target = Sort::bool();

    let result = ChcCtx::coerce_bool_to_bitvec_assignment(bool_expr, &target);
    assert!(result.is_none(), "Bool to Bool target should return None (not a bitvec target)");
}

#[test]
fn test_coerce_bool_to_bitvec_assignment_bool_to_bv1() {
    let bool_expr = Expr::bool_const(false);
    let target = Sort::bitvec(1);

    let result = ChcCtx::coerce_bool_to_bitvec_assignment(bool_expr, &target);
    assert!(result.is_some(), "Bool to bv1 coercion should succeed");

    let expr = result.unwrap();
    assert_eq!(expr.sort().bitvec_width(), Some(1), "Result should be 1-bit bitvec");
}

#[test]
fn test_coerce_assignment_rhs_to_sort_single_field_datatype_unwraps() {
    let tuple_sort = struct_sort("Tuple_bv32", [("fld_0", Sort::bitvec(32))]);
    let wrapped = Expr::var("_wrapped", tuple_sort);

    let result =
        ChcCtx::coerce_assignment_rhs_to_sort(wrapped.clone(), &Sort::bitvec(32), Some(false));
    assert!(result.is_some(), "single-field datatype rhs should coerce in assignment path");

    let expected = wrapped.field_select("Tuple_bv32", "fld_0", Sort::bitvec(32));
    assert_eq!(
        result.unwrap(),
        expected,
        "assignment coercion should unwrap tuple-like datatype to inner field"
    );
}

#[test]
fn test_coerce_assignment_rhs_to_sort_int_to_bitvec() {
    let int_expr = Expr::int_const(7);
    let target = Sort::bitvec(32);

    let result = ChcCtx::coerce_assignment_rhs_to_sort(int_expr, &target, Some(false));
    assert!(result.is_some(), "Int to BitVec assignment coercion should succeed");
    assert_eq!(
        result.unwrap().sort().bitvec_width(),
        Some(32),
        "coerced Int expression should match destination BitVec width"
    );
}

#[test]
fn test_coerce_assignment_rhs_to_sort_bitvec_to_int_unsigned() {
    let bv_expr = Expr::bitvec_const(7u64, 32);
    let target = Sort::int();

    let result = ChcCtx::coerce_assignment_rhs_to_sort(bv_expr, &target, Some(false));
    assert!(result.is_some(), "BitVec to Int assignment coercion should succeed");
    let coerced = result.unwrap();
    assert!(coerced.sort().is_int(), "coerced BitVec expression should match destination Int sort");
    // Part of #3055: unsigned BV→Int must use bare bv2int (Bv2Int node), not bv2int_signed (ITE).
    assert!(
        !format!("{:?}", coerced).contains("Ite"),
        "unsigned BV→Int should not contain ITE (signed expansion), got {:?}",
        coerced
    );
}

#[test]
fn test_coerce_assignment_rhs_to_sort_bitvec_to_int_signed() {
    let bv_expr = Expr::bitvec_const(0x8000_0000u64, 32);
    let target = Sort::int();

    let result = ChcCtx::coerce_assignment_rhs_to_sort(bv_expr, &target, Some(true));
    assert!(result.is_some(), "BitVec to Int signed assignment coercion should succeed");
    let coerced = result.unwrap();
    assert!(coerced.sort().is_int(), "coerced BitVec expression should match destination Int sort");
    // Signed BV→Int: bv2int_signed expands to ITE(msb==1, bv2int-2^width, bv2int).
    assert!(
        format!("{:?}", coerced).contains("Ite"),
        "signed BV→Int should expand to ITE for two's complement, got {:?}",
        coerced
    );
}

#[test]
fn test_coerce_assignment_rhs_to_sort_slice_to_pointer_extracts_fld_ptr() {
    let slice_sort = struct_sort(
        "Slice_bv8",
        [
            ("fld_ptr", Sort::bitvec(64)),
            ("fld_len", Sort::bitvec(64)),
            ("fld_data", Sort::array(Sort::bitvec(64), Sort::bitvec(8))),
        ],
    );
    let slice_expr = Expr::var("slice", slice_sort);

    let result =
        ChcCtx::coerce_assignment_rhs_to_sort(slice_expr.clone(), &Sort::bitvec(64), Some(false))
            .expect("Slice_bv8 should coerce to its pointer field for BV64 destinations");

    let expected = slice_expr.field_select("Slice_bv8", "fld_ptr", Sort::bitvec(64));
    assert_eq!(
        result, expected,
        "assignment coercion should extract fld_ptr from Slice_bv8 payloads"
    );
}

// =============================================================================
// coerce_expr_to_target_sort (static method, pure logic)
// =============================================================================

#[test]
fn test_coerce_expr_to_target_sort_same_sort() {
    let bv32 = Expr::bitvec_const(42, 32);
    let target = Sort::bitvec(32);

    let result = ChcCtx::coerce_expr_to_target_sort(bv32, &target, false);
    assert!(result.is_some(), "Same-sort coercion should succeed");
    assert_eq!(result.unwrap().sort(), &target);
}

#[test]
fn test_coerce_expr_to_target_sort_bool_to_bitvec() {
    let bool_expr = Expr::var("b", Sort::bool());
    let target = Sort::bitvec(32);

    let result = ChcCtx::coerce_expr_to_target_sort(bool_expr, &target, false);
    assert!(result.is_some(), "Bool to bitvec coercion should succeed");
    assert_eq!(result.unwrap().sort().bitvec_width(), Some(32), "Result should be 32-bit");
}

#[test]
fn test_coerce_expr_to_target_sort_bitvec_to_bitvec_different_width() {
    let bv16 = Expr::bitvec_const(100, 16);
    let target = Sort::bitvec(32);

    let result = ChcCtx::coerce_expr_to_target_sort(bv16, &target, false);
    assert!(result.is_some(), "Bitvec width coercion should succeed");
    assert_eq!(result.unwrap().sort().bitvec_width(), Some(32), "Result should be 32-bit");
}

#[test]
fn test_coerce_expr_to_target_sort_int_to_bitvec() {
    let int_expr = Expr::int_const(42);
    let target = Sort::bitvec(64);

    let result = ChcCtx::coerce_expr_to_target_sort(int_expr, &target, false);
    assert!(result.is_some(), "Int to bitvec coercion should succeed");
    assert_eq!(result.unwrap().sort().bitvec_width(), Some(64), "Result should be 64-bit");
}

#[test]
fn test_coerce_expr_to_target_sort_bitvec_to_int() {
    let bv_expr = Expr::bitvec_const(42, 32);
    let target = Sort::int();

    let result = ChcCtx::coerce_expr_to_target_sort(bv_expr, &target, false);
    assert!(result.is_some(), "Bitvec to Int coercion should succeed");
    assert!(result.unwrap().sort().is_int(), "Result should be Int sort");
}

#[test]
fn test_coerce_expr_to_target_sort_int_to_int() {
    let int_expr = Expr::int_const(42);
    let target = Sort::int();

    let result = ChcCtx::coerce_expr_to_target_sort(int_expr, &target, false);
    assert!(result.is_some(), "Int to Int coercion should succeed");
    assert!(result.unwrap().sort().is_int(), "Result should be Int sort");
}

#[test]
fn test_coerce_expr_to_target_sort_array_target_returns_none() {
    let bv_expr = Expr::bitvec_const(42, 32);
    let target = Sort::array(Sort::bitvec(32), Sort::bitvec(32));

    let result = ChcCtx::coerce_expr_to_target_sort(bv_expr, &target, false);
    assert!(result.is_none(), "Coercion to Array sort should return None");
}

// =============================================================================
// build_copy_index_guard (static method, pure logic)
// =============================================================================

#[test]
fn test_build_copy_index_guard_bitvec_bitvec() {
    let idx = Expr::bitvec_const(0, 32);
    let count = Expr::bitvec_const(4, 32);

    let result = ChcCtx::build_copy_index_guard(idx, count);
    assert!(result.is_some(), "BV index guard should be built");
    let guard = result.unwrap();
    assert!(guard.sort().is_bool(), "Guard should be Bool");
}

#[test]
fn test_build_copy_index_guard_int_int() {
    let idx = Expr::int_const(0);
    let count = Expr::int_const(4);

    let result = ChcCtx::build_copy_index_guard(idx, count);
    assert!(result.is_some(), "Int index guard should be built");
    let guard = result.unwrap();
    assert!(guard.sort().is_bool(), "Guard should be Bool");
}

#[test]
fn test_build_copy_index_guard_mixed_sorts_returns_none() {
    let idx = Expr::bitvec_const(0, 32);
    let count = Expr::int_const(4);

    let result = ChcCtx::build_copy_index_guard(idx, count);
    assert!(result.is_none(), "Mixed BV/Int sorts should return None");
}

#[test]
fn test_build_copy_index_guard_bool_sorts_returns_none() {
    let idx = Expr::bool_const(true);
    let count = Expr::bool_const(false);

    let result = ChcCtx::build_copy_index_guard(idx, count);
    assert!(result.is_none(), "Bool sorts should return None (no comparison defined)");
}

// =============================================================================
// CopyNonOverlapping MIR-driven pipeline test
// =============================================================================

#[test]
fn test_mir_copy_nonoverlapping_array_pipeline() {
    // Compile a function that uses copy_nonoverlapping between two arrays.
    // Verify the CHC pipeline processes it without panicking and produces a VC.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_array() {
            let src = [1u32, 2, 3, 4];
            let mut dst = [0u32; 4];
            unsafe {
                std::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 4);
            }
            let _ = dst;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_array");
        let body = instance.body().expect("function body");
        let bb_count = body.blocks.len();

        let vc = mir_to_chc(ctx.tcx, &body, "probe_copy_array", ChcConfig::default());
        assert!(
            !vc.relations.is_empty(),
            "VC should have relations for copy_nonoverlapping pipeline"
        );
        assert!(!vc.rules.is_empty(), "VC should have rules for copy_nonoverlapping pipeline");
        // Basic structural checks
        assert!(vc.relations.len() >= bb_count, "Should have at least one relation per BB");
    });
}

#[test]
fn test_mir_copy_nonoverlapping_zero_length() {
    // Zero-length copy should be a no-op in the CHC encoding
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_zero() {
            let src = [1u32; 4];
            let mut dst = [0u32; 4];
            unsafe {
                std::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 0);
            }
            let _ = dst;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_zero");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_copy_zero", ChcConfig::default());
        assert!(!vc.relations.is_empty(), "VC should be generated for zero-length copy");
    });
}

#[test]
fn test_mir_copy_nonoverlapping_scalar_count_one_no_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_scalar() -> i32 {
            let src = 42i32;
            let mut dst = 99i32;
            unsafe {
                std::ptr::copy_nonoverlapping(&src as *const i32, &mut dst as *mut i32, 1);
            }
            dst
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_scalar");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_copy_scalar", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "scalar count=1 copy_nonoverlapping should avoid demoted fallback"
        );
        assert!(!vc.rules.is_empty(), "scalar copy_nonoverlapping should emit rules");
    });
}

#[test]
fn test_mir_intrinsic_copy_scalar_count_one_no_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn probe_intrinsic_copy_scalar() -> i32 {
            let src = 7i32;
            let mut dst = 11i32;
            unsafe {
                core::intrinsics::copy(&src as *const i32, &mut dst as *mut i32, 1);
            }
            dst
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_intrinsic_copy_scalar");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_intrinsic_copy_scalar", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "scalar intrinsic copy should reuse the precise count=1 path without fallback"
        );
        assert!(!vc.rules.is_empty(), "scalar intrinsic copy should emit rules");
    });
}

#[test]
fn test_mir_intrinsic_copy_with_offset_no_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn probe_intrinsic_copy_with_offset() -> [i32; 3] {
            let arr: [i32; 3] = [0, 1, 0];
            let src: *const i32 = arr.as_ptr();
            unsafe {
                let dst = src.add(1) as *mut i32;
                core::intrinsics::copy(src, dst, 2);
            }
            arr
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_intrinsic_copy_with_offset");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_intrinsic_copy_with_offset", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "offset intrinsic copy should stay on the precise path without demoted fallback"
        );
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(store"),
            "offset intrinsic copy should emit array store constraints"
        );
    });
}

#[test]
fn test_mir_copy_nonoverlapping_uninitialized_swap_no_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code, deprecated)]

        fn swap<T>(x: &mut T, y: &mut T) {
            unsafe {
                let mut t: T = std::mem::uninitialized();
                std::ptr::copy_nonoverlapping(x, &mut t, 1);
                std::ptr::copy_nonoverlapping(y, x, 1);
                std::ptr::copy_nonoverlapping(&t, y, 1);
                std::mem::forget(t);
            }
        }

        pub fn probe_i32_anchor(x: i32) -> i32 { x }

        pub fn probe_copy_swap() -> (i32, i32) {
            let mut x = 12;
            let mut y = 13;
            swap(&mut x, &mut y);
            (x, y)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let concrete_ty = fn_sig_by_suffix(ctx.tcx, "probe_i32_anchor").inputs()[0];
        let instance = resolve_single_type_generic_instance_by_suffix(ctx.tcx, "swap", concrete_ty);
        let body = instance.body().expect("resolved generic function body");
        let chc_ctx =
            ChcCtx::new_with_instance(ctx.tcx, &body, instance, "swap", ChcConfig::default());
        let (_vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "swap scratch-slot copy path should avoid demoted fallback"
        );
        assert_eq!(
            diagnostics.type_sort_fallback.get(),
            0,
            "mem::uninitialized scratch slot should avoid type/layout fallback"
        );
        assert_eq!(
            diagnostics.unhandled_call.get(),
            0,
            "mem::uninitialized scratch slot should stay off the unhandled-call path"
        );
    });
}

// =============================================================================
// Part of #4079 D4: coroutine root coercion regression
// =============================================================================

/// Build a synthetic coroutine root sort with 2 same-sort captured fields.
/// Structure:
///   CoroutineRoot { direct_fields: DirectFields { case: BV8, field_0: BV32, field_1: BV32 } }
fn build_two_field_coroutine_root_sort() -> Sort {
    let direct_fields_sort = struct_sort(
        "DirectFields",
        [
            ("case", Sort::bitvec(8)),
            ("coroutine_field_0", Sort::bitvec(32)),
            ("coroutine_field_1", Sort::bitvec(32)),
        ],
    );
    struct_sort("CoroutineRoot", [("direct_fields", direct_fields_sort)])
}

/// Part of #4079 D4: after removing the field_0 heuristic, the generic
/// `coerce_assignment_rhs_to_sort` must return `None` for a multi-field
/// coroutine root with same-sort captured fields.
#[test]
fn test_coroutine_root_multi_field_coercion_returns_none() {
    let root_sort = build_two_field_coroutine_root_sort();
    let root_expr = Expr::var("_coroutine", root_sort);

    let result = ChcCtx::coerce_assignment_rhs_to_sort(root_expr, &Sort::bitvec(32), Some(false));
    assert!(
        result.is_none(),
        "Generic coercion must not guess field_0 for multi-field coroutine root"
    );
}

// =============================================================================
// P3-uninit: scalar LE byte splice for punned constant-size copies
// (`try_copy_scalar_byte_splice` — codegen_stmt_copy.rs)
// =============================================================================

/// A punned constant-size partial copy into a BV-sorted scalar local must be
/// encoded as a precise little-endian byte splice — no demoting fallback, and
/// the destination constraint preserves the untouched high bits via
/// `concat(extract(63, 32, dst_in), src_bytes)`.
#[test]
fn test_punned_partial_copy_scalar_byte_splice() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_punned_partial_copy(src: u32) -> u64 {
            let mut dst: u64 = 0xAABB_CCDD_EEFF_0011;
            unsafe {
                std::ptr::copy_nonoverlapping(
                    &src as *const u32 as *const u8,
                    &mut dst as *mut u64 as *mut u8,
                    4,
                );
            }
            dst
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_punned_partial_copy");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_punned_partial_copy", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "punned constant-size copy into a scalar local must take the \
             byte-splice path, not the demoting self-loop havoc"
        );
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("(concat ((_ extract 63 32)"),
            "splice must preserve the destination's high 32 bits via \
             concat(extract(63,32,dst_in), src): {smt}"
        );
    });
}

/// A full 8-byte struct copy (S(u32,u8): 5 data + 3 padding bytes) through
/// punned `*const u8` must build the source image with nondet padding bits
/// (`copy_splice_pad`) — padding VALUE is unspecified — and no fallback.
#[test]
fn test_punned_struct_copy_le_image_with_padding_vars() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct S(pub u32, pub u8);

        pub fn probe_punned_struct_copy(a: u32, b: u8) -> u64 {
            let src = S(a, b);
            let mut dst: u64 = 0;
            unsafe {
                std::ptr::copy_nonoverlapping(
                    &src as *const S as *const u8,
                    &mut dst as *mut u64 as *mut u8,
                    8,
                );
            }
            dst
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_punned_struct_copy");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_punned_struct_copy", ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_eq!(
            diagnostics.fallback_count.get(),
            0,
            "punned struct copy with known layout must take the byte-splice path"
        );
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("copy_splice_pad"),
            "struct image must model the 3 padding bytes as fresh nondet bits: {smt}"
        );
    });
}

/// A SYMBOLIC-count punned copy must NOT take the splice (constant sizes
/// only) — the demoting fallback stays (fail-closed).
#[test]
fn test_punned_symbolic_count_copy_keeps_demoting_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_punned_symbolic_count(src: u32, n: usize) -> u64 {
            let mut dst: u64 = 0;
            unsafe {
                std::ptr::copy_nonoverlapping(
                    &src as *const u32 as *const u8,
                    &mut dst as *mut u64 as *mut u8,
                    n,
                );
            }
            dst
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_punned_symbolic_count");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_punned_symbolic_count", ChcConfig::default());
        let (_vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert!(
            diagnostics.fallback_count.get() > 0,
            "symbolic-count punned copy into a scalar must keep the demoting \
             fallback (fail-closed), got fallback_count=0"
        );
    });
}
