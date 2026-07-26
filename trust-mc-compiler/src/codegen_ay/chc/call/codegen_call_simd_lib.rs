// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD library operation dispatch for CHC code generation.
//!
//! Handles `Simd::from_array`, `to_array`, `as_array`, `splat`, and `resize` —
//! regular library functions (not compiler intrinsics) whose MIR bodies expand
//! through MaybeUninit + copy_nonoverlapping. After transparent type unwrapping
//! (#3792), both `Simd<T, N>` and `[T; N]` have the same `Array(BV64, BV_elem)`
//! sort, enabling direct CHC encoding.
//!
//! Part of #3792: portable-SIMD vector boundary residuals.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_simd::{
    SimdIntrinsicKind, emit_simd_dest_constraint, extract_simd_layout,
    neutral_simd_result_array_like, resolve_simd_array,
};
use super::codegen_call_simd_ops::{codegen_simd_elementwise_binop, codegen_simd_shift};
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Classification of SIMD library operations with dedicated CHC handlers.
#[derive(Clone, Copy, Debug)]
enum SimdLibKind {
    /// `Simd::from_array([T; N]) -> Simd<T, N>` — identity (same Array sort).
    FromArray,
    /// `Simd::to_array(self) -> [T; N]` — identity (same Array sort).
    ToArray,
    /// `Simd::as_array(&self) -> &[T; N]` — identity (value semantics).
    AsArray,
    /// `Simd::splat(v) -> Simd<T, N>` — const array, all lanes = v.
    Splat,
    /// `Simd::resize::<M>(self, default) -> Simd<T, M>` — truncate/extend.
    Resize,
}

/// Detect SIMD library operations that have dedicated CHC handlers.
fn detect_simd_lib_op(path: &str) -> Option<SimdLibKind> {
    if !path.contains("simd") && !path.contains("Simd") {
        return None;
    }
    let m = path.rsplit("::").next()?;
    match m {
        "from_array" => Some(SimdLibKind::FromArray),
        "to_array" => Some(SimdLibKind::ToArray),
        "as_array" | "as_mut_array" => Some(SimdLibKind::AsArray),
        "splat" => Some(SimdLibKind::Splat),
        "resize" => Some(SimdLibKind::Resize),
        _ => None,
    }
}

/// Part of #4086: Detect portable-SIMD arithmetic operator trait impls.
///
/// `<Simd<T, N> as Add>::add` etc. are thin wrappers around `simd_add` intrinsics.
/// Without interception, fn_inline enters the body, encounters intermediate MIR
/// (type coercions, temporaries), and often bails — leaving the result unconstrained.
/// Redirect to the existing SIMD intrinsic encoding instead.
///
/// Requires the path to contain both a SIMD indicator ("simd" or "Simd") AND "ops"
/// (the module where std arithmetic trait impls live) to avoid false matches on
/// non-SIMD types that happen to have methods named "add", "sub", etc.
fn detect_simd_arith_op(path: &str) -> Option<SimdIntrinsicKind> {
    if !(path.contains("simd") || path.contains("Simd")) {
        return None;
    }
    if !path.contains("ops") {
        return None;
    }
    let m = path.rsplit("::").next()?;
    match m {
        "add" => Some(SimdIntrinsicKind::Add),
        "sub" => Some(SimdIntrinsicKind::Sub),
        "mul" => Some(SimdIntrinsicKind::Mul),
        "div" => Some(SimdIntrinsicKind::Div),
        "rem" => Some(SimdIntrinsicKind::Rem),
        "bitand" => Some(SimdIntrinsicKind::And),
        "bitor" => Some(SimdIntrinsicKind::Or),
        "bitxor" => Some(SimdIntrinsicKind::Xor),
        "shl" => Some(SimdIntrinsicKind::Shl),
        "shr" => Some(SimdIntrinsicKind::Shr),
        "neg" => Some(SimdIntrinsicKind::Neg),
        _ => None,
    }
}

/// Try to dispatch a SIMD library call. Returns `true` if handled.
///
/// Must run before `try_dispatch_call_fn_inline` to avoid the fn_inline
/// path producing Bool-sorted results for Array-sorted destinations.
pub(in crate::codegen_ay::chc) fn try_dispatch_simd_lib_call(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> bool {
    let callee_path = dcx.callee_path.clone().or_else(|| ctx.resolve_callee_path(dcx.func));
    let Some(ref path) = callee_path else { return false };

    // Part of #4086: Check for portable-SIMD arithmetic operator trait impls first.
    // These are thin wrappers around simd_add/sub/mul etc. that fn_inline can't handle.
    if let Some(arith_kind) = detect_simd_arith_op(path) {
        return dispatch_simd_arith_op(ctx, dcx, arith_kind);
    }

    let Some(kind) = detect_simd_lib_op(path) else { return false };

    let Some(target) = dcx.target else { return true };
    if dcx.args.is_empty() {
        return false;
    }

    let dest_local: usize = dcx.destination.local;

    // Check if destination has Array sort (confirms transparent SIMD unwrapping).
    let dest_arr_info = ctx.resolve_destination(dest_local).and_then(|(_, v)| {
        let s = v.sort().clone();
        if s.is_array() { Some(s) } else { None }
    });

    // as_array returns &[T; N] — dest has reference (BV64) sort, not Array.
    if matches!(kind, SimdLibKind::AsArray) && dest_arr_info.is_none() {
        return dispatch_as_array_ref(ctx, dcx, *target, dest_local);
    }

    let Some(dest_sort) = dest_arr_info else {
        return false;
    };

    match kind {
        SimdLibKind::FromArray | SimdLibKind::ToArray | SimdLibKind::AsArray => {
            let arg_expr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
            let Some(arg_arr) = arg_expr else {
                debug!(?kind, "simd lib: operand resolution failed, deferring");
                return false;
            };
            debug!(?kind, bb = dcx.bb_idx, "simd identity dispatch");
            emit_simd_dest_constraint(ctx, dcx, *target, dest_local, arg_arr);
        }
        SimdLibKind::Splat => {
            let val = ctx.translate_operand_with_modified(&dcx.args[0], dcx.modified_locals);
            let Some(val) = val else {
                debug!("simd splat: operand resolution failed, deferring");
                return false;
            };
            let Some(arr_sort) = dest_sort.array_sort() else {
                return false;
            };
            let result = Expr::const_array(arr_sort.index_sort.clone(), val);
            debug!(bb = dcx.bb_idx, "simd splat dispatch");
            emit_simd_dest_constraint(ctx, dcx, *target, dest_local, result);
        }
        SimdLibKind::Resize => {
            return dispatch_simd_resize(ctx, dcx, *target, dest_local, &dest_sort);
        }
    }
    true
}

/// Handle `as_array` when dest is a reference type (not Array sort).
///
/// Part of #4086: Register both ref_target (for downstream deref resolution) AND
/// seed the Array value into `const_ref_values` so that `resolve_ref_or_const_referent`
/// can find it directly during comparison dispatch. Without the const_ref_values seed,
/// the eq handler sees unconstrained BV64 values for the `as_array()` results and
/// cannot prove `b.as_array() == b.as_array()` — both sides resolve to independent
/// free variables instead of the same underlying Array expression.
fn dispatch_as_array_ref(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    dest_local: usize,
) -> bool {
    let arg_local = match &dcx.args[0] {
        Operand::Copy(p) | Operand::Move(p) => Some(p.local),
        _ => None,
    };
    let Some(ref_local) = arg_local else { return false };
    let target_local =
        ctx.ref_resolution.ref_targets.get(&ref_local).map(|rt| rt.local).unwrap_or(ref_local);
    debug!(bb = dcx.bb_idx, dest_local, ref_local, target_local, "simd as_array ref_target");
    ctx.ref_resolution.ref_targets.insert(
        dest_local,
        crate::codegen_ay::chc::codegen_ctx::types::RefTarget::with_projections(
            target_local,
            vec![],
        ),
    );

    // Part of #4086: Resolve the source SIMD local to its Array expression and
    // seed it as a const_ref_value. This allows `resolve_ref_or_const_referent`
    // Tier 2 to return the Array directly for comparison dispatch, bypassing the
    // multi-hop ref_targets chain that can fail across CHC rule boundaries.
    // Use the target_local (the actual SIMD/Array local, not the &self ref local)
    // to build a synthetic operand for resolution.
    let src_place = rustc_public::mir::Place { local: target_local, projection: vec![] };
    let src_operand = Operand::Copy(src_place);
    if let Some(arr_expr) =
        super::codegen_call_simd::resolve_simd_array(ctx, &src_operand, dcx.modified_locals)
    {
        debug!(bb = dcx.bb_idx, dest_local, "simd as_array: seeded const_ref_values with Array");
        ctx.ref_resolution.const_ref_values.insert(dest_local, arr_expr);
    }

    let out = ctx.build_output_args(dcx.modified_locals, &[]);
    ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    true
}

/// Dispatch `Simd::resize::<M>(self, default) -> Simd<T, M>`.
///
/// Builds: `const_array(idx_sort, default)` then stores src[0..min(N,M)] on top.
fn dispatch_simd_resize(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    dest_local: usize,
    dest_sort: &ay_bindings::Sort,
) -> bool {
    if dcx.args.len() < 2 {
        debug!("simd resize: expected 2 args (self, default), got {}", dcx.args.len());
        return false;
    }

    let src_ty = dcx.args[0].ty(ctx.body.locals()).ok();
    let src_layout = src_ty.and_then(extract_simd_layout);
    let dest_ty = ctx.body.locals()[dest_local].ty;
    let dest_layout = extract_simd_layout(dest_ty);

    let (Some(src_ly), Some(dest_ly)) = (src_layout, dest_layout) else {
        debug!("simd resize: layout extraction failed, deferring");
        return false;
    };

    let src_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let default_val = ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals);

    let (Some(src), Some(default)) = (src_arr, default_val) else {
        debug!("simd resize: operand resolution failed, deferring");
        return false;
    };

    let Some(arr_sort) = dest_sort.array_sort() else {
        return false;
    };
    let mut result = Expr::const_array(arr_sort.index_sort.clone(), default);

    let copy_count = src_ly.lane_count.min(dest_ly.lane_count);
    for i in 0..copy_count {
        let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
        let val = src.clone().select(idx.clone());
        result = result.store(idx, val);
    }

    debug!(
        bb = dcx.bb_idx,
        src_lanes = src_ly.lane_count,
        dest_lanes = dest_ly.lane_count,
        "simd resize dispatch"
    );
    emit_simd_dest_constraint(ctx, dcx, target, dest_local, result);
    true
}

/// Part of #4086: Dispatch portable-SIMD arithmetic operators to intrinsic handlers.
///
/// `<Simd<T, N> as Add>::add(self, rhs)` has the same calling convention as
/// `simd_add(a, b)` — both take two SIMD values by value and return one.
/// Redirect to the existing element-wise binop / shift handlers.
fn dispatch_simd_arith_op(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    kind: SimdIntrinsicKind,
) -> bool {
    let Some(target) = dcx.target else { return true };
    if dcx.args.len() < 2 && !matches!(kind, SimdIntrinsicKind::Neg) {
        return false;
    }
    if dcx.args.is_empty() {
        return false;
    }

    debug!(?kind, bb = dcx.bb_idx, "simd arith operator dispatch (Part of #4086)");

    match kind {
        SimdIntrinsicKind::Add
        | SimdIntrinsicKind::Sub
        | SimdIntrinsicKind::Mul
        | SimdIntrinsicKind::Div
        | SimdIntrinsicKind::Rem
        | SimdIntrinsicKind::And
        | SimdIntrinsicKind::Or
        | SimdIntrinsicKind::Xor => {
            codegen_simd_elementwise_binop(ctx, dcx, *target, kind);
        }
        SimdIntrinsicKind::Shl | SimdIntrinsicKind::Shr => {
            codegen_simd_shift(ctx, dcx, *target, kind);
        }
        SimdIntrinsicKind::Neg => {
            // Neg is unary — delegate to the existing simd neg handler via the
            // intrinsic trait. Use the same resolve+emit pattern as codegen_simd_neg.
            let dest_local: usize = dcx.destination.local;
            let src_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
            let layout = dcx.args.first().and_then(|op| {
                let ty = op.ty(ctx.body.locals()).ok()?;
                extract_simd_layout(ty)
            });
            if let (Some(src), Some(layout)) = (src_arr, layout) {
                let mut result = neutral_simd_result_array_like(&src, layout.elem_width)
                    .unwrap_or_else(|| src.clone());
                let sign_mask = if layout.is_float {
                    Some(Expr::bitvec_const(1u64 << (layout.elem_width - 1), layout.elem_width))
                } else {
                    None
                };
                for i in 0..layout.lane_count {
                    let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
                    let val = src.clone().select(idx.clone());
                    let neg_val = if let Some(ref mask) = sign_mask {
                        val.bvxor(mask.clone())
                    } else {
                        val.bvneg()
                    };
                    result = result.store(idx, neg_val);
                }
                emit_simd_dest_constraint(ctx, dcx, *target, dest_local, result);
            } else {
                use super::codegen_call_simd::emit_simd_sound_fallback;
                emit_simd_sound_fallback(ctx, dcx, *target);
            }
        }
        _ => return false,
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_simd_lib_op_from_array() {
        let path = "std::simd::Simd::<u32, 4>::from_array";
        assert!(matches!(detect_simd_lib_op(path), Some(SimdLibKind::FromArray)));
    }

    #[test]
    fn test_detect_simd_lib_op_to_array() {
        let path = "core::core_simd::vector::Simd::<u64, 16>::to_array";
        assert!(matches!(detect_simd_lib_op(path), Some(SimdLibKind::ToArray)));
    }

    #[test]
    fn test_detect_simd_lib_op_as_array() {
        let path = "std::simd::Simd::<u32, 4>::as_array";
        assert!(matches!(detect_simd_lib_op(path), Some(SimdLibKind::AsArray)));
    }

    #[test]
    fn test_detect_simd_lib_op_splat() {
        let path = "core::core_simd::vector::Simd::<u64, 16>::splat";
        assert!(matches!(detect_simd_lib_op(path), Some(SimdLibKind::Splat)));
    }

    #[test]
    fn test_detect_simd_lib_op_resize() {
        let path = "std::simd::Simd::<u32, 4>::resize";
        assert!(matches!(detect_simd_lib_op(path), Some(SimdLibKind::Resize)));
    }

    #[test]
    fn test_detect_simd_lib_op_non_simd_path() {
        assert!(detect_simd_lib_op("std::vec::Vec::from_array").is_none());
        assert!(detect_simd_lib_op("std::collections::HashMap::splat").is_none());
    }

    #[test]
    fn test_detect_simd_lib_op_unknown_method() {
        let path = "std::simd::Simd::<u32, 4>::unknown_method";
        assert!(detect_simd_lib_op(path).is_none());
    }

    // Part of #4086: Tests for portable-SIMD arithmetic operator detection.

    #[test]
    fn test_detect_simd_arith_op_add() {
        let path = "core::core_simd::ops::<impl core::ops::arith::Add for core::core_simd::vector::Simd<f32, 4>>::add";
        assert!(matches!(detect_simd_arith_op(path), Some(SimdIntrinsicKind::Add)));
    }

    #[test]
    fn test_detect_simd_arith_op_sub() {
        let path = "core::core_simd::ops::<impl core::ops::arith::Sub for Simd<i64, 2>>::sub";
        assert!(matches!(detect_simd_arith_op(path), Some(SimdIntrinsicKind::Sub)));
    }

    #[test]
    fn test_detect_simd_arith_op_mul() {
        let path = "core::core_simd::ops::<impl core::ops::arith::Mul for Simd<u32, 4>>::mul";
        assert!(matches!(detect_simd_arith_op(path), Some(SimdIntrinsicKind::Mul)));
    }

    #[test]
    fn test_detect_simd_arith_op_bitand() {
        let path = "core::core_simd::ops::<impl core::ops::bit::BitAnd for Simd<u8, 16>>::bitand";
        assert!(matches!(detect_simd_arith_op(path), Some(SimdIntrinsicKind::And)));
    }

    #[test]
    fn test_detect_simd_arith_op_non_simd_rejected() {
        // Regular Add::add on a non-SIMD type should NOT match.
        let path = "core::ops::arith::<impl core::ops::arith::Add for i32>::add";
        assert!(detect_simd_arith_op(path).is_none());
    }

    #[test]
    fn test_detect_simd_arith_op_no_ops_rejected() {
        // SIMD path without "ops" should NOT match (e.g., Simd::add if it existed).
        let path = "std::simd::Simd::<u32, 4>::add";
        assert!(detect_simd_arith_op(path).is_none());
    }
}
