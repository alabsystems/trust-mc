// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Primitive comparison handlers: Ord::cmp, PartialOrd, PartialEq.
//!
//! Extracted from codegen_call_cmp_string.rs — Part of #2408.

use ay_bindings::Expr;
use rustc_public::mir::BasicBlockIdx;
use tracing::warn;

use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_expr_signedness::arg_signedness_or_fallback;
use super::super::codegen_rules::CodegenRules;
use super::super::stubs_option_helpers::{OptionHelpers, option_value_sort};
use super::cmp_array;
use super::cmp_array::{
    MAX_LEXICO_LANES, array_len_from_body_locals, array_len_from_operand, build_lexicographic_cmp,
    build_lexicographic_cmp_from_elements, build_lexicographic_ord,
    build_lexicographic_ord_from_elements, try_load_array_elements,
};
use super::cmp_raw_pointer::{
    operand_is_raw_pointer_like, raw_pointer_cmp_expr_with_operands,
    raw_pointer_ord_expr_with_operands, resolve_raw_pointer_cmp_operand,
};
use super::cmp_slice_backing::{
    SliceBackingCmpResult, compute_optional_slice_backing_method_cmp_result,
};
use crate::codegen_ay::shared::SignednessFallbackKind;

/// Handle primitive comparison trait calls:
/// - `Ord::cmp` / `PartialOrd::partial_cmp`
/// - `PartialEq::{eq, ne}`
/// - `PartialOrd::{lt, le, gt, ge}`
pub(in crate::codegen_ay::chc) fn codegen_primitive_cmp(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    method: &str,
) {
    let args = dcx.args;
    let destination = dcx.destination;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let bb_idx = dcx.bb_idx;
    let dest_local: usize = destination.local;
    let is_partial = method == "partial_cmp";
    let raw_pointer_ordering = operand_is_raw_pointer_like(&args[0], ctx.body.locals())
        && operand_is_raw_pointer_like(&args[1], ctx.body.locals());
    let lhs = if raw_pointer_ordering {
        resolve_raw_pointer_cmp_operand(ctx, &args[0], modified_locals)
    } else {
        ctx.resolve_ref_or_const_referent(&args[0], modified_locals)
    };
    let rhs = if raw_pointer_ordering {
        resolve_raw_pointer_cmp_operand(ctx, &args[1], modified_locals)
    } else {
        ctx.resolve_ref_or_const_referent(&args[1], modified_locals)
    };
    if let (Some(mut lhs), Some(mut rhs)) = (lhs, rhs) {
        let lhs_raw = lhs.clone();
        let rhs_raw = rhs.clone();
        // Part of #3806, #4086: when operands are BV pointers (from referenced
        // args like &&[T; N] in `<&A as PartialOrd<&B>>::partial_cmp`), try to
        // follow the ref_targets chain to find the actual array-sorted values.
        // BV64 = thin pointer (refs to sized types).
        // BV128 = fat pointer (refs to slices like &[i64] from Unsize coercion
        // of &[i64; 2], which appears in MIR-inlined partial_cmp for SIMD types).
        if !raw_pointer_ordering && matches!(lhs.sort().bitvec_width(), Some(64 | 128)) {
            let arr = ctx.resolve_ref_chain_to_array(&args[0], modified_locals);
            if let Some(arr) = arr {
                lhs = arr;
            }
        }
        if !raw_pointer_ordering && matches!(rhs.sort().bitvec_width(), Some(64 | 128)) {
            let arr = ctx.resolve_ref_chain_to_array(&args[1], modified_locals);
            if let Some(arr) = arr {
                rhs = arr;
            }
        }
        // Part of #3806: When operands are Slice Datatypes (from Unsize coercion),
        // extract the fld_data array for lexicographic comparison.
        if !raw_pointer_ordering {
            if let Some(arr) = extract_slice_array_data(&lhs) {
                lhs = arr;
            }
            if let Some(arr) = extract_slice_array_data(&rhs) {
                rhs = arr;
            }
        }
        // Part of #4086: When operands are single-field Datatype wrappers
        // around Array (from user-defined #[repr(simd)] types like i64x2),
        // unwrap to the inner Array for lexicographic comparison.
        if !raw_pointer_ordering {
            if let Some(arr) = extract_single_field_array_wrapper(&lhs) {
                lhs = arr;
            }
            if let Some(arr) = extract_single_field_array_wrapper(&rhs) {
                rhs = arr;
            }
        }
        // Part of #3702: signedness detection is deferred to ordering-only
        // branches (cmp, partial_cmp, lt/le/gt/ge). For eq/ne, signedness
        // does not affect semantics — widening with signed=false avoids a
        // spurious signedness_fallback that demotes valid PROOFs.
        // Part of #3427: skip signedness entirely for non-bitvec sorts.
        let is_signed_for_ordering = if matches!(method, "eq" | "ne") || raw_pointer_ordering {
            false // eq/ne and raw-pointer ordering never depend on pointee signedness
        } else if lhs.sort().is_bitvec() || rhs.sort().is_bitvec() {
            arg_signedness_or_fallback(
                &args[0],
                ctx.body.locals(),
                "primitive_cmp",
                SignednessFallbackKind::Comparison,
            )
        } else if lhs.sort().is_array() || rhs.sort().is_array() {
            // Part of #3806: for Array-sort operands (from resolved ref chains),
            // derive signedness from the element type. Peeling through references
            // and arrays in the MIR type to find the scalar element type.
            arg_signedness_or_fallback(
                &args[0],
                ctx.body.locals(),
                "primitive_cmp_array",
                SignednessFallbackKind::Comparison,
            )
        } else {
            false // non-bitvec: no fallback recorded
        };
        let is_signed = is_signed_for_ordering;
        let slice_backing_cmp = if !raw_pointer_ordering {
            let lhs_backing =
                args.first().and_then(|arg| ctx.resolve_slice_backing(arg, modified_locals));
            let rhs_backing =
                args.get(1).and_then(|arg| ctx.resolve_slice_backing(arg, modified_locals));
            compute_optional_slice_backing_method_cmp_result(
                method,
                lhs_backing.as_ref(),
                rhs_backing.as_ref(),
                is_signed,
            )
        } else {
            None
        };
        if slice_backing_cmp.as_ref().is_some_and(SliceBackingCmpResult::is_unsupported) {
            warn!(
                fn_name = %ctx.fn_name,
                method,
                bb_idx,
                "CHC: slice-backed comparison unsupported; using sound fallback"
            );
            emit_sound_fallback_goto(
                ctx,
                from_app,
                target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
            return;
        }
        let mut extra_constraints = Vec::new();
        let cmp_result = match method {
            "cmp" | "partial_cmp" => {
                if raw_pointer_ordering {
                    if let Some(cmp_expr) = raw_pointer_cmp_expr_with_operands(
                        ctx,
                        &lhs_raw,
                        &rhs_raw,
                        &args[0],
                        &args[1],
                        modified_locals,
                    ) {
                        cmp_expr
                    } else {
                        warn!(
                            fn_name = %ctx.fn_name,
                            method,
                            lhs_sort = ?lhs_raw.sort(),
                            rhs_sort = ?rhs_raw.sort(),
                            bb_idx,
                            "CHC: raw-pointer cmp could not derive ordering keys"
                        );
                        emit_sound_fallback_goto(
                            ctx,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    }
                } else if let Some(cmp_expr) =
                    slice_backing_cmp.as_ref().and_then(SliceBackingCmpResult::as_expr)
                {
                    let cmp_expr = cmp_expr.clone();
                    cmp_expr
                } else {
                    // Build ITE chain: lt -> -1, eq -> 0, else -> 1
                    if lhs.sort().is_array()
                        && rhs.sort().is_array()
                        && let Some(len) = array_len_from_operand(&args[0], ctx.body.locals())
                            .or_else(|| array_len_from_body_locals(&args[0], ctx.body.locals()))
                        && len <= MAX_LEXICO_LANES
                        && let Some(cmp_expr) = build_lexicographic_cmp(&lhs, &rhs, len, is_signed)
                    {
                        // Part of #3806: lexicographic cmp for fixed-size arrays (SIMD).
                        cmp_expr
                    } else if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
                        // Part of #3806: when BV64 operands are pointers to array/slice
                        // data (from `<&A as PartialOrd<&B>>::partial_cmp`), try loading
                        // elements from heap memory for element-wise comparison.
                        let arr_len = array_len_from_operand(&args[0], ctx.body.locals())
                            .or_else(|| array_len_from_body_locals(&args[0], ctx.body.locals()));
                        if let Some(len) = arr_len
                            && len <= MAX_LEXICO_LANES
                        {
                            // Part of #4086: packed BV decomposition for repr(simd) types.
                            // When operands are BV(N*W) (e.g., BV128 for [i64; 2]),
                            // extract elements via bit-slicing instead of heap loading.
                            let elem_width =
                                cmp_array::packed_simd_element_width(&args[0], ctx.body.locals());
                            let packed_elems = elem_width.and_then(|ew| {
                                let le = cmp_array::extract_packed_bv_elements(&lhs, len, ew)?;
                                let re = cmp_array::extract_packed_bv_elements(&rhs, len, ew)?;
                                build_lexicographic_cmp_from_elements(&le, &re, is_signed)
                            });
                            if let Some(cmp_expr) = packed_elems {
                                cmp_expr
                            } else if let Some(lhs_elems) =
                                try_load_array_elements(ctx, &lhs, &args[0], len)
                                && let Some(rhs_elems) =
                                    try_load_array_elements(ctx, &rhs, &args[1], len)
                                && let Some(cmp_expr) = build_lexicographic_cmp_from_elements(
                                    &lhs_elems, &rhs_elems, is_signed,
                                )
                            {
                                cmp_expr
                            } else {
                                // Fall through to scalar BV comparison below
                                let Some(target_width) = ChcCtx::max_bitvec_width(&lhs, &rhs)
                                else {
                                    warn!(fn_name = %ctx.fn_name, "CHC: cmp bitvec width resolution failed");
                                    emit_sound_fallback_goto(
                                        ctx,
                                        from_app,
                                        target,
                                        modified_locals,
                                        &[dest_local],
                                        stmt_constraints,
                                    );
                                    return;
                                };
                                let (lhs, rhs) = (
                                    coerce_bitvec_width_safe(
                                        lhs,
                                        target_width,
                                        SignExtension::for_signedness(is_signed),
                                    ),
                                    coerce_bitvec_width_safe(
                                        rhs,
                                        target_width,
                                        SignExtension::for_signedness(is_signed),
                                    ),
                                );
                                let lt = if is_signed {
                                    lhs.clone().bvslt(rhs.clone())
                                } else {
                                    lhs.clone().bvult(rhs.clone())
                                };
                                let eq = lhs.eq(rhs);
                                Expr::ite(
                                    lt,
                                    Expr::bitvec_const(-1i128, 32),
                                    Expr::ite(
                                        eq,
                                        Expr::bitvec_const(0, 32),
                                        Expr::bitvec_const(1, 32),
                                    ),
                                )
                            }
                        } else {
                            // No array length found — scalar BV comparison.
                            let Some(target_width) = ChcCtx::max_bitvec_width(&lhs, &rhs) else {
                                warn!(fn_name = %ctx.fn_name, "CHC: cmp bitvec width resolution failed");
                                emit_sound_fallback_goto(
                                    ctx,
                                    from_app,
                                    target,
                                    modified_locals,
                                    &[dest_local],
                                    stmt_constraints,
                                );
                                return;
                            };
                            let (lhs, rhs) = (
                                coerce_bitvec_width_safe(
                                    lhs,
                                    target_width,
                                    SignExtension::for_signedness(is_signed),
                                ),
                                coerce_bitvec_width_safe(
                                    rhs,
                                    target_width,
                                    SignExtension::for_signedness(is_signed),
                                ),
                            );
                            let lt = if is_signed {
                                lhs.clone().bvslt(rhs.clone())
                            } else {
                                lhs.clone().bvult(rhs.clone())
                            };
                            let eq = lhs.eq(rhs);
                            Expr::ite(
                                lt,
                                Expr::bitvec_const(-1i128, 32),
                                Expr::ite(eq, Expr::bitvec_const(0, 32), Expr::bitvec_const(1, 32)),
                            )
                        }
                    } else if lhs.sort().is_int() && rhs.sort().is_int() {
                        let lt = lhs.clone().int_lt(rhs.clone());
                        let eq = lhs.eq(rhs);
                        Expr::ite(
                            lt,
                            Expr::bitvec_const(-1i128, 32),
                            Expr::ite(eq, Expr::bitvec_const(0, 32), Expr::bitvec_const(1, 32)),
                        )
                    } else {
                        // Part of #2773: upgraded from debug! and added record_fallback().
                        warn!(
                            fn_name = %ctx.fn_name,
                            method,
                            lhs_sort = ?lhs.sort(),
                            rhs_sort = ?rhs.sort(),
                            bb_idx,
                            "CHC: primitive cmp/partial_cmp unsupported sorts; destination left unconstrained"
                        );
                        emit_sound_fallback_goto(
                            ctx,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    }
                }
            }
            "eq" | "ne" => {
                // PartialEq::eq / PartialEq::ne (Part of #2196, #3427)
                if raw_pointer_ordering {
                    let Some(cmp_expr) = raw_pointer_cmp_expr_with_operands(
                        ctx,
                        &lhs_raw,
                        &rhs_raw,
                        &args[0],
                        &args[1],
                        modified_locals,
                    ) else {
                        warn!(
                            fn_name = %ctx.fn_name,
                            method,
                            lhs_sort = ?lhs_raw.sort(),
                            rhs_sort = ?rhs_raw.sort(),
                            bb_idx,
                            "CHC: raw-pointer eq/ne could not derive ordering keys"
                        );
                        emit_sound_fallback_goto(
                            ctx,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    };
                    let ptr_eq = cmp_expr.eq(Expr::bitvec_const(0, 32));
                    if method == "eq" { ptr_eq } else { ptr_eq.not() }
                } else if let Some(cmp_expr) =
                    slice_backing_cmp.as_ref().and_then(SliceBackingCmpResult::as_expr)
                {
                    let cmp_expr = cmp_expr.clone();
                    cmp_expr
                } else if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
                    // Part of #3124: graceful fallback instead of panic.
                    let Some(target_width) = ChcCtx::max_bitvec_width(&lhs, &rhs) else {
                        warn!(fn_name = %ctx.fn_name, "CHC: eq/ne bitvec width resolution failed");
                        emit_sound_fallback_goto(
                            ctx,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    };
                    let lhs = coerce_bitvec_width_safe(
                        lhs,
                        target_width,
                        SignExtension::for_signedness(is_signed),
                    );
                    let rhs = coerce_bitvec_width_safe(
                        rhs,
                        target_width,
                        SignExtension::for_signedness(is_signed),
                    );
                    if method == "eq" { lhs.eq(rhs) } else { lhs.ne(rhs) }
                } else if lhs.sort() == rhs.sort() {
                    // Same sort: SMT-LIB = is sort-polymorphic and works on all
                    // sorts including int, bool, datatype (Vec, Bits, etc.), and
                    // array. This handles derived PartialEq on structs containing
                    // Vec<bool> and similar composite types. Part of #3427.
                    if method == "eq" { lhs.eq(rhs) } else { lhs.ne(rhs) }
                } else {
                    // Part of #2773: upgraded from debug! and added record_fallback().
                    warn!(
                        fn_name = %ctx.fn_name,
                        method,
                        lhs_sort = ?lhs.sort(),
                        rhs_sort = ?rhs.sort(),
                        bb_idx,
                        "CHC: primitive eq/ne unsupported sorts; destination left unconstrained"
                    );
                    emit_sound_fallback_goto(
                        ctx,
                        from_app,
                        target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                    return;
                }
            }
            "lt" | "le" | "gt" | "ge" => {
                if raw_pointer_ordering {
                    if let Some(ord_expr) = raw_pointer_ord_expr_with_operands(
                        ctx,
                        &lhs_raw,
                        &rhs_raw,
                        &args[0],
                        &args[1],
                        method,
                        modified_locals,
                    ) {
                        ord_expr
                    } else {
                        warn!(
                            fn_name = %ctx.fn_name,
                            method,
                            lhs_sort = ?lhs_raw.sort(),
                            rhs_sort = ?rhs_raw.sort(),
                            bb_idx,
                            "CHC: raw-pointer ord could not derive ordering keys"
                        );
                        emit_sound_fallback_goto(
                            ctx,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    }
                } else if let Some(ord_expr) =
                    slice_backing_cmp.as_ref().and_then(SliceBackingCmpResult::as_expr)
                {
                    let ord_expr = ord_expr.clone();
                    ord_expr
                } else if lhs.sort().is_array()
                    && rhs.sort().is_array()
                    && let Some(len) = array_len_from_operand(&args[0], ctx.body.locals())
                        .or_else(|| array_len_from_body_locals(&args[0], ctx.body.locals()))
                    && len <= MAX_LEXICO_LANES
                    && let Some(ord_expr) =
                        build_lexicographic_ord(&lhs, &rhs, len, method, is_signed)
                {
                    // Part of #3806: lexicographic ordering for fixed-size arrays (SIMD).
                    ord_expr
                } else if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
                    // Part of #3806/#4086: element-wise comparison for BV-sorted array operands.
                    let arr_len = array_len_from_operand(&args[0], ctx.body.locals())
                        .or_else(|| array_len_from_body_locals(&args[0], ctx.body.locals()));
                    // Part of #4086: try packed BV decomposition first (repr(simd) types).
                    let packed_ord = arr_len.and_then(|len| {
                        if len > MAX_LEXICO_LANES {
                            return None;
                        }
                        let ew = cmp_array::packed_simd_element_width(&args[0], ctx.body.locals())?;
                        let le = cmp_array::extract_packed_bv_elements(&lhs, len, ew)?;
                        let re = cmp_array::extract_packed_bv_elements(&rhs, len, ew)?;
                        build_lexicographic_ord_from_elements(&le, &re, method, is_signed)
                    });
                    if let Some(ord_expr) = packed_ord {
                        ord_expr
                    } else if let Some(len) = arr_len
                        && len <= MAX_LEXICO_LANES
                        && let Some(lhs_elems) = try_load_array_elements(ctx, &lhs, &args[0], len)
                        && let Some(rhs_elems) = try_load_array_elements(ctx, &rhs, &args[1], len)
                        && let Some(ord_expr) = build_lexicographic_ord_from_elements(
                            &lhs_elems, &rhs_elems, method, is_signed,
                        )
                    {
                        ord_expr
                    } else {
                        // Scalar BV comparison (non-array pointer types).
                        let Some(target_width) = ChcCtx::max_bitvec_width(&lhs, &rhs) else {
                            warn!(fn_name = %ctx.fn_name, method,
                                "CHC: ord bitvec width resolution failed");
                            emit_sound_fallback_goto(
                                ctx,
                                from_app,
                                target,
                                modified_locals,
                                &[dest_local],
                                stmt_constraints,
                            );
                            return;
                        };
                        let lhs = coerce_bitvec_width_safe(
                            lhs,
                            target_width,
                            SignExtension::for_signedness(is_signed),
                        );
                        let rhs = coerce_bitvec_width_safe(
                            rhs,
                            target_width,
                            SignExtension::for_signedness(is_signed),
                        );
                        match method {
                            "lt" => {
                                if is_signed {
                                    lhs.bvslt(rhs)
                                } else {
                                    lhs.bvult(rhs)
                                }
                            }
                            "le" => {
                                if is_signed {
                                    lhs.bvsle(rhs)
                                } else {
                                    lhs.bvule(rhs)
                                }
                            }
                            "gt" => {
                                if is_signed {
                                    lhs.bvsgt(rhs)
                                } else {
                                    lhs.bvugt(rhs)
                                }
                            }
                            "ge" => {
                                if is_signed {
                                    lhs.bvsge(rhs)
                                } else {
                                    lhs.bvuge(rhs)
                                }
                            }
                            _ => unreachable!(
                                "inner bitvec ord match: method '{method}' passed outer guard"
                            ),
                        }
                    }
                } else if lhs.sort().is_int() && rhs.sort().is_int() {
                    match method {
                        "lt" => lhs.int_lt(rhs),
                        "le" => lhs.int_le(rhs),
                        "gt" => lhs.int_gt(rhs),
                        "ge" => lhs.int_ge(rhs),
                        _ => unreachable!(
                            "inner int ord match: method '{method}' passed outer guard"
                        ),
                    }
                } else {
                    warn!(
                        fn_name = %ctx.fn_name,
                        method,
                        lhs_sort = ?lhs.sort(),
                        rhs_sort = ?rhs.sort(),
                        bb_idx,
                        "CHC: primitive ord unsupported sorts; destination left unconstrained"
                    );
                    emit_sound_fallback_goto(
                        ctx,
                        from_app,
                        target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                    return;
                }
            }
            // Part of #4008: Ord::{min, max} — return one of the operands.
            "min" | "max" => {
                let is_min = method == "min";
                if raw_pointer_ordering {
                    let cmp_method = if is_min { "le" } else { "ge" };
                    if let Some(cond) = raw_pointer_ord_expr_with_operands(
                        ctx,
                        &lhs_raw,
                        &rhs_raw,
                        &args[0],
                        &args[1],
                        cmp_method,
                        modified_locals,
                    ) {
                        Expr::ite(cond, lhs_raw, rhs_raw)
                    } else {
                        warn!(
                            fn_name = %ctx.fn_name,
                            method,
                            lhs_sort = ?lhs_raw.sort(),
                            rhs_sort = ?rhs_raw.sort(),
                            "CHC: raw-pointer min/max could not derive ordering keys"
                        );
                        emit_sound_fallback_goto(
                            ctx,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    }
                } else if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
                    let Some(target_width) = ChcCtx::max_bitvec_width(&lhs, &rhs) else {
                        warn!(fn_name = %ctx.fn_name, method, "CHC: min/max bitvec width failed");
                        emit_sound_fallback_goto(
                            ctx,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    };
                    let lhs = coerce_bitvec_width_safe(
                        lhs,
                        target_width,
                        SignExtension::for_signedness(is_signed),
                    );
                    let rhs = coerce_bitvec_width_safe(
                        rhs,
                        target_width,
                        SignExtension::for_signedness(is_signed),
                    );
                    let cond = if is_min {
                        if is_signed {
                            lhs.clone().bvsle(rhs.clone())
                        } else {
                            lhs.clone().bvule(rhs.clone())
                        }
                    } else if is_signed {
                        lhs.clone().bvsge(rhs.clone())
                    } else {
                        lhs.clone().bvuge(rhs.clone())
                    };
                    Expr::ite(cond, lhs, rhs)
                } else if lhs.sort().is_int() && rhs.sort().is_int() {
                    let cond = if is_min {
                        lhs.clone().int_le(rhs.clone())
                    } else {
                        lhs.clone().int_ge(rhs.clone())
                    };
                    Expr::ite(cond, lhs, rhs)
                } else {
                    warn!(fn_name = %ctx.fn_name, method, lhs_sort = ?lhs.sort(), rhs_sort = ?rhs.sort(),
                        "CHC: primitive min/max unsupported sorts");
                    emit_sound_fallback_goto(
                        ctx,
                        from_app,
                        target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                    return;
                }
            }
            // Part of #4008: Ord::clamp(self, min, max) — 3-arg ITE chain.
            "clamp" => {
                if args.len() < 3 {
                    warn!(fn_name = %ctx.fn_name, "CHC: clamp needs 3 args, got {}", args.len());
                    emit_sound_fallback_goto(
                        ctx,
                        from_app,
                        target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                    return;
                }
                // lhs = args[0] (self), rhs = args[1] (min) — both already resolved above
                let max_val = if raw_pointer_ordering {
                    resolve_raw_pointer_cmp_operand(ctx, &args[2], modified_locals)
                } else {
                    ctx.resolve_ref_or_const_referent(&args[2], modified_locals)
                };
                let min_val = rhs; // reuse already-resolved args[1]
                if let Some(max_val) = max_val {
                    if raw_pointer_ordering {
                        let Some(range_ok) = raw_pointer_ord_expr_with_operands(
                            ctx,
                            &rhs_raw,
                            &max_val,
                            &args[1],
                            &args[2],
                            "le",
                            modified_locals,
                        ) else {
                            warn!(
                                fn_name = %ctx.fn_name,
                                lhs_sort = ?rhs_raw.sort(),
                                rhs_sort = ?max_val.sort(),
                                "CHC: raw-pointer clamp bounds comparison could not derive ordering keys"
                            );
                            emit_sound_fallback_goto(
                                ctx,
                                from_app,
                                target,
                                modified_locals,
                                &[dest_local],
                                stmt_constraints,
                            );
                            return;
                        };
                        ctx.emit_error_rule_for_condition(
                            from_app,
                            range_ok.clone(),
                            stmt_constraints,
                            bb_idx,
                        );
                        extra_constraints.push(range_ok);
                        let Some(lt_min) = raw_pointer_ord_expr_with_operands(
                            ctx,
                            &lhs_raw,
                            &rhs_raw,
                            &args[0],
                            &args[1],
                            "lt",
                            modified_locals,
                        ) else {
                            warn!(
                                fn_name = %ctx.fn_name,
                                lhs_sort = ?lhs_raw.sort(),
                                rhs_sort = ?rhs_raw.sort(),
                                "CHC: raw-pointer clamp min comparison could not derive ordering keys"
                            );
                            emit_sound_fallback_goto(
                                ctx,
                                from_app,
                                target,
                                modified_locals,
                                &[dest_local],
                                stmt_constraints,
                            );
                            return;
                        };
                        let Some(gt_max) = raw_pointer_ord_expr_with_operands(
                            ctx,
                            &lhs_raw,
                            &max_val,
                            &args[0],
                            &args[2],
                            "gt",
                            modified_locals,
                        ) else {
                            warn!(
                                fn_name = %ctx.fn_name,
                                lhs_sort = ?lhs_raw.sort(),
                                rhs_sort = ?max_val.sort(),
                                "CHC: raw-pointer clamp max comparison could not derive ordering keys"
                            );
                            emit_sound_fallback_goto(
                                ctx,
                                from_app,
                                target,
                                modified_locals,
                                &[dest_local],
                                stmt_constraints,
                            );
                            return;
                        };
                        Expr::ite(lt_min, rhs_raw, Expr::ite(gt_max, max_val, lhs_raw))
                    } else if lhs.sort().is_bitvec()
                        && min_val.sort().is_bitvec()
                        && max_val.sort().is_bitvec()
                    {
                        let Some(target_width) = ChcCtx::max_bitvec_width(&lhs, &min_val)
                            .and_then(|w1| max_val.sort().bitvec_width().map(|w2| w1.max(w2)))
                        else {
                            warn!(fn_name = %ctx.fn_name, "CHC: clamp bitvec width failed");
                            emit_sound_fallback_goto(
                                ctx,
                                from_app,
                                target,
                                modified_locals,
                                &[dest_local],
                                stmt_constraints,
                            );
                            return;
                        };
                        let self_v = coerce_bitvec_width_safe(
                            lhs,
                            target_width,
                            SignExtension::for_signedness(is_signed),
                        );
                        let min_v = coerce_bitvec_width_safe(
                            min_val,
                            target_width,
                            SignExtension::for_signedness(is_signed),
                        );
                        let max_v = coerce_bitvec_width_safe(
                            max_val,
                            target_width,
                            SignExtension::for_signedness(is_signed),
                        );
                        let range_ok = if is_signed {
                            min_v.clone().bvsle(max_v.clone())
                        } else {
                            min_v.clone().bvule(max_v.clone())
                        };
                        ctx.emit_error_rule_for_condition(
                            from_app,
                            range_ok.clone(),
                            stmt_constraints,
                            bb_idx,
                        );
                        extra_constraints.push(range_ok);
                        let lt_min = if is_signed {
                            self_v.clone().bvslt(min_v.clone())
                        } else {
                            self_v.clone().bvult(min_v.clone())
                        };
                        let gt_max = if is_signed {
                            self_v.clone().bvsgt(max_v.clone())
                        } else {
                            self_v.clone().bvugt(max_v.clone())
                        };
                        Expr::ite(lt_min, min_v, Expr::ite(gt_max, max_v, self_v))
                    } else if lhs.sort().is_int()
                        && min_val.sort().is_int()
                        && max_val.sort().is_int()
                    {
                        let range_ok = min_val.clone().int_le(max_val.clone());
                        ctx.emit_error_rule_for_condition(
                            from_app,
                            range_ok.clone(),
                            stmt_constraints,
                            bb_idx,
                        );
                        extra_constraints.push(range_ok);
                        let lt_min = lhs.clone().int_lt(min_val.clone());
                        let gt_max = lhs.clone().int_gt(max_val.clone());
                        Expr::ite(lt_min, min_val, Expr::ite(gt_max, max_val, lhs))
                    } else {
                        warn!(fn_name = %ctx.fn_name, "CHC: clamp unsupported sorts");
                        emit_sound_fallback_goto(
                            ctx,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    }
                } else {
                    warn!(fn_name = %ctx.fn_name, "CHC: clamp operand resolution failed");
                    emit_sound_fallback_goto(
                        ctx,
                        from_app,
                        target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                    return;
                }
            }
            _ => {
                // non-enum: &str (method name)
                warn!(fn_name = %ctx.fn_name, method, "CHC: unexpected primitive cmp method");
                emit_sound_fallback_goto(
                    ctx,
                    from_app,
                    target,
                    modified_locals,
                    &[dest_local],
                    stmt_constraints,
                );
                return;
            }
        };

        // Part of #3182: check for flattened destination first.
        // partial_cmp returns Option<Ordering> which may be flattened into
        // (is_some, ordering_payload) slots. Direct slot constraining avoids
        // the decompose mismatch (cmp_result is a raw bitvec, not a Datatype).
        // Guard: only enter flattened path when field_count >= 2, otherwise
        // fall through to resolve_destination (audit fix: field_count < 2 gap).
        if is_partial
            && ctx.flatten.flattened_tuple_locals.contains(&dest_local)
            && ctx.flattened_field_count(dest_local) >= 2
            && let Some(vec_idx) = ctx.try_state_idx_for_local(dest_local)
        {
            let mut constraints = Vec::new();
            constraints.extend(extra_constraints);
            // Slot 0: is_some — partial_cmp on concrete bitvecs always returns Some.
            if let Some((out_name, out_sort)) =
                ctx.state_var_mgr.output_state_vars.get(vec_idx).cloned()
            {
                let is_some_var = Expr::var(&*out_name, out_sort.clone());
                let is_some_val = if out_sort.is_bool() {
                    Expr::bool_const(true)
                } else {
                    Expr::bitvec_const(1u64, out_sort.bitvec_width().unwrap_or(1))
                };
                ctx.encode.flattened_field_env.insert((dest_local, 0), is_some_val.clone());
                constraints.push(is_some_var.eq(is_some_val));
            }
            // Slot 1: ordering payload — coerce cmp_result to match slot width.
            if let Some((out_name, out_sort)) =
                ctx.state_var_mgr.output_state_vars.get(vec_idx + 1).cloned()
            {
                let payload_var = Expr::var(&*out_name, out_sort.clone());
                let coerced = if let Some(w) = out_sort.bitvec_width() {
                    coerce_bitvec_width_safe(cmp_result, w, SignExtension::SignExtend)
                } else {
                    cmp_result
                };
                ctx.encode.flattened_field_env.insert((dest_local, 1), coerced.clone());
                constraints.push(payload_var.eq(coerced));
            }
            if !constraints.is_empty() {
                let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
                ctx.emit_goto_rule_extra(
                    from_app,
                    target,
                    &new_output_args,
                    stmt_constraints,
                    constraints,
                );
            }
        } else if let Some(flat_constraints) =
            ctx.build_flattened_destination_constraints(dest_local, cmp_result.clone())
        {
            // Wide-pointer Ord helpers (`min`/`max`/`clamp`) return one operand
            // directly. When the destination local is flattened, route the raw
            // pointer/slice result through the shared decomposition helper so the
            // per-slot output vars receive `fld_ptr`/`fld_len` instead of
            // spuriously falling back through single-slot coercion.
            let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(
                from_app,
                target,
                &new_output_args,
                stmt_constraints,
                extra_constraints.into_iter().chain(flat_constraints),
            );
        } else if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let out_sort = dest_var.sort();
            let final_result = if *cmp_result.sort() == *out_sort {
                Some(cmp_result)
            } else if is_partial && out_sort.is_datatype() {
                // Part of #1229: use actual inner sort width from Option payload.
                // If inner payload is not a bitvec, or is not Ordering-compatible
                // width (8/32), return None and fall through to the unconstrained
                // path rather than silently guessing width.
                option_value_sort(out_sort)
                    .and_then(|s| s.bitvec_width())
                    .filter(|inner_width| *inner_width == 8 || *inner_width == 32)
                    .map(|inner_width| {
                        coerce_bitvec_width_safe(cmp_result, inner_width, SignExtension::SignExtend)
                    })
                    .and_then(|bv| ctx.make_some_expr_for_option(bv, out_sort))
            } else if cmp_result.sort().is_bool() {
                if out_sort.is_bool() {
                    Some(cmp_result)
                } else {
                    out_sort.bitvec_width().map(|w| {
                        Expr::ite(cmp_result, Expr::bitvec_const(1, w), Expr::bitvec_const(0, w))
                    })
                }
            } else {
                out_sort
                    .bitvec_width()
                    .map(|w| coerce_bitvec_width_safe(cmp_result, w, SignExtension::SignExtend))
            };
            if let Some(converted) = final_result {
                let eq = ctx.make_coerced_eq_constraint(
                    &dest_var,
                    converted,
                    out_sort,
                    dest_local,
                    "codegen_call_primitive_cmp",
                );
                let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
                ctx.emit_goto_rule_extra(
                    from_app,
                    target,
                    &new_output_args,
                    stmt_constraints,
                    extra_constraints.into_iter().chain(eq),
                );
            } else {
                warn!(
                    fn_name = %ctx.fn_name,
                    dest_local,
                    is_partial,
                    "CHC: codegen_call_primitive_cmp sort conversion failed — \
                     destination left unconstrained"
                );
                // Part of #2773 follow-up: self-audit found missing record_fallback().
                emit_sound_fallback_goto(
                    ctx,
                    from_app,
                    target,
                    modified_locals,
                    &[dest_local],
                    stmt_constraints,
                );
            }
        } else {
            // Part of #2773 follow-up: output_state_vars missing for dest.
            warn!(
                fn_name = %ctx.fn_name,
                dest_local,
                "CHC: codegen_call_primitive_cmp output state var missing; destination left unconstrained"
            );
            emit_sound_fallback_goto(
                ctx,
                from_app,
                target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
        }
    } else {
        // Part of #2773 follow-up: operand resolution failed.
        warn!(
            fn_name = %ctx.fn_name,
            "CHC: codegen_call_primitive_cmp operand resolution failed; destination left unconstrained"
        );
        emit_sound_fallback_goto(
            ctx,
            from_app,
            target,
            modified_locals,
            &[dest_local],
            stmt_constraints,
        );
    }
}

/// Extract the array data from a Slice Datatype expression.
///
/// Slice_* Datatypes have a `fld_data` field with Array sort.
/// Returns `None` for non-Slice sorts or if `fld_data` is not found.
///
/// Part of #3806: enables CHC comparison handlers to operate on the
/// underlying array data when operands are Slice Datatypes from Unsize coercion.
fn extract_slice_array_data(expr: &Expr) -> Option<Expr> {
    if expr.sort().is_array() {
        return None; // already array
    }
    let dt = expr.sort().datatype_sort()?;
    if !dt.name.starts_with("Slice_") || dt.constructors.len() != 1 {
        return None;
    }
    let cons = &dt.constructors[0];
    let data_field = cons.fields.iter().find(|f| &*f.name == "fld_data")?;
    if !data_field.sort.is_array() {
        return None;
    }
    Some(expr.clone().field_select(&*dt.name, "fld_data", data_field.sort.clone()))
}

/// Part of #4086: Extract inner Array from single-field Datatype wrappers.
///
/// User-defined `#[repr(simd)]` types like `i64x2([i64; 2])` are translated
/// as bare Array sorts by `translate_ty`, but aggregate construction may
/// produce Datatype-wrapped values when the type name doesn't contain "simd".
/// This function unwraps `DT_mk(fld_0: Array(...))` to the inner Array,
/// enabling lexicographic comparison in the CMP handler.
fn extract_single_field_array_wrapper(expr: &Expr) -> Option<Expr> {
    if expr.sort().is_array() {
        return None; // already array
    }
    let dt = expr.sort().datatype_sort()?;
    if dt.constructors.len() != 1 {
        return None;
    }
    let cons = &dt.constructors[0];
    if cons.fields.len() != 1 {
        return None;
    }
    let field = &cons.fields[0];
    if !field.sort.is_array() {
        return None;
    }
    Some(expr.clone().field_select(&*dt.name, &*field.name, field.sort.clone()))
}
