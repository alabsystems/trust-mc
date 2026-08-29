// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Math intrinsic CHC handler: constant-fold f32/f64 math intrinsics (Part of #3373).
//!
//! The CHC call dispatch chain had no handler for math intrinsics (floor, ceil,
//! round, trunc, round_ties_even, sqrt, sin, cos, etc.). These fell through to
//! the `unhandled_call` catch-all, leaving destinations unconstrained.
//!
//! The BMC path already handles these via `dispatch_math()` in
//! `statement/dispatch/intrinsic/math.rs` with constant folding in
//! `statement/intrinsics/math.rs`.
//!
//! This module adds the same constant-folding capability to the CHC path:
//! - Detect math intrinsics via callee path suffix matching
//! - Extract constant float args from MIR `Operand::Constant` or `Copy/Move`
//!   of locals assigned a constant (MIR body scan)
//! - Fold at compile time (identical to BMC)
//! - Emit CHC rule with dest constrained to the constant result
//! - Non-constant args: sound over-approximation (unconstrained)

use ay_bindings::Expr;
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_call_fallback_emit::{
    emit_math_axiom_goto_extra, emit_sound_fallback_goto_extra,
};
use super::super::codegen_rules::CodegenRules;
use super::math_axioms;
use super::math_const::{
    try_extract_const_f32_with_ctx, try_extract_const_f64_with_ctx, try_extract_const_i32_with_ctx,
    try_fold_f32_intrinsic, try_fold_f64_intrinsic,
};
use super::math_range_axioms;

/// Suffix lists for f32 math intrinsics (same as BMC's `is_f32_math_intrinsic`).
pub(crate) const F32_SUFFIXES: &[&str] = &[
    "sqrtf32",
    "sinf32",
    "cosf32",
    "expf32",
    "logf32",
    "exp2f32",
    "log2f32",
    "log10f32",
    "powf32",
    "powif32",
    "fabsf32",
    "copysignf32",
    "floorf32",
    "ceilf32",
    "truncf32",
    "roundf32",
    "round_ties_even_f32",
    "fmaf32",
    "minnumf32",
    "maxnumf32",
];

/// Suffix lists for f64 math intrinsics (same as BMC's `is_f64_math_intrinsic`).
pub(crate) const F64_SUFFIXES: &[&str] = &[
    "sqrtf64",
    "sinf64",
    "cosf64",
    "expf64",
    "logf64",
    "exp2f64",
    "log2f64",
    "log10f64",
    "powf64",
    "powif64",
    "fabsf64",
    "copysignf64",
    "floorf64",
    "ceilf64",
    "truncf64",
    "roundf64",
    "round_ties_even_f64",
    "fmaf64",
    "minnumf64",
    "maxnumf64",
];

/// Method-call-form names for math functions that MIR inlining may produce.
/// When `f32::fract()` is MIR-inlined to `x - f32::trunc(x)`, the `trunc`
/// call appears as `core::f32::math::trunc` (not `intrinsics::truncf32`).
/// This table maps method names to (intrinsic_f32_suffix, intrinsic_f64_suffix).
const METHOD_MATH_NAMES: &[(&str, &str, &str)] = &[
    ("sin", "sinf32", "sinf64"),
    ("cos", "cosf32", "cosf64"),
    ("exp", "expf32", "expf64"),
    ("exp2", "exp2f32", "exp2f64"),
    ("log", "logf32", "logf64"),
    ("log2", "log2f32", "log2f64"),
    ("log10", "log10f32", "log10f64"),
    ("powf", "powf32", "powf64"),
    ("powi", "powif32", "powif64"),
    ("mul_add", "fmaf32", "fmaf64"),
    ("trunc", "truncf32", "truncf64"),
    ("floor", "floorf32", "floorf64"),
    ("ceil", "ceilf32", "ceilf64"),
    ("round", "roundf32", "roundf64"),
    ("round_ties_even", "round_ties_even_f32", "round_ties_even_f64"),
    ("sqrt", "sqrtf32", "sqrtf64"),
    ("abs", "fabsf32", "fabsf64"),
    ("copysign", "copysignf32", "copysignf64"),
];

/// Detect whether a callee path is a math intrinsic.
/// Returns `Some(true)` for f32, `Some(false)` for f64, `None` otherwise.
///
/// Matches both intrinsic forms (`std::intrinsics::truncf32`) and method-call
/// forms produced by MIR inlining (`core::f32::math::trunc`).
pub(crate) fn detect_math_intrinsic(path: &str) -> Option<bool> {
    if F32_SUFFIXES.iter().any(|s| path.ends_with(s)) {
        Some(true) // f32
    } else if F64_SUFFIXES.iter().any(|s| path.ends_with(s)) {
        Some(false) // f64
    } else {
        detect_method_call_math(path)
    }
}

/// Detect method-call-form math functions (e.g., `core::f32::math::trunc`).
/// Returns `Some(true)` for f32 methods, `Some(false)` for f64, `None` otherwise.
fn detect_method_call_math(path: &str) -> Option<bool> {
    let method = path.rsplit("::").next()?;
    for &(method_name, _, _) in METHOD_MATH_NAMES {
        if method == method_name {
            if path.contains("f32") {
                return Some(true);
            } else if path.contains("f64") {
                return Some(false);
            }
        }
    }
    None
}

/// Normalize a callee path to its intrinsic suffix form.
/// Converts method-call forms (e.g., `core::f32::math::trunc`) to intrinsic
/// suffixes (`truncf32`) so that existing `ends_with` matching in
/// `try_exact_unary_encoding` works without duplication.
pub(crate) fn normalize_to_intrinsic_suffix(path: &str) -> Option<String> {
    let method = path.rsplit("::").next()?;
    for &(method_name, f32_suffix, f64_suffix) in METHOD_MATH_NAMES {
        if method == method_name {
            if path.contains("f32") {
                return Some(f32_suffix.to_string());
            } else if path.contains("f64") {
                return Some(f64_suffix.to_string());
            }
        }
    }
    None
}

/// Handle a math intrinsic call in the CHC path (Part of #3373).
///
/// Constant-folds the intrinsic if all arguments are compile-time constants.
/// Otherwise, emits sound over-approximation (destination unconstrained).
pub(in crate::codegen_ay::chc) fn codegen_math_intrinsic(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: rustc_public::mir::BasicBlockIdx,
    callee_path: &str,
    is_f32: bool,
) {
    // Normalize method-call forms (e.g., core::f32::math::trunc) to intrinsic
    // suffix forms (truncf32) so downstream matching (constant folding, exact
    // BV encoding) works without duplication. Part of #3688.
    let normalized;
    let callee_path = if let Some(suffix) = normalize_to_intrinsic_suffix(callee_path) {
        normalized = suffix;
        normalized.as_str()
    } else {
        callee_path
    };

    let dest_local: usize = dcx.destination.local;
    let modified_locals = dcx.modified_locals;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let bb_idx = dcx.bb_idx;

    // Try constant folding based on float width.
    let folded_result = if is_f32 {
        try_fold_f32_intrinsic(ctx, callee_path, dcx.args, modified_locals)
            .map(|bits| Expr::bitvec_const(bits as u128, 32))
    } else {
        try_fold_f64_intrinsic(ctx, callee_path, dcx.args, modified_locals)
            .map(|bits| Expr::bitvec_const(bits as u128, 64))
    };

    if let Some(result_expr) = folded_result {
        // Constant folded — emit rule with dest constrained to constant.
        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            // Part of #3839: Record the constant-folded result for cross-block
            // propagation. The target block's clear_block() seeds local_expr_env
            // from this map, allowing downstream float operations (Sub, Abs,
            // comparison) to constant-fold through the full assertion chain.
            ctx.encode.const_folded_call_results.insert(dest_local, result_expr.clone());
            let eq = ctx.make_coerced_eq_constraint(
                &dest_var,
                result_expr,
                dest_var.sort(),
                dest_local,
                "codegen_math_intrinsic",
            );
            let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(from_app, target, &new_output_args, stmt_constraints, eq);
            debug!(
                callee = callee_path,
                is_f32, "math intrinsic constant-folded (bb{}->bb{})", bb_idx, target
            );
            return;
        }
    }

    // Non-constant — try exact BV encoding first, then axiom fallback (Part of #3323).
    let width = if is_f32 { 32u32 } else { 64u32 };

    // Tier 1: Exact BV encoding for intrinsics with bit-level definitions.
    // These produce precise `dest = f(input)` constraints, not over-approximations.
    // Unary exact encoding (fabs).
    if let Some(input_expr) = ctx.translate_operand_with_modified(&dcx.args[0], modified_locals)
        && let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
    {
        if let Some(exact_result) =
            math_axioms::try_exact_unary_encoding(callee_path, &input_expr, width)
        {
            let eq = ctx.make_coerced_eq_constraint(
                &dest_var,
                exact_result,
                dest_var.sort(),
                dest_local,
                "codegen_math_exact_unary",
            );
            let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(from_app, target, &new_output_args, stmt_constraints, eq);
            debug!(
                callee = callee_path,
                is_f32, "math intrinsic exact BV encoding (bb{}->bb{})", bb_idx, target
            );
            return;
        }
    }
    // Binary exact encoding (copysign).
    if dcx.args.len() >= 2
        && let Some(arg0_expr) = ctx.translate_operand_with_modified(&dcx.args[0], modified_locals)
        && let Some(arg1_expr) = ctx.translate_operand_with_modified(&dcx.args[1], modified_locals)
        && let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
    {
        if let Some(exact_result) =
            math_axioms::try_exact_binary_encoding(callee_path, &arg0_expr, &arg1_expr, width)
        {
            let eq = ctx.make_coerced_eq_constraint(
                &dest_var,
                exact_result,
                dest_var.sort(),
                dest_local,
                "codegen_math_exact_binary",
            );
            let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(from_app, target, &new_output_args, stmt_constraints, eq);
            debug!(
                callee = callee_path,
                is_f32, "math intrinsic exact BV encoding (bb{}->bb{})", bb_idx, target
            );
            return;
        }
    }

    // CONGRUENCE (Part of #4270 / TL18). Every tier below leaves the result a
    // fresh havoc, so the encoder could not prove `sin(x) == sin(x)` — the two
    // sites got independent values. Bind the destination to a select over the
    // frozen, never-constrained `call_uf_tbl` instead: still universally
    // quantified (for a fixed key the ∀-table ranges over every value, so no
    // behaviour is removed), but now EQUAL at equal arguments, which is what
    // the real function does. Purity is established by the intrinsic's
    // specification — see `call_uf_table::math_uf_summary_term`.
    let uf_congruence: Option<Expr> = math_uf_congruence(ctx, dcx, callee_path, dest_local);

    // Tier 2: Sound range axioms for transcendental intrinsics (Part of #3609).
    // Constrains symbolic results to valid ranges (e.g. sin in [-1,1], sqrt >= 0).
    if let Some(input_expr) = ctx.translate_operand_with_modified(&dcx.args[0], modified_locals)
        && let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
    {
        let mut axioms =
            math_range_axioms::emit_range_axioms(callee_path, &input_expr, &dest_var, width);
        if !axioms.is_empty() {
            axioms.extend(uf_congruence.clone());
            emit_math_axiom_goto_extra(
                ctx,
                from_app,
                target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
                axioms,
            );
            debug!(
                callee = callee_path,
                is_f32, "math intrinsic range-axiom constrained (bb{}->bb{})", bb_idx, target
            );
            return;
        }
    }

    // Tier 2 (binary): Even-power non-negativity for powf/powi (Part of #3609 D2).
    let is_pow = callee_path.ends_with("powf32")
        || callee_path.ends_with("powf64")
        || callee_path.ends_with("powif32")
        || callee_path.ends_with("powif64");
    if is_pow && dcx.args.len() >= 2 {
        let is_even = if callee_path.ends_with("powif32") || callee_path.ends_with("powif64") {
            try_extract_const_i32_with_ctx(ctx, &dcx.args[1], modified_locals)
                .is_some_and(|e| e != 0 && e % 2 == 0)
        } else if is_f32 {
            try_extract_const_f32_with_ctx(ctx, &dcx.args[1], modified_locals).is_some_and(|bits| {
                let val = f32::from_bits(bits);
                val > 0.0 && val == val.floor() && (val as i64) % 2 == 0
            })
        } else {
            try_extract_const_f64_with_ctx(ctx, &dcx.args[1], modified_locals).is_some_and(|bits| {
                let val = f64::from_bits(bits);
                val > 0.0 && val == val.floor() && (val as i64) % 2 == 0
            })
        };
        if is_even {
            if let Some(input_expr) =
                ctx.translate_operand_with_modified(&dcx.args[0], modified_locals)
                && let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
            {
                let mut axioms =
                    math_range_axioms::emit_power_nonneg_axiom(&input_expr, &dest_var, width);
                if !axioms.is_empty() {
                    axioms.extend(uf_congruence.clone());
                    emit_math_axiom_goto_extra(
                        ctx,
                        from_app,
                        target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                        axioms,
                    );
                    debug!(
                        callee = callee_path,
                        is_f32, "math intrinsic even-power axiom (bb{}->bb{})", bb_idx, target
                    );
                    return;
                }
            }
        }
    }

    // Tier 3: no range axiom for this intrinsic (log, tan, powf with a symbolic
    // exponent, …). The destination stays unconstrained apart from congruence,
    // and the pre-existing fail-closed `call_dispatch_fallback` reason is
    // recorded unchanged — this tier is a precision refinement only.
    debug!(
        callee = callee_path,
        is_f32,
        congruent = uf_congruence.is_some(),
        "math intrinsic fallback to unconstrained (bb{}->bb{})",
        bb_idx,
        target
    );
    emit_sound_fallback_goto_extra(
        ctx,
        from_app,
        target,
        modified_locals,
        &[dest_local],
        stmt_constraints,
        uf_congruence,
    );
}

/// `dest == select(call_uf_tbl, tag(f) ++ args)` for a pure math intrinsic, or
/// `None` when the table was not declared for this harness, an argument does
/// not translate, or the key/value widths do not fit (never truncated — a
/// colliding key would assert an equality that need not hold).
fn math_uf_congruence(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    callee_path: &str,
    dest_local: usize,
) -> Option<Expr> {
    if !ctx.call_uf_table_declared() {
        return None;
    }
    let mut arg_exprs: Vec<Expr> = Vec::with_capacity(dcx.args.len());
    for arg in dcx.args {
        arg_exprs.push(ctx.translate_operand_with_modified(arg, dcx.modified_locals)?);
    }
    let (_, dest_var) = ctx.resolve_destination(dest_local)?;
    let out_sort = dest_var.sort().clone();
    let term = ctx.math_uf_summary_term(callee_path, &arg_exprs, &out_sort)?;
    Some(dest_var.eq(term))
}
