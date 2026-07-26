// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Step::forward_unchecked/backward_unchecked, wrapping, checked, and saturating
//! arithmetic handlers.
//!
//! Extracted from codegen_call_cmp_string.rs — Part of #2408.
//! Checked/saturating arithmetic added — Part of #3094.

use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe, ty_to_bv_width};
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, BinOp};
use tracing::{debug, warn};

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{emit_sound_fallback_goto, try_emit_precise_call_result};
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_expr_signedness::{ExprSignedness, arg_signedness_or_fallback};
use crate::codegen_ay::shared::SignednessFallbackKind;

// Saturating and overflowing arithmetic moved to step_saturating.rs per #4206.
pub(in crate::codegen_ay::chc) use super::step_saturating::{
    codegen_overflowing_add_signed, codegen_overflowing_arithmetic, codegen_saturating_arithmetic,
};

pub(super) fn reshape_flattened_result_field(
    ctx: &ChcCtx<'_, '_>,
    dest_local: usize,
    field_idx: usize,
    value: Expr,
    is_signed: bool,
) -> Expr {
    let Some(vec_idx) = ctx.try_state_idx_for_local(dest_local) else {
        return value;
    };
    let Some((_, out_sort)) = ctx.state_var_mgr.output_state_vars.get(vec_idx + field_idx) else {
        return value;
    };

    if *value.sort() == *out_sort {
        value
    } else if out_sort.is_int() && value.sort().is_bitvec() {
        if is_signed { value.bv2int_signed() } else { value.bv2int() }
    } else if value.sort().is_bitvec()
        && out_sort.is_bitvec()
        && let Some(width) = out_sort.bitvec_width()
    {
        coerce_bitvec_width_safe(value, width, SignExtension::for_signedness(is_signed))
    } else {
        value
    }
}

/// Handle `Step::forward_unchecked` / `Step::backward_unchecked` calls.
///
/// `is_forward`: true for forward_unchecked, false for backward_unchecked.
pub(in crate::codegen_ay::chc) fn codegen_step_unchecked(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    is_forward: bool,
) {
    let args = dcx.args;
    let destination = dcx.destination;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let bb_idx = dcx.bb_idx;
    let dest_local: usize = destination.local;
    let lhs = ctx.resolve_ref_or_const_referent(&args[0], modified_locals);
    let rhs = ctx.resolve_ref_or_const_referent(&args[1], modified_locals);

    // Part of #3561: labeled block collapses 3 fallback sites into 1 (inside try_emit).
    let step_result: Option<Expr> = 'compute: {
        let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
            break 'compute None;
        };
        let is_signed = arg_signedness_or_fallback(
            &args[0],
            ctx.body.locals(),
            "step_unchecked",
            SignednessFallbackKind::Arithmetic,
        );
        if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
            let Some(target_width) = ChcCtx::max_bitvec_width(&lhs, &rhs) else {
                break 'compute None;
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
            // Part of #3406: Step::forward/backward_unchecked have UB on overflow.
            // Emit error rule: from_rel(state) ∧ constraints ∧ ¬no_overflow → error().
            let no_overflow = if is_forward {
                if is_signed {
                    lhs.clone().bvadd_no_overflow_signed(rhs.clone())
                } else {
                    lhs.clone().bvadd_no_overflow_unsigned(rhs.clone())
                }
            } else if is_signed {
                lhs.clone().bvsub_no_overflow_signed(rhs.clone())
            } else {
                lhs.clone().bvsub_no_underflow_unsigned(rhs.clone())
            };
            ctx.emit_error_rule_for_condition(from_app, no_overflow, stmt_constraints, bb_idx);
            Some(if is_forward { lhs.bvadd(rhs) } else { lhs.bvsub(rhs) })
        } else if lhs.sort().is_int() && rhs.sort().is_int() {
            Some(if is_forward { lhs.int_add(rhs) } else { lhs.int_sub(rhs) })
        } else {
            None
        }
    };

    // Part of #3561: consolidated resolve→coerce→emit tail.
    try_emit_precise_call_result(
        ctx,
        step_result,
        dest_local,
        from_app,
        target,
        modified_locals,
        stmt_constraints,
        [],
        "codegen_call_step_unchecked",
    );
}

/// Handle wrapping/unchecked arithmetic: wrapping_add/sub/mul → bvadd/bvsub/bvmul (#2210).
///
/// When `is_unchecked` is true, also emits an overflow error rule:
/// `from_rel(state) ∧ constraints ∧ overflow → error()`.
/// Unchecked arithmetic (e.g. `u8::unchecked_add`) has UB on overflow,
/// so the solver must detect it. Part of #3299.
pub(in crate::codegen_ay::chc) fn codegen_wrapping_arithmetic(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    arith_op: BinOp,
    is_unchecked: bool,
) {
    let args = dcx.args;
    let destination = dcx.destination;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let bb_idx = dcx.bb_idx;
    let dest_local: usize = destination.local;
    let lhs = ctx.resolve_ref_or_const_referent(&args[0], modified_locals);
    let rhs = ctx.resolve_ref_or_const_referent(&args[1], modified_locals);

    let mut normal_guards = Vec::new();

    // Part of #3561: labeled block collapses 4 fallback sites into 1 (inside try_emit).
    let result: Option<Expr> = 'compute: {
        let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
            break 'compute None;
        };
        // Part of #3530: Int-lifted operands need coercion to BV for wrapping arithmetic.
        let (lhs, rhs) = if lhs.sort().is_int() || rhs.sort().is_int() {
            let w = ty_to_bv_width(ctx.body.locals()[dest_local].ty)
                .unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);
            let lhs = if lhs.sort().is_int() { lhs.int2bv(w) } else { lhs };
            let rhs = if rhs.sort().is_int() { rhs.int2bv(w) } else { rhs };
            (lhs, rhs)
        } else {
            (lhs, rhs)
        };
        if !lhs.sort().is_bitvec() || !rhs.sort().is_bitvec() {
            break 'compute None;
        }
        let Some(value_width) = lhs.sort().bitvec_width() else {
            break 'compute None;
        };
        let Some(shift_width) = rhs.sort().bitvec_width() else {
            break 'compute None;
        };
        let is_signed = arg_signedness_or_fallback(
            &args[0],
            ctx.body.locals(),
            "wrapping_arith",
            SignednessFallbackKind::Arithmetic,
        );
        let Some(target_width) = ChcCtx::max_bitvec_width(&lhs, &rhs) else {
            break 'compute None;
        };
        let lhs =
            coerce_bitvec_width_safe(lhs, target_width, SignExtension::for_signedness(is_signed));
        let rhs =
            coerce_bitvec_width_safe(rhs, target_width, SignExtension::for_signedness(is_signed));

        // Part of #3299: unchecked arithmetic has UB on overflow.
        // Emit error rule: from_rel(state) ∧ constraints ∧ ¬no_overflow → error().
        if is_unchecked {
            let no_overflow = match arith_op {
                BinOp::Add if is_signed => lhs.clone().bvadd_no_overflow_signed(rhs.clone()),
                BinOp::Add => lhs.clone().bvadd_no_overflow_unsigned(rhs.clone()),
                BinOp::Sub if is_signed => lhs.clone().bvsub_no_overflow_signed(rhs.clone()),
                BinOp::Sub => lhs.clone().bvsub_no_underflow_unsigned(rhs.clone()),
                BinOp::Mul if is_signed => lhs.clone().bvmul_no_overflow_signed(rhs.clone()),
                BinOp::Mul => lhs.clone().bvmul_no_overflow_unsigned(rhs.clone()),
                // Div/Rem UB: division by zero, or signed MIN / -1 overflow.
                BinOp::Div | BinOp::Rem => {
                    let zero = Expr::bitvec_const(0u64, target_width);
                    let rhs_nonzero = rhs.clone().eq(zero).not();
                    if is_signed {
                        let t_min = Expr::bitvec_const(1u128 << (target_width - 1), target_width);
                        let neg_one =
                            Expr::bitvec_const(!0u128 >> (128 - target_width), target_width);
                        let signed_overflow = lhs.clone().eq(t_min).and(rhs.clone().eq(neg_one));
                        rhs_nonzero.and(signed_overflow.not())
                    } else {
                        rhs_nonzero
                    }
                }
                // Shl/Shr UB: shift amount must be in [0, value_width).
                // The result expression may use widened operands for BV
                // compatibility, but the unchecked shift contract is defined
                // by the LHS type.
                BinOp::Shl | BinOp::Shr => {
                    let rhs_signed = ctx.operand_signedness(&args[1]).unwrap_or(false);
                    let compare_width = value_width.max(shift_width);
                    let rhs_cmp = coerce_bitvec_width_safe(
                        rhs.clone(),
                        compare_width,
                        SignExtension::for_signedness(rhs_signed),
                    );
                    let width_const = Expr::bitvec_const(value_width as u64, compare_width);
                    let in_range = rhs_cmp.clone().bvult(width_const);
                    if rhs_signed {
                        let zero = Expr::bitvec_const(0u64, compare_width);
                        in_range.and(rhs_cmp.bvsge(zero))
                    } else {
                        in_range
                    }
                }
                _ => {
                    // external enum: BinOp — unknown unchecked op, skip UB check
                    warn!(fn_name = %ctx.fn_name, ?arith_op, "CHC: unknown unchecked arith op for UB check");
                    Expr::bool_const(true)
                }
            };
            ctx.emit_error_rule_for_condition(
                from_app,
                no_overflow.clone(),
                stmt_constraints,
                bb_idx,
            );
            normal_guards.push(no_overflow);
        }

        match arith_op {
            BinOp::Add => Some(lhs.bvadd(rhs)),
            BinOp::Sub => Some(lhs.bvsub(rhs)),
            BinOp::Mul => Some(lhs.bvmul(rhs)),
            BinOp::Div if is_signed => Some(lhs.bvsdiv(rhs)),
            BinOp::Div => Some(lhs.bvudiv(rhs)),
            BinOp::Rem if is_signed => Some(lhs.bvsrem(rhs)),
            BinOp::Rem => Some(lhs.bvurem(rhs)),
            BinOp::Shl => Some(lhs.bvshl(rhs)),
            BinOp::Shr if is_signed => Some(lhs.bvashr(rhs)),
            BinOp::Shr => Some(lhs.bvlshr(rhs)),
            _ => {
                warn!(fn_name = %ctx.fn_name, ?arith_op, "CHC: unexpected wrapping arithmetic op");
                None
            }
        }
    };

    // Part of #3561: consolidated resolve→coerce→emit tail.
    // coerce_eq_constraint handles BV→BV width, BV→Int, Int→BV coercion.
    try_emit_precise_call_result(
        ctx,
        result,
        dest_local,
        from_app,
        target,
        modified_locals,
        stmt_constraints,
        normal_guards,
        "codegen_call_wrapping_arithmetic",
    );
}

/// Handle checked arithmetic: checked_add/sub/mul/div/rem/shl/shr → Option<T> (Part of #3094, #3463).
///
/// `checked_*` methods return `Some(result)` when no overflow, `None` on overflow.
/// The destination is typically a flattened `Option<T>`:
/// - field 0: discriminant (is_some = !overflow)
/// - field 1: payload (wrapping result)
///
/// Uses `translate_checked_binop_flat` to compute (result, overflow) with proper
/// signed/unsigned overflow detection, then constrains the flattened output slots.
pub(in crate::codegen_ay::chc) fn codegen_checked_arithmetic(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    arith_op: BinOp,
) {
    let args = dcx.args;
    let destination = dcx.destination;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let bb_idx = dcx.bb_idx;
    let dest_local: usize = destination.local;
    let lhs = ctx.resolve_ref_or_const_referent(&args[0], modified_locals);
    let rhs = ctx.resolve_ref_or_const_referent(&args[1], modified_locals);

    // Part of #3561: labeled block collapses checked-arithmetic fallback exits into 1.
    let emitted: bool = 'compute: {
        let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
            break 'compute false;
        };
        let is_signed = arg_signedness_or_fallback(
            &args[0],
            ctx.body.locals(),
            "checked_arith",
            SignednessFallbackKind::Arithmetic,
        );
        // Derive BV width from first argument's MIR type (Part of #3043).
        // Part of #3243: fall through to sound fallback on type resolution failure.
        let Some(int_bv_width) = args[0].ty(ctx.body.locals()).ok().and_then(ty_to_bv_width) else {
            break 'compute false;
        };

        let Some((result, overflow)) =
            ctx.translate_checked_binop_flat(arith_op, lhs, rhs, is_signed, int_bv_width)
        else {
            break 'compute false;
        };
        // Option<T> flattened: discriminant (is_some) + payload.
        if !(ctx.flatten.flattened_tuple_locals.contains(&dest_local)
            && ctx.flattened_field_count(dest_local) >= 2)
        {
            // Non-flattened destination — sound over-approximation.
            debug!("checked arithmetic non-flattened dest (bb{}->bb{})", bb_idx, target);
            break 'compute false;
        }
        let field_values = [
            Some(ctx.reshape_flattened_bool_field_for_call(dest_local, 0, overflow.not())),
            Some(reshape_flattened_result_field(ctx, dest_local, 1, result, is_signed)),
        ];
        ctx.emit_flattened_call_fields(
            dest_local,
            &field_values,
            from_app,
            target,
            modified_locals,
            stmt_constraints,
        )
    };

    if !emitted {
        // Fallback: args not resolved, translate failed, or non-flattened dest.
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
