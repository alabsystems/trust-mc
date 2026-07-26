// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Saturating and overflowing arithmetic handlers.
//!
//! - `codegen_saturating_arithmetic`: saturating add/sub (clamped to MIN/MAX on overflow)
//! - `codegen_overflowing_arithmetic`: `overflowing_*` / `*_with_overflow` tuple results
//! - `codegen_overflowing_add_signed`: `overflowing_add_signed` (ptr.offset lowering)
//!
//! Extracted from `step_wrapping.rs` — Part of #4206.

use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe, ty_to_bv_width};
use ay_bindings::Expr;
use num_bigint::BigInt;
use rustc_public::mir::{BasicBlockIdx, BinOp};
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{emit_sound_fallback_goto, try_emit_precise_call_result};
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_expr_signedness::arg_signedness_or_fallback;
use super::step_wrapping::reshape_flattened_result_field;
use crate::codegen_ay::shared::SignednessFallbackKind;

fn saturating_bound_expr(
    lhs: &Expr,
    result: &Expr,
    arith_op: BinOp,
    is_signed: bool,
    int_bv_width: u32,
) -> Option<Expr> {
    if result.sort().is_bitvec() {
        let w = result.sort().bitvec_width()?;
        if is_signed {
            // Part of #3403: Use BigInt to avoid i128 overflow at width=128.
            let half = BigInt::from(1u128) << (w - 1);
            let max_val = Expr::bitvec_const(&half - 1, w); // 0111...1
            let min_val = Expr::bitvec_const(-half, w); // 1000...0
            let lhs_positive = if lhs.sort().is_bitvec() {
                lhs.clone().extract(w - 1, w - 1).eq(Expr::bitvec_const(0, 1))
            } else {
                // Int-lifted lhs: check >= 0
                lhs.clone().int_ge(Expr::int_const(0))
            };
            Some(Expr::ite(lhs_positive, max_val, min_val))
        } else {
            match arith_op {
                BinOp::Add => Some(Expr::bitvec_const(-1i128, w)), // all ones = MAX for unsigned
                BinOp::Sub => Some(Expr::bitvec_const(0, w)),      // 0 = MIN for unsigned
                _ => None,
            }
        }
    } else if result.sort().is_int() {
        if is_signed {
            // Part of #3403: Use BigInt to avoid i128 overflow at width=128.
            let half = BigInt::from(1u128) << (int_bv_width - 1);
            let max_val = Expr::int_const(&half - 1);
            let min_val = Expr::int_const(-half);
            let lhs_positive = lhs.clone().int_ge(Expr::int_const(0));
            Some(Expr::ite(lhs_positive, max_val, min_val))
        } else {
            match arith_op {
                // Part of #3403: Use BigInt to avoid shift-width UB at width=128.
                BinOp::Add => Some(Expr::int_const((BigInt::from(1u128) << int_bv_width) - 1)),
                BinOp::Sub => Some(Expr::int_const(0)),
                _ => None,
            }
        }
    } else {
        None
    }
}

/// Handle `saturating_add`, `saturating_sub`, etc.
///
/// `saturating_*` methods return the wrapping result clamped to `T::MIN`/`T::MAX`
/// on overflow: `ite(overflow, saturation_bound, wrapping_result)`.
///
/// - Unsigned add overflow → `T::MAX` (all ones)
/// - Unsigned sub underflow → `0`
/// - Signed overflow → `ite(lhs_positive, T::MAX, T::MIN)`
pub(in crate::codegen_ay::chc) fn codegen_saturating_arithmetic(
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

    // Part of #3561: labeled block + saturation helper collapse saturating fallback exits.
    // `Some(false)` means try_emit_precise_call_result already emitted the fallback.
    let emitted: Option<bool> = 'compute: {
        let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
            break 'compute None;
        };
        let is_signed = arg_signedness_or_fallback(
            &args[0],
            ctx.body.locals(),
            "saturating_arith",
            SignednessFallbackKind::Arithmetic,
        );
        // Part of #3243: fall through to sound fallback on type resolution failure.
        let Some(int_bv_width) = args[0].ty(ctx.body.locals()).ok().and_then(ty_to_bv_width) else {
            debug!("saturating arithmetic type resolution failed (bb{}->bb{})", bb_idx, target);
            break 'compute None;
        };

        let Some((result, overflow)) =
            ctx.translate_checked_binop_flat(arith_op, lhs.clone(), rhs, is_signed, int_bv_width)
        else {
            break 'compute None;
        };
        if !result.sort().is_bitvec() && !result.sort().is_int() {
            debug!(
                "saturating arithmetic unsupported sort {:?} (bb{}->bb{})",
                result.sort(),
                bb_idx,
                target
            );
        }
        let Some(sat_value) =
            saturating_bound_expr(&lhs, &result, arith_op, is_signed, int_bv_width)
        else {
            break 'compute None;
        };

        // Final result: ite(overflow, saturation_bound, wrapping_result).
        let final_result = Expr::ite(overflow, sat_value, result);

        // Part of #3561: consolidated resolve→coerce→emit tail.
        Some(try_emit_precise_call_result(
            ctx,
            Some(final_result),
            dest_local,
            from_app,
            target,
            modified_locals,
            stmt_constraints,
            [],
            "codegen_call_saturating_arithmetic",
        ))
    };

    if emitted.is_some() {
        return;
    }

    // Fallback: args not resolved or translate failed.
    debug!("saturating arithmetic fallback (bb{}->bb{})", bb_idx, target);
    emit_sound_fallback_goto(
        ctx,
        from_app,
        target,
        modified_locals,
        &[dest_local],
        stmt_constraints,
    );
}

/// Handle `overflowing_add/sub/mul` and `add/sub/mul_with_overflow` returning `(T, bool)`.
///
/// The destination is a flattened tuple:
/// - field 0: wrapping result
/// - field 1: overflow flag
pub(in crate::codegen_ay::chc) fn codegen_overflowing_arithmetic(
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
    let dest_local: usize = destination.local;
    let lhs = ctx.resolve_ref_or_const_referent(&args[0], modified_locals);
    let rhs = ctx.resolve_ref_or_const_referent(&args[1], modified_locals);

    let emitted: bool = 'compute: {
        let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
            break 'compute false;
        };
        let is_signed = arg_signedness_or_fallback(
            &args[0],
            ctx.body.locals(),
            "overflowing_arith",
            SignednessFallbackKind::Arithmetic,
        );
        let Some(int_bv_width) = args[0].ty(ctx.body.locals()).ok().and_then(ty_to_bv_width) else {
            break 'compute false;
        };
        let Some((result, overflow)) =
            ctx.translate_checked_binop_flat(arith_op, lhs, rhs, is_signed, int_bv_width)
        else {
            break 'compute false;
        };
        if !(ctx.flatten.flattened_tuple_locals.contains(&dest_local)
            && ctx.flattened_field_count(dest_local) >= 2)
        {
            break 'compute false;
        }

        let field_values = [
            Some(reshape_flattened_result_field(ctx, dest_local, 0, result, is_signed)),
            Some(ctx.reshape_flattened_bool_field_for_call(dest_local, 1, overflow)),
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

/// Handle `overflowing_add_signed(self: usize, rhs: isize) -> (usize, bool)` (Part of #3300).
///
/// `ptr.offset()` is inlined by the Rust compiler into calls to `overflowing_add_signed`
/// rather than being lowered to `BinOp::Offset`. The semantics are:
/// - result = self.wrapping_add(rhs as usize)   [bitvec add, signedness irrelevant]
/// - overflow = (result < self) XOR (rhs < 0)   [unsigned overflow adjusted for sign]
///
/// The destination is a flattened `(usize, bool)` tuple:
/// - field 0: wrapping result
/// - field 1: overflow flag
///
/// When `extra_pointer_checks` is enabled, also emits an error rule for
/// the overflow condition so the solver produces CTREX.
pub(in crate::codegen_ay::chc) fn codegen_overflowing_add_signed(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
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

    // Part of #3561: labeled block collapses 3 fallback sites into 1.
    let emitted: bool = 'compute: {
        let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
            break 'compute false;
        };
        // Part of #3530: Int-lifted operands need coercion to BV for overflowing arithmetic.
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
            break 'compute false;
        }
        let Some(target_width) = ChcCtx::max_bitvec_width(&lhs, &rhs) else {
            break 'compute false;
        };
        // Coerce to same width. LHS (self) is unsigned, RHS (rhs) is signed.
        let lhs = coerce_bitvec_width_safe(lhs, target_width, SignExtension::ZeroExtend);
        let rhs = coerce_bitvec_width_safe(rhs, target_width, SignExtension::SignExtend);

        // result = self.wrapping_add(rhs as usize)  [BV add, sign irrelevant]
        let result = lhs.clone().bvadd(rhs.clone());

        // unsigned_carry = result < self  [unsigned comparison]
        let unsigned_carry = result.clone().bvult(lhs);
        // rhs_negative = rhs < 0  [signed comparison]
        let zero = Expr::bitvec_const(0u128, target_width);
        let rhs_negative = rhs.bvslt(zero);
        // overflow = unsigned_carry XOR rhs_negative = !(carry == negative)
        let overflow = unsigned_carry.eq(rhs_negative).not();

        // Part of #3300: When extra_pointer_checks is enabled, emit an error rule
        // for the overflow condition.
        if ctx.extra_pointer_checks {
            let no_overflow = overflow.clone().not();
            ctx.emit_error_rule_for_condition(from_app, no_overflow, stmt_constraints, bb_idx);
        }

        // Constrain flattened destination: field_0 = result, field_1 = overflow.
        if ctx.flatten.flattened_tuple_locals.contains(&dest_local)
            && ctx.flattened_field_count(dest_local) >= 2
        {
            let field_values = [
                Some(reshape_flattened_result_field(ctx, dest_local, 0, result, false)),
                Some(ctx.reshape_flattened_bool_field_for_call(dest_local, 1, overflow)),
            ];
            ctx.emit_flattened_call_fields(
                dest_local,
                &field_values,
                from_app,
                target,
                modified_locals,
                stmt_constraints,
            )
        } else {
            false
        }
    };

    if !emitted {
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
