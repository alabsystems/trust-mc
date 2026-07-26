// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Integer `pow`/`wrapping_pow` CHC encoding handler (Part of #3186).
//!
//! These methods use exponentiation-by-squaring loops in MIR that exceed
//! the inline block limit, falling through to unconstrained (→ UNKNOWN).
//! This module provides direct bitvector encoding for:
//! - Constant base 2 → `bvshl(1, exp)` (power of two = left shift)
//! - Both constants → evaluate `base.wrapping_pow(exp)` at codegen time
//! - Otherwise → sound over-approximation (unconstrained)

use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe, ty_to_bv_width};
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand};
use rustc_public::ty::{ConstantKind, RigidTy, TyConstKind, TyKind};
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_rules::CodegenRules;

/// Handle `pow`/`wrapping_pow`: base.pow(exp) → bitvec result (Part of #3186).
///
/// Integer `pow`/`wrapping_pow` use exponentiation-by-squaring loops in MIR,
/// exceeding the inline block limit and falling through to unconstrained.
/// This handler provides exact encoding for:
/// - **Constant base 2**: `2^exp` = `bvshl(1, exp)` (power of two → left shift)
/// - **Both constants**: evaluate `base.wrapping_pow(exp)` at codegen time
/// - **Otherwise**: sound over-approximation (fall through to unconstrained)
pub(in crate::codegen_ay::chc) fn codegen_pow(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let args = dcx.args;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let bb_idx = dcx.bb_idx;
    let dest_local: usize = dcx.destination.local;

    // Extract constant values from MIR operands for base and exponent.
    let base_const = try_extract_const_u128(&args[0]);
    let exp_const = try_extract_const_u128(&args[1]);

    // Determine the result bitvec width from the return type.
    let result_width = args[0].ty(ctx.body.locals()).ok().and_then(ty_to_bv_width).unwrap_or(0);
    if result_width == 0 {
        debug!("pow: cannot determine result width (bb{}->bb{})", bb_idx, target);
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

    // Case 1: Both base and exponent are constants — evaluate at codegen time.
    if let (Some(base), Some(exp)) = (base_const, exp_const) {
        if let Ok(exp_u32) = u32::try_from(exp) {
            let result_val = base.wrapping_pow(exp_u32);
            let result_expr = Expr::bitvec_const(result_val as i128, result_width);

            if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
                let eq = ctx.make_coerced_eq_constraint(
                    &dest_var,
                    result_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_pow_const",
                );
                let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
                ctx.emit_goto_rule_extra(from_app, target, &new_output_args, stmt_constraints, eq);
                debug!(
                    base,
                    exp,
                    result = result_val,
                    "pow: constant-folded (bb{}->bb{})",
                    bb_idx,
                    target
                );
                return;
            }
        }
    }

    // Case 2: Base is constant 2 — emit bvshl(1, exp).
    // 2^n == 1 << n for bitvector arithmetic.
    if base_const == Some(2) {
        let exp_expr = ctx.resolve_ref_or_const_referent(&args[1], modified_locals);
        if let Some(exp_expr) = exp_expr {
            let one = Expr::bitvec_const(1, result_width);
            let exp_coerced =
                coerce_bitvec_width_safe(exp_expr, result_width, SignExtension::ZeroExtend);
            let result_expr = one.bvshl(exp_coerced.clone());

            if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
                let eq = ctx.make_coerced_eq_constraint(
                    &dest_var,
                    result_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_pow_base2",
                );
                let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
                ctx.emit_goto_rule_extra(from_app, target, &new_output_args, stmt_constraints, eq);
                // Record that dest_local holds 2^exp for downstream optimizations
                // (e.g., div_euclid(a, 2^n) → bvashr(a, n)). Part of #3428.
                ctx.known_pow2_locals.insert(dest_local, exp_coerced);
                debug!("pow: base-2 → bvshl(1, exp) (bb{}->bb{})", bb_idx, target);
                return;
            }
        }
    }

    // Fallback: non-constant base or cannot resolve — sound over-approximation.
    debug!("pow: fallback to unconstrained (bb{}->bb{})", bb_idx, target);
    emit_sound_fallback_goto(
        ctx,
        from_app,
        target,
        modified_locals,
        &[dest_local],
        stmt_constraints,
    );
}

/// Try to extract a constant unsigned integer value from a MIR operand.
///
/// Returns `Some(value)` if the operand is `Operand::Constant` with an integer
/// allocation that can be read as `u128`. Returns `None` for non-constant
/// operands, non-integer types, or unreadable allocations.
fn try_extract_const_u128(operand: &Operand) -> Option<u128> {
    let const_op = match operand {
        Operand::Constant(c) => c,
        Operand::Copy(_) | Operand::Move(_) => return None,
    };
    let mir_const = &const_op.const_;

    let extract_from_alloc =
        |alloc: &rustc_public::ty::Allocation, ty: rustc_public::ty::Ty| -> Option<u128> {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Uint(_)) => alloc.read_uint().ok(),
                TyKind::RigidTy(RigidTy::Int(_)) => {
                    let v = alloc.read_int().ok()?;
                    u128::try_from(v).ok()
                }
                _ => None,
            }
        };

    let ty = mir_const.ty();
    match mir_const.kind() {
        ConstantKind::Allocated(alloc) => extract_from_alloc(alloc, ty),
        ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(value_ty, alloc) => extract_from_alloc(alloc, *value_ty),
            _ => None,
        },
        _ => None,
    }
}
