// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `div_euclid`/`rem_euclid` CHC encoding handler (Part of #3186).
//!
//! These methods use branching MIR bodies that fn_inline expands into
//! complex CHC rule sets the solver cannot handle (UNKNOWN).
//! This module provides direct bitvector encoding:
//! - Unsigned: `bvudiv`/`bvurem` (identical to regular division)
//! - Signed: `ite`-guarded adjustment of `bvsdiv`/`bvsrem` to produce
//!   non-negative remainder (Euclidean division semantics)

use crate::codegen_ay::shared::SignednessFallbackKind;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand};
use tracing::{debug, warn};

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_expr_signedness::arg_signedness_or_fallback;
use super::super::codegen_rules::CodegenRules;

/// Whether we are encoding `div_euclid` or `rem_euclid`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum EuclidOp {
    Div,
    Rem,
}

/// Handle `div_euclid`/`rem_euclid`: bitvector encoding (Part of #3186).
///
/// Euclidean division/remainder differs from truncated division (`/`, `%`)
/// for signed operands: the remainder is always non-negative.
///
/// - **Unsigned**: identical to `bvudiv`/`bvurem`.
/// - **Signed `div_euclid(a, b)`**:
///   ```text
///   q = bvsdiv(a, b);  r = bvsrem(a, b)
///   result = if r < 0 { if b > 0 { q - 1 } else { q + 1 } } else { q }
///   ```
/// - **Signed `rem_euclid(a, b)`**:
///   ```text
///   r = bvsrem(a, b)
///   result = if r < 0 { if b < 0 { r - b } else { r + b } } else { r }
///   ```
pub(in crate::codegen_ay::chc) fn codegen_euclid(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    op: EuclidOp,
) {
    let args = dcx.args;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let bb_idx = dcx.bb_idx;
    let dest_local: usize = dcx.destination.local;

    let lhs = ctx.resolve_ref_or_const_referent(&args[0], modified_locals);
    let rhs = ctx.resolve_ref_or_const_referent(&args[1], modified_locals);

    if let (Some(lhs), Some(rhs)) = (lhs, rhs)
        && lhs.sort().is_bitvec()
        && rhs.sort().is_bitvec()
    {
        let is_signed = arg_signedness_or_fallback(
            &args[0],
            ctx.body.locals(),
            match op {
                EuclidOp::Div => "div_euclid",
                EuclidOp::Rem => "rem_euclid",
            },
            SignednessFallbackKind::Arithmetic,
        );
        let Some(target_width) = ChcCtx::max_bitvec_width(&lhs, &rhs) else {
            warn!(fn_name = %ctx.fn_name, "CHC: euclid bitvec width unavailable");
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
        let a =
            coerce_bitvec_width_safe(lhs, target_width, SignExtension::for_signedness(is_signed));
        let b =
            coerce_bitvec_width_safe(rhs, target_width, SignExtension::for_signedness(is_signed));
        let zero = Expr::bitvec_const(0u128, target_width);
        let one = Expr::bitvec_const(1u128, target_width);

        // NOTE(#3424): Error rules for div-by-zero and signed overflow are omitted.
        // The handler-level error rule pattern (emit_euclid_error) produces spurious
        // CTREX because the resolved operand variables may not be properly constrained
        // within the projected CHC relation signature. The block-level safety check
        // mechanism does not apply here (Call terminator, not BinOp statement).
        // TODO: Re-add error rules using a pattern that correctly constrains
        // operand variables within the from_app relation (see #3424 for details).

        // Power-of-2 optimization (Part of #3428): when divisor is known to be 2^n
        // (recorded by codegen_pow), replace the complex ite/bvsdiv decomposition
        // with a simple shift operation. This eliminates the nested ite+bvsdiv+bvsrem
        // that PDR cannot synthesize invariants for.
        //
        // Correctness:
        //   div_euclid(a, 2^n) == bvashr(a, n)  for signed (positive divisor)
        //   div_euclid(a, 2^n) == bvlshr(a, n)  for unsigned
        //   rem_euclid(a, 2^n) == bvand(a, 2^n - 1)  (mask low n bits)
        let divisor_local = match &args[1] {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        };
        if let Some(div_local) = divisor_local {
            if let Some(exp_expr) = ctx.known_pow2_locals.get(&div_local).cloned() {
                let exp_coerced =
                    coerce_bitvec_width_safe(exp_expr, target_width, SignExtension::ZeroExtend);
                let result = match op {
                    EuclidOp::Div => {
                        if is_signed {
                            a.clone().bvashr(exp_coerced)
                        } else {
                            a.clone().bvlshr(exp_coerced)
                        }
                    }
                    EuclidOp::Rem => {
                        // 2^n - 1 is a bitmask for the low n bits.
                        let mask = Expr::bitvec_const(1u128, target_width)
                            .bvshl(exp_coerced)
                            .bvsub(Expr::bitvec_const(1u128, target_width));
                        a.clone().bvand(mask)
                    }
                };

                if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
                    let eq = ctx.make_coerced_eq_constraint(
                        &dest_var,
                        result,
                        dest_var.sort(),
                        dest_local,
                        match op {
                            EuclidOp::Div => "codegen_div_euclid_pow2",
                            EuclidOp::Rem => "codegen_rem_euclid_pow2",
                        },
                    );
                    let out = ctx.build_output_args(modified_locals, &[dest_local]);
                    ctx.emit_goto_rule_extra(from_app, target, &out, stmt_constraints, eq);
                    debug!(
                        op = ?op,
                        target_width,
                        is_signed,
                        "euclid: pow2 shift optimization (bb{}->bb{})",
                        bb_idx,
                        target
                    );
                    return;
                }
            }
        }

        let result = if !is_signed {
            // Unsigned: Euclidean == truncated.
            match op {
                EuclidOp::Div => a.bvudiv(b),
                EuclidOp::Rem => a.bvurem(b),
            }
        } else {
            match op {
                EuclidOp::Div => {
                    // q = bvsdiv(a, b); r = bvsrem(a, b)
                    // result = ite(r < 0, ite(b > 0, q - 1, q + 1), q)
                    let q = a.clone().bvsdiv(b.clone());
                    let r = a.bvsrem(b.clone());
                    let r_neg = r.bvslt(zero);
                    let b_pos = b.bvsgt(Expr::bitvec_const(0u128, target_width));
                    let q_minus_1 = q.clone().bvsub(one.clone());
                    let q_plus_1 = q.clone().bvadd(one);
                    let adjusted = Expr::ite(b_pos, q_minus_1, q_plus_1);
                    Expr::ite(r_neg, adjusted, q)
                }
                EuclidOp::Rem => {
                    // r = bvsrem(a, b)
                    // result = ite(r < 0, ite(b < 0, r - b, r + b), r)
                    let r = a.bvsrem(b.clone());
                    let r_neg = r.clone().bvslt(zero);
                    let b_neg = b.clone().bvslt(Expr::bitvec_const(0u128, target_width));
                    let r_minus_b = r.clone().bvsub(b.clone());
                    let r_plus_b = r.clone().bvadd(b);
                    let adjusted = Expr::ite(b_neg, r_minus_b, r_plus_b);
                    Expr::ite(r_neg, adjusted, r)
                }
            }
        };

        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let eq = ctx.make_coerced_eq_constraint(
                &dest_var,
                result,
                dest_var.sort(),
                dest_local,
                match op {
                    EuclidOp::Div => "codegen_div_euclid",
                    EuclidOp::Rem => "codegen_rem_euclid",
                },
            );
            let out = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(from_app, target, &out, stmt_constraints, eq);
            debug!(
                op = ?op,
                target_width,
                is_signed,
                "euclid: encoded (bb{}->bb{})",
                bb_idx,
                target
            );
        } else {
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
        warn!(
            fn_name = %ctx.fn_name,
            "CHC: euclid operands unresolved; destination unconstrained"
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
