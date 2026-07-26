// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `wrapping_abs` / `wrapping_neg` CHC encoding handler (Part of #3293).
//!
//! These are unary integer methods with branching MIR bodies. Without direct
//! stubs, `wrapping_abs` calls `wrapping_neg` internally, causing fn_inline
//! to produce complex CHC rules or fall through to unconstrained.
//!
//! Encoding:
//! - `wrapping_abs(x)` → `ite(bvslt(x, 0), bvneg(x), x)`
//! - `wrapping_neg(x)` → `bvneg(x)`

use ay_bindings::Expr;
use rustc_public::mir::BasicBlockIdx;
use tracing::{debug, warn};

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_rules::CodegenRules;

/// Handle `wrapping_abs`: `ite(bvslt(x, 0), bvneg(x), x)` (Part of #3293).
///
/// `wrapping_abs` is defined only on signed integer types. For the minimum
/// value (e.g. `i32::MIN`), `wrapping_abs` wraps: `(-128i8).wrapping_abs() == -128`.
/// This is correctly modeled by bitvector `bvneg` which wraps on two's complement.
pub(in crate::codegen_ay::chc) fn codegen_wrapping_abs(
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

    let operand = ctx.resolve_ref_or_const_referent(&args[0], modified_locals);

    if let Some(x) = operand
        && x.sort().is_bitvec()
    {
        let w = x.sort().bitvec_width().expect("invariant: is_bitvec guard");
        let zero = Expr::bitvec_const(0u128, w);
        let is_neg = x.clone().bvslt(zero);
        let negated = x.clone().bvneg();
        let result = Expr::ite(is_neg, negated, x);

        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let eq = ctx.make_coerced_eq_constraint(
                &dest_var,
                result,
                dest_var.sort(),
                dest_local,
                "codegen_wrapping_abs",
            );
            let out = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(from_app, target, &out, stmt_constraints, eq);
            debug!("wrapping_abs: encoded (bb{}->bb{})", bb_idx, target);
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
            "CHC: wrapping_abs operand unresolved; destination unconstrained"
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

/// Handle `wrapping_neg`: `bvneg(x)` (Part of #3293).
///
/// Equivalent to MIR `UnOp::Neg` but appears as a function call when not
/// lowered by rustc. Encoding is straightforward bitvector negation.
pub(in crate::codegen_ay::chc) fn codegen_wrapping_neg(
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

    let operand = ctx.resolve_ref_or_const_referent(&args[0], modified_locals);

    if let Some(x) = operand
        && x.sort().is_bitvec()
    {
        let result = x.bvneg();

        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let eq = ctx.make_coerced_eq_constraint(
                &dest_var,
                result,
                dest_var.sort(),
                dest_local,
                "codegen_wrapping_neg",
            );
            let out = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(from_app, target, &out, stmt_constraints, eq);
            debug!("wrapping_neg: encoded (bb{}->bb{})", bb_idx, target);
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
            "CHC: wrapping_neg operand unresolved; destination unconstrained"
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
