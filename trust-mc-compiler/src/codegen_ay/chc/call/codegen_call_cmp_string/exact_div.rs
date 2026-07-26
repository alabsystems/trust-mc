// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CHC handler for the `exact_div` intrinsic (#3177).
//!
//! `exact_div(a, b)` computes `a / b` with three UB conditions:
//! 1. `b == 0` (division by zero)
//! 2. `a % b != 0` (division is not exact)
//! 3. Signed overflow: `a == T::MIN && b == -1`
//!
//! Each UB condition emits an error rule; the happy path emits a
//! transition rule constraining `dest = a / b`.
//!
//! Upstream Kani: codegen_cprover_gotoc/codegen/intrinsic.rs:675-709.

use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};
use ay_bindings::Expr;
use rustc_public::mir::BasicBlockIdx;
use tracing::{debug, warn};

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_expr_signedness::arg_signedness_or_fallback;
use super::super::codegen_rules::CodegenRules;
use super::super::{ChcCtx, RelationApp, Rule, RuleBody};
use crate::codegen_ay::shared::SignednessFallbackKind;

/// Handle `exact_div(a, b)` intrinsic in CHC code generation.
pub(in crate::codegen_ay::chc) fn codegen_exact_div(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let args = dcx.args;
    let destination = dcx.destination;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let dest_local: usize = destination.local;

    let lhs = ctx.resolve_ref_or_const_referent(&args[0], modified_locals);
    let rhs = ctx.resolve_ref_or_const_referent(&args[1], modified_locals);

    if let (Some(lhs), Some(rhs)) = (lhs, rhs)
        && lhs.sort().is_bitvec()
        && rhs.sort().is_bitvec()
    {
        let is_signed = arg_signedness_or_fallback(
            &args[0],
            ctx.body.locals(),
            "exact_div",
            SignednessFallbackKind::Arithmetic,
        );
        let Some(target_width) = ChcCtx::max_bitvec_width(&lhs, &rhs) else {
            warn!(fn_name = %ctx.fn_name, "CHC: exact_div bitvec width unavailable");
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

        // Error rule 1: b == 0 (division by zero).
        let b_is_zero = b.clone().eq(zero.clone());
        emit_exact_div_error(ctx, from_app, stmt_constraints, b_is_zero.clone());

        // Error rule 2: a % b != 0 (not exact), guarded by b != 0.
        let remainder =
            if is_signed { a.clone().bvsrem(b.clone()) } else { a.clone().bvurem(b.clone()) };
        let not_exact = b_is_zero.not().and(remainder.ne(zero));
        emit_exact_div_error(ctx, from_app, stmt_constraints, not_exact);

        // Error rule 3: signed overflow (a == T::MIN && b == -1).
        if is_signed {
            let int_min = Expr::bitvec_const(1u128 << (target_width - 1), target_width);
            let neg_one = Expr::bitvec_const(!0u128, target_width);
            let overflow = a.clone().eq(int_min).and(b.clone().eq(neg_one));
            emit_exact_div_error(ctx, from_app, stmt_constraints, overflow);
        }

        // Happy path: dest = a / b.
        let result = if is_signed { a.bvsdiv(b) } else { a.bvudiv(b) };

        if let Some(fc) = ctx.build_flattened_destination_constraints(dest_local, result.clone()) {
            let out = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(from_app, target, &out, stmt_constraints, fc);
        } else if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let out_sort = dest_var.sort();
            let final_result = if *result.sort() == *out_sort {
                Some(result)
            } else {
                out_sort.bitvec_width().map(|w| {
                    coerce_bitvec_width_safe(result, w, SignExtension::for_signedness(is_signed))
                })
            };
            if let Some(converted) = final_result {
                let eq = ctx.make_coerced_eq_constraint(
                    &dest_var,
                    converted,
                    out_sort,
                    dest_local,
                    "codegen_exact_div",
                );
                let out = ctx.build_output_args(modified_locals, &[dest_local]);
                ctx.emit_goto_rule_extra(from_app, target, &out, stmt_constraints, eq);
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
            emit_sound_fallback_goto(
                ctx,
                from_app,
                target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
        }
        debug!(target_width, is_signed, fn_name = %ctx.fn_name, "CHC: exact_div encoded");
    } else {
        warn!(fn_name = %ctx.fn_name, "CHC: exact_div operands unresolved; destination unconstrained");
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

/// Emit an error rule guarded by a violation condition.
fn emit_exact_div_error(
    ctx: &mut ChcCtx<'_, '_>,
    from_app: &RelationApp,
    stmt_constraints: &[Expr],
    violation: Expr,
) {
    let error_app = RelationApp::new("error", Vec::new());
    let body = RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, [violation]);
    ctx.vc.add_rule(Rule::new(body, error_app));
}
