// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SwitchInt guard computation and Range::next composition for fragments (#112).
//!
//! - **SwitchInt guards**: compute guard expressions for intermediate SwitchInt
//!   targets during fragment composition, and emit exit rules for out-of-fragment
//!   branches.
//! - **Range::next composition**: inline Range::spec_next constraints during
//!   fragment composition, enabling large-step encoding for Rust `for` loops.
//!
//! Extracted from `fragment_gen.rs` as part of #3199.

use std::collections::HashSet;
use std::sync::Arc;

use ay_bindings::Expr;
use rustc_public::mir::{Operand, TerminatorKind};
use tracing::{debug, warn};

use super::ChcCtx;
use super::codegen_call_coerce::coerce_eq_constraint;
use super::codegen_rules::CodegenRules;
use super::codegen_rules_helpers::CodegenRulesHelpers;
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};

pub(super) struct SwitchIntExitContext<'a> {
    pub from_app: &'a RelationApp,
    pub output_args: &'a [Expr],
    pub accumulated_constraints: &'a Arc<[Expr]>,
    pub bb_idx: usize,
}

/// Compute the SwitchInt guard expression for a specific target block.
///
/// Returns `Some(guard)` where `guard` constrains the discriminant to select
/// `target_bb`, or `None` if the guard cannot be computed.
///
/// Part of #112: extract SwitchInt guards for intermediate fragment composition.
pub(super) fn switchint_guard_for_target(
    discr_expr: &Expr,
    targets: &rustc_public::mir::SwitchTargets,
    target_bb: usize,
    bb_idx: usize,
) -> Option<Expr> {
    let branches: Vec<(u128, usize)> = targets.branches().collect();

    // Check explicit case branches.
    for &(case_val, target) in &branches {
        if target == target_bb {
            return ChcCtx::switchint_case_guard(discr_expr, case_val, bb_idx);
        }
    }

    // Check the otherwise (default) branch.
    if targets.otherwise() == target_bb {
        let case_vals: Vec<u128> = branches.iter().map(|(case_val, _)| *case_val).collect();
        return ChcCtx::switchint_otherwise_guard(discr_expr, &case_vals, bb_idx);
    }

    None
}

/// Emit exit rules for out-of-fragment SwitchInt targets at an intermediate block.
///
/// For each SwitchInt branch that exits the fragment (i.e., targets a cut point
/// or an excluded Unreachable block), emits a guarded rule from the fragment's
/// entry cut point. Unreachable targets get direct error rules instead of
/// goto rules, since they have no declared relation.
///
/// Part of #112: handle intermediate SwitchInt exits during fragment composition.
/// Part of #3101: direct error rules for Unreachable exits.
pub(super) fn emit_intermediate_switchint_exits(
    ctx: &mut ChcCtx<'_, '_>,
    discr_expr: &Expr,
    targets: &rustc_public::mir::SwitchTargets,
    in_fragment_target: usize,
    exit_ctx: &SwitchIntExitContext<'_>,
) {
    let branches: Vec<(u128, usize)> = targets.branches().collect();
    let otherwise = targets.otherwise();

    // For each explicit branch that exits the fragment.
    for &(case_val, target) in &branches {
        if target == in_fragment_target {
            continue; // Skip the in-fragment target.
        }
        if let Some(guard) = ChcCtx::switchint_case_guard(discr_expr, case_val, exit_ctx.bb_idx) {
            // Part of #3101: Unreachable blocks have no declared relation —
            // emit error rule directly instead of a goto rule.
            if target < ctx.body.blocks.len()
                && matches!(ctx.body.blocks[target].terminator.kind, TerminatorKind::Unreachable)
            {
                emit_guarded_error_rule(
                    ctx,
                    exit_ctx.from_app,
                    exit_ctx.accumulated_constraints,
                    guard,
                );
            } else {
                ctx.emit_guarded_goto_rule_shared(
                    exit_ctx.from_app,
                    target,
                    exit_ctx.output_args,
                    exit_ctx.accumulated_constraints,
                    guard,
                );
            }
        }
    }

    // For the otherwise branch (if it exits the fragment).
    if otherwise != in_fragment_target {
        let case_vals: Vec<u128> = branches.iter().map(|(case_val, _)| *case_val).collect();
        if let Some(guard) =
            ChcCtx::switchint_otherwise_guard(discr_expr, &case_vals, exit_ctx.bb_idx)
        {
            if otherwise < ctx.body.blocks.len()
                && matches!(ctx.body.blocks[otherwise].terminator.kind, TerminatorKind::Unreachable)
            {
                emit_guarded_error_rule(
                    ctx,
                    exit_ctx.from_app,
                    exit_ctx.accumulated_constraints,
                    guard,
                );
            } else {
                ctx.emit_guarded_goto_rule_shared(
                    exit_ctx.from_app,
                    otherwise,
                    exit_ctx.output_args,
                    exit_ctx.accumulated_constraints,
                    guard,
                );
            }
        }
    }
}

/// Emit a guarded error rule: `error() :- from_app, constraints, guard`.
///
/// Part of #3101: handles SwitchInt exits to Unreachable blocks during
/// fragment composition. The Unreachable block doesn't need its own
/// relation — the error is emitted directly from the composed rule.
fn emit_guarded_error_rule(
    ctx: &mut ChcCtx<'_, '_>,
    from_app: &RelationApp,
    accumulated_constraints: &Arc<[Expr]>,
    guard: Expr,
) {
    let error_app = RelationApp::new("error", Vec::new());
    let body = RuleBody::from_shared_base(
        Some(from_app.clone()),
        Arc::clone(accumulated_constraints),
        [guard],
    );
    ctx.vc.add_rule(Rule::new(body, error_app));
}

/// Emit unguarded exit rules for all out-of-fragment SwitchInt targets.
///
/// Fallback when discriminant translation fails: without the discriminant
/// we can't distinguish branches, so we conservatively allow all exit paths.
/// Unreachable targets get error rules; regular targets get goto rules.
///
/// Part of #3265: prevents silent exit rule drops when discriminant is
/// untranslatable during fragment composition.
pub(super) fn emit_unguarded_switchint_exits(
    ctx: &mut ChcCtx<'_, '_>,
    from_app: &RelationApp,
    targets: &rustc_public::mir::SwitchTargets,
    in_fragment_target: usize,
    output_args: &[Expr],
    accumulated_constraints: &Arc<[Expr]>,
    bb_idx: usize,
) {
    let branches: Vec<(u128, usize)> = targets.branches().collect();
    for &(_, target) in &branches {
        if target == in_fragment_target {
            continue;
        }
        emit_unguarded_exit_target(ctx, from_app, target, output_args, accumulated_constraints);
    }
    let otherwise = targets.otherwise();
    if otherwise != in_fragment_target {
        emit_unguarded_exit_target(ctx, from_app, otherwise, output_args, accumulated_constraints);
    }
    debug!(bb_idx, "emitted unguarded SwitchInt exits for untranslatable discriminant (#3265)");
}

/// Emit a single unguarded exit rule for a target block.
fn emit_unguarded_exit_target(
    ctx: &mut ChcCtx<'_, '_>,
    from_app: &RelationApp,
    target: usize,
    output_args: &[Expr],
    constraints: &Arc<[Expr]>,
) {
    if target < ctx.body.blocks.len()
        && matches!(ctx.body.blocks[target].terminator.kind, TerminatorKind::Unreachable)
    {
        let error_app = RelationApp::new("error", Vec::new());
        let body = RuleBody::from_shared_base(Some(from_app.clone()), Arc::clone(constraints), []);
        ctx.vc.add_rule(Rule::new(body, error_app));
    } else {
        ctx.emit_goto_rule_shared(from_app, target, output_args, constraints);
    }
}

/// Build and add Range::spec_next constraints during fragment composition.
///
/// Replicates the constraint-building logic from `codegen_call_iterator_adapter`
/// for `StubKind::RangeSpecNext`, but pushes constraints into the composition
/// accumulator instead of emitting a CHC rule.
///
/// Handles both the flattened path (Range fields as consecutive scalar state
/// vars) and the datatype path (Range as a AY datatype). Constrains:
/// - Iterator state: `start' = ite(start < end, start + 1, start)`
/// - Destination Option: `is_some = (start < end), payload = ite(start < end, start, old)`
///
/// Part of #112: composing through Range::next makes large-step encoding
/// effective for Rust `for` loops (which desugar to Iterator::next calls).
pub(super) fn compose_range_next_constraints(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[Operand],
    dest_local: usize,
    modified: &HashSet<usize>,
    all_constraints: &mut Vec<Expr>,
    bb_idx: usize,
) -> bool {
    let checkpoint = all_constraints.len();
    macro_rules! abort_composition {
        () => {{
            all_constraints.truncate(checkpoint);
            return false;
        }};
    }

    let Some((iter_expr, iter_local)) = ctx.iterator_receiver_expr_and_local(args, modified) else {
        warn!(bb_idx, "RangeNext composition: cannot resolve iterator receiver");
        abort_composition!();
    };

    ctx.ensure_local_live_at_block(dest_local, bb_idx);
    if let Some(iter_local) = iter_local {
        ctx.ensure_local_live_at_block(iter_local, bb_idx);
    }

    let Some((advanced_iter, has_remaining, current_item)) =
        ctx.advance_range_iterator_expr(&iter_expr, iter_local, modified)
    else {
        warn!(bb_idx, "RangeNext composition: cannot advance range iterator");
        abort_composition!();
    };

    if let Some(bound) = ctx.range_advance_bound_constraint(
        &iter_expr,
        iter_local,
        &advanced_iter,
        &has_remaining,
        modified,
    ) {
        all_constraints.push(bound);
    }

    // Build destination constraints (Option<T> result).
    // Guard: track whether destination was actually constrained. If not, skip
    // iterator state update to prevent unsound rules with free destination vars.
    let constraints_before = all_constraints.len();
    let Some(dest_vec_idx) = ctx.try_state_idx_for_local(dest_local) else {
        warn!(bb_idx, dest_local, "RangeNext composition: destination local not in state vars");
        abort_composition!();
    };
    if ctx.flatten.flattened_tuple_locals.contains(&dest_local)
        && ctx.flatten.flattened_enum_discr.contains_key(&dest_local)
    {
        // Flattened path: Option becomes [is_some: Bool, payload: T].
        if let Some(values) =
            ctx.build_flattened_range_next_fields(dest_local, has_remaining, current_item, modified)
        {
            if !ctx.constrain_flattened_fields_for_call(dest_local, &values, all_constraints) {
                warn!(
                    bb_idx,
                    dest_local, "RangeNext composition: failed to constrain flattened destination"
                );
                ctx.record_sound_fallback_reason("range_next_flattened_dest_unconstrained");
                abort_composition!();
            }
        }
    } else {
        // Datatype path: build full Option datatype expression.
        if let Some(out_sort) =
            ctx.state_var_mgr.output_state_vars.get(dest_vec_idx).map(|(_, s)| s.clone())
        {
            if let Some(option_result) =
                ctx.build_range_next_result(has_remaining, current_item, &out_sort)
            {
                if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
                    if let Some(eq) =
                        coerce_eq_constraint(&dest_var, option_result, dest_var.sort(), false)
                    {
                        all_constraints.push(eq);
                    } else {
                        warn!(
                            bb_idx,
                            dest_local,
                            "RangeNext composition: sort mismatch on destination result, sound fallback"
                        );
                        all_constraints.push(Expr::bool_const(true));
                        // Part of #3814: upgrade to reason-coded recording.
                        ctx.record_sound_fallback_reason("range_next_sort_mismatch");
                        abort_composition!();
                    }
                }
            }
        }
    }

    if all_constraints.len() == constraints_before {
        warn!(
            bb_idx,
            dest_local,
            "RangeNext composition: destination unconstrained, skipping iterator state update"
        );
        abort_composition!();
    }

    // Build iterator state update constraints.
    if let Some(iter_local) = iter_local {
        let iter_constraints_before = all_constraints.len();
        if ctx.flatten.flattened_tuple_locals.contains(&iter_local) {
            // Flattened Range: update start field, preserve end and other fields.
            if let Some(iter_end) = ctx.flattened_local_field_expr(iter_local, 1, modified) {
                let mut iter_values = vec![Some(advanced_iter), Some(iter_end)];
                for field_idx in 2..ctx.flattened_field_count(iter_local) {
                    iter_values
                        .push(ctx.flattened_local_field_expr(iter_local, field_idx, modified));
                }
                if !ctx.constrain_flattened_fields_for_call(
                    iter_local,
                    &iter_values,
                    all_constraints,
                ) {
                    warn!(
                        bb_idx,
                        iter_local,
                        "RangeNext composition: failed to constrain flattened iterator update"
                    );
                    ctx.record_sound_fallback_reason("range_next_flattened_iter_unconstrained");
                    abort_composition!();
                }
            } else {
                warn!(
                    bb_idx,
                    iter_local, "RangeNext composition: cannot read flattened iterator end field"
                );
                ctx.record_sound_fallback_reason("range_next_iter_end_unavailable");
                abort_composition!();
            }
        } else if let Some((_, iter_var)) = ctx.resolve_destination(iter_local) {
            // Datatype Range: direct equality for full iterator value.
            if let Some(eq) = coerce_eq_constraint(&iter_var, advanced_iter, iter_var.sort(), false)
            {
                all_constraints.push(eq);
            } else {
                warn!(
                    bb_idx,
                    ?iter_local,
                    "RangeNext composition: sort mismatch on iterator state update, sound fallback"
                );
                all_constraints.push(Expr::bool_const(true));
                // Part of #3814: upgrade to reason-coded recording.
                ctx.record_sound_fallback_reason("range_iter_state_sort_mismatch");
                abort_composition!();
            }
        } else {
            warn!(bb_idx, iter_local, "RangeNext composition: cannot resolve iterator destination");
            ctx.record_sound_fallback_reason("range_next_iter_destination_unresolved");
            abort_composition!();
        }

        if all_constraints.len() == iter_constraints_before {
            warn!(bb_idx, iter_local, "RangeNext composition: iterator update unconstrained");
            ctx.record_sound_fallback_reason("range_next_iter_update_unconstrained");
            abort_composition!();
        }
    }

    debug!(
        bb_idx,
        dest_local,
        ?iter_local,
        "RangeNext composition: constraints added inline (#112)"
    );
    true
}
