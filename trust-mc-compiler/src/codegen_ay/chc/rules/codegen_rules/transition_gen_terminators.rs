// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Terminator-specific handlers for CHC transition rule generation.
//!
//! Contains SwitchInt, Assert, and unwind-edge emission logic, extracted
//! from `transition_gen.rs` to keep per-file line counts under 500.
//!
//! Extracted from `transition_gen.rs` — Part of #3927.

use ay_bindings::Expr;
use rustc_public::mir::UnwindAction;
use tracing::debug;

use super::super::codegen_rules_helpers::CodegenRulesHelpers;
use super::super::{ChcCtx, CodegenRulesPointerCheck};
use super::{CodegenRules, TransitionContext};

/// Handle SwitchInt terminator with shared constraints.
///
/// This is the primary beneficiary of Arc-shared constraints: a SwitchInt
/// with K branches emits K+1 rules, all sharing the same base constraint
/// slice via Arc rather than copying it K+1 times. Part of #2507.
pub(super) fn codegen_switchint(
    ctx: &mut ChcCtx<'_, '_>,
    discr: &rustc_public::mir::Operand,
    targets: &rustc_public::mir::SwitchTargets,
    tctx: &TransitionContext<'_>,
) {
    // Translate the discriminant using OUTPUT vars for modified locals (#656)
    if let Some(discr_expr) = ctx.translate_operand_with_modified(discr, tctx.modified_locals) {
        let branches: Vec<(u128, usize)> = targets.branches().collect();
        let mut branch_guards = Vec::with_capacity(branches.len());
        let mut fallback = false;

        for (case_val, target) in &branches {
            if let Some(guard) = ChcCtx::switchint_case_guard(&discr_expr, *case_val, tctx.bb_idx) {
                branch_guards.push((*target, guard));
            } else {
                fallback = true;
                break;
            }
        }

        if fallback {
            // Fallback path now uses Arc-shared constraints (Part of #2507).
            ctx.emit_switchint_fallback_rules(
                &branches,
                targets.otherwise(),
                tctx,
                "unsupported SwitchInt discriminant",
            );
        } else {
            // Hot path: K+1 rules sharing the same base constraints via Arc.
            for (target, guard) in branch_guards {
                ctx.emit_guarded_goto_rule_shared(
                    tctx.from_app,
                    target,
                    tctx.output_args,
                    tctx.shared_constraints,
                    guard,
                );
            }

            // Otherwise branch: none of the explicit cases matched.
            //
            // Missed-bug F fix: do NOT conjoin `selector ∈ cases` for exhaustive
            // enum matches with an `Unreachable` otherwise arm. For a WELL-TYPED
            // enum the selector is already pinned to a valid discriminant VALUE by
            // the encoding — `SetDiscriminant`/literal construction store the
            // discriminant value (encode_unit_enum_discriminant,
            // codegen_unit_enum_from_alloc) and `kani::any` is bounded to the valid
            // tag set (unit_enum_discriminant_bounds) — so `selector ∉ cases` is
            // already UNSAT and the conjunction was redundant. But an INVALID
            // discriminant produced by an unsafe transmute (e.g.
            // `transmute::<u8,E>(3)` with E's tags {10,20,30}) is NOT a valid tag:
            // the otherwise arm is genuinely reachable (invalid-value UB) and MUST
            // reach the `Unreachable` error edge. Refuting it unconditionally here
            // dropped that UB and proved defective programs SUCCESSFUL.
            let case_vals: Vec<u128> = branches.iter().map(|(case_val, _)| *case_val).collect();
            let otherwise_guard =
                ChcCtx::switchint_otherwise_guard(&discr_expr, &case_vals, tctx.bb_idx);

            if let Some(guard) = otherwise_guard {
                ctx.emit_guarded_goto_rule_shared(
                    tctx.from_app,
                    targets.otherwise(),
                    tctx.output_args,
                    tctx.shared_constraints,
                    guard,
                );
            } else {
                ctx.emit_goto_rule_shared(
                    tctx.from_app,
                    targets.otherwise(),
                    tctx.output_args,
                    tctx.shared_constraints,
                );
            }
        }
    } else {
        let branches: Vec<(u128, usize)> = targets.branches().collect();
        ctx.emit_switchint_fallback_rules(
            &branches,
            targets.otherwise(),
            tctx,
            "cannot translate SwitchInt discriminant",
        );
    }
}

/// Handle Assert terminator.
///
/// Returns `Some(failure_guard)` when the assertion condition was successfully
/// translated — the caller can use `failure_guard` (which is `¬guard`) to
/// condition the unwind edge so cleanup is only reachable on assertion failure.
/// Returns `None` when the condition was untranslatable (conservative fallback).
pub(super) fn codegen_assert(
    ctx: &mut ChcCtx<'_, '_>,
    cond: &rustc_public::mir::Operand,
    expected: bool,
    msg: &rustc_public::mir::AssertMessage,
    target: usize,
    tctx: &TransitionContext<'_>,
) -> Option<Expr> {
    if ctx.should_skip_reg_pointer_assert(tctx.bb_idx, cond, msg) {
        debug!(
            bb_idx = tctx.bb_idx,
            ?msg,
            "skipping ref-derived pointer runtime check at Reg track level"
        );
        ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
        // Assertion skipped — failure is impossible, so unwind is unreachable.
        return Some(Expr::bool_const(false));
    }
    if assert_check_disabled(ctx, msg) {
        debug!(bb_idx = tctx.bb_idx, ?msg, "skipping disabled runtime check");
        ctx.emit_goto_rule_shared(tctx.from_app, target, tctx.output_args, tctx.shared_constraints);
        return Some(Expr::bool_const(false));
    }
    // Debug: trace Assert terminators (#1889)
    debug!("[assert] bb{} cond={:?} expected={} target={}", tctx.bb_idx, cond, expected, target);
    if let Some(bool_cond) = ctx.translate_assert_condition(cond, tctx.modified_locals, tctx.bb_idx)
    {
        let guard = if expected { bool_cond } else { bool_cond.not() };

        // Emit error rule for assertion violation.
        // `guard` already encodes `cond == expected`, so
        // violation is simply `guard != true`.
        ctx.emit_assert_error_rule_shared(
            tctx.from_app,
            guard.clone(),
            true,
            tctx.shared_constraints,
            tctx.bb_idx,
            Some(msg),
        );

        // Emit guarded successor edge (assertion holds)
        ctx.emit_guarded_goto_rule_shared(
            tctx.from_app,
            target,
            tctx.output_args,
            tctx.shared_constraints,
            guard.clone(),
        );

        // Return ¬guard so the caller can condition the unwind edge.
        Some(guard.not())
    } else {
        debug!(
            bb_idx = tctx.bb_idx,
            "cannot translate assertion condition, emitting conservative fallback"
        );
        ctx.emit_untranslatable_assert_fallback(
            tctx.from_app,
            target,
            tctx.output_args,
            tctx.shared_constraints,
            tctx.bb_idx,
        );
        // Condition untranslatable — conservative: unwind stays unconditional.
        None
    }
}

fn assert_check_disabled(ctx: &ChcCtx<'_, '_>, msg: &rustc_public::mir::AssertMessage) -> bool {
    use rustc_public::mir::AssertMessage;
    match msg {
        AssertMessage::Overflow(..) | AssertMessage::OverflowNeg(..) => !ctx.overflow_checks,
        AssertMessage::BoundsCheck { .. }
        | AssertMessage::NullPointerDereference
        | AssertMessage::MisalignedPointerDereference { .. } => !ctx.memory_safety_checks,
        _ => false,
    }
}

/// Part of #3301: Emit unwind edge to cleanup block for panic-path reachability.
///
/// Part of #3436: Skip unwind edges to error-only blocks. Cleanup blocks are
/// on panic paths that cannot reach Return. If we emit an unconditional goto
/// to an error-only block, `try_emit_unreachable_error_shared` would shortcircuit
/// it to `error()`, creating a false positive (every block with a cleanup target
/// would unconditionally reach error). The actual error conditions are already
/// captured by the Assert/Call handlers with proper guards.
pub(super) fn emit_unwind_edge(
    ctx: &mut ChcCtx<'_, '_>,
    tctx: &TransitionContext<'_>,
    unwind: &UnwindAction,
) {
    if let UnwindAction::Cleanup(cleanup_bb) = unwind {
        // Part of #3436: Skip if cleanup block is error-only (dead block elimination).
        if !ctx.block_relations.contains_key(cleanup_bb) {
            debug!(
                bb_idx = tctx.bb_idx,
                cleanup_bb = *cleanup_bb,
                "skipping unwind edge to error-only cleanup block (#3436)"
            );
            return;
        }
        debug!(
            bb_idx = tctx.bb_idx,
            cleanup_bb = *cleanup_bb,
            "emitting unwind edge to cleanup block (#3301)"
        );
        ctx.emit_goto_rule_shared(
            tctx.from_app,
            *cleanup_bb,
            tctx.output_args,
            tctx.shared_constraints,
        );
    }
}

/// Part of #3783: Emit guarded unwind edge for Assert terminators.
///
/// Unlike `emit_unwind_edge` (unconditional), this conditions the cleanup edge
/// on `failure_guard` — the negated assertion condition. MIR semantics: the
/// unwind path is only taken when the assertion fails. Without guarding, the
/// cleanup path is unconditionally reachable, creating a spurious `error()`
/// path through Resume/Abort even when the assertion holds.
///
/// When `failure_guard` is `None` (untranslatable assertion), falls back to
/// the unconditional `emit_unwind_edge` for soundness.
pub(super) fn emit_assert_unwind_edge(
    ctx: &mut ChcCtx<'_, '_>,
    tctx: &TransitionContext<'_>,
    unwind: &UnwindAction,
    failure_guard: Option<&Expr>,
) {
    match failure_guard {
        Some(guard) => {
            if let UnwindAction::Cleanup(cleanup_bb) = unwind {
                if !ctx.block_relations.contains_key(cleanup_bb) {
                    debug!(
                        bb_idx = tctx.bb_idx,
                        cleanup_bb = *cleanup_bb,
                        "skipping assert unwind edge to error-only cleanup block"
                    );
                    return;
                }
                debug!(
                    bb_idx = tctx.bb_idx,
                    cleanup_bb = *cleanup_bb,
                    "emitting guarded assert unwind edge (#3783)"
                );
                ctx.emit_guarded_goto_rule_shared(
                    tctx.from_app,
                    *cleanup_bb,
                    tctx.output_args,
                    tctx.shared_constraints,
                    guard.clone(),
                );
            }
        }
        None => {
            // Untranslatable assertion — fall back to unconditional unwind.
            emit_unwind_edge(ctx, tctx, unwind);
        }
    }
}
