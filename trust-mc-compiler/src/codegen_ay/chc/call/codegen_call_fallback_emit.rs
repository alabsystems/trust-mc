// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Sound-fallback transition emission helpers.
//!
//! Extracted from `codegen_call_coerce.rs` to keep that file under 500 LOC.
//! Part of #3561: sound fallback transition helpers.

use ay_bindings::Expr;
use std::collections::HashSet;
use tracing::debug;

use super::ChcCtx;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use trust_mc_core::chc::RelationApp;

/// Emit the sound-fallback transition epilogue: record the fallback counter,
/// build output args, and emit a goto rule to the target block.
///
/// This replaces the repeated 3-line pattern:
///   ctx.record_sound_fallback_reason("...");
///   let output_args = ctx.build_output_args(modified_locals, dest_locals);
///   ctx.emit_goto_rule(from_app, target, &output_args, stmt_constraints);
///
/// Part of #3561: sound fallback transition helper.
pub(in crate::codegen_ay::chc) fn emit_sound_fallback_goto(
    ctx: &mut ChcCtx<'_, '_>,
    from_app: &RelationApp,
    target: usize,
    modified_locals: &HashSet<usize>,
    dest_locals: &[usize],
    stmt_constraints: &[Expr],
) {
    emit_sound_fallback_goto_extra(
        ctx,
        from_app,
        target,
        modified_locals,
        dest_locals,
        stmt_constraints,
        [],
    );
}

/// Like [`emit_sound_fallback_goto`], but appends extra constraints beyond
/// the base `stmt_constraints` slice — for call sites that add range axioms
/// or additional destination constraints.
///
/// Part of #3561: sound fallback transition helper.
pub(in crate::codegen_ay::chc) fn emit_sound_fallback_goto_extra(
    ctx: &mut ChcCtx<'_, '_>,
    from_app: &RelationApp,
    target: usize,
    modified_locals: &HashSet<usize>,
    dest_locals: &[usize],
    stmt_constraints: &[Expr],
    extra: impl IntoIterator<Item = Expr>,
) {
    debug!(
        fn_name = %ctx.fn_name,
        target,
        "CHC: call_dispatch_fallback fired (Part of #4203)"
    );
    ctx.record_sound_fallback_reason("call_dispatch_fallback");
    let output_args = ctx.build_output_args(modified_locals, dest_locals);
    ctx.emit_goto_rule_extra(from_app, target, &output_args, stmt_constraints, extra);
}

/// P4-4: axiom-constrained over-approximation for PURE math intrinsics
/// (sin/cos/sqrt/exp range axioms, even-power non-negativity).
///
/// Identical emission to [`emit_sound_fallback_goto_extra`] but records the
/// blessed `math_axiom_range_overapprox` reason instead of the fail-closed
/// `call_dispatch_fallback`: the destination is the ONLY effect of these
/// intrinsics (no memory side effects, nothing identity-retained), it reaches
/// the head as a fresh havoc constrained only by axioms every concrete
/// execution satisfies — a strict over-approximation, ∀-sound. The generic
/// reason exists for calls that may have unmodeled SIDE EFFECTS (dropping
/// those retains stale memory = under-approximation); that hazard cannot
/// occur here, and the fail-closed demotion was flipping fully-proved
/// harnesses (powf32.rs: 4/4 checks SUCCESS) to FAILED.
pub(in crate::codegen_ay::chc) fn emit_math_axiom_goto_extra(
    ctx: &mut ChcCtx<'_, '_>,
    from_app: &RelationApp,
    target: usize,
    modified_locals: &HashSet<usize>,
    dest_locals: &[usize],
    stmt_constraints: &[Expr],
    extra: impl IntoIterator<Item = Expr>,
) {
    debug!(
        fn_name = %ctx.fn_name,
        target,
        "CHC: math axiom-constrained over-approximation emitted (P4-4)"
    );
    ctx.record_sound_fallback_reason("math_axiom_range_overapprox");
    let output_args = ctx.build_output_args(modified_locals, dest_locals);
    ctx.emit_goto_rule_extra(from_app, target, &output_args, stmt_constraints, extra);
}

/// Like [`emit_sound_fallback_goto`], but accepts pre-built `output_args`
/// instead of computing them from `(modified_locals, dest_locals)`.
///
/// Use when the caller already called `build_output_args` earlier (e.g., shared
/// across multiple branches) or when late state variables make re-computation
/// incorrect.
///
/// Part of #3561: sound fallback transition helper.
pub(in crate::codegen_ay::chc) fn emit_sound_fallback_goto_prebuilt(
    ctx: &mut ChcCtx<'_, '_>,
    from_app: &RelationApp,
    target: usize,
    output_args: &[Expr],
    stmt_constraints: &[Expr],
) {
    ctx.record_sound_fallback_reason("call_dispatch_fallback_prebuilt");
    ctx.emit_goto_rule(from_app, target, output_args, stmt_constraints);
}

/// Try to emit a precise call result: resolve destination, coerce to output sort,
/// and emit a goto rule with the equality constraint. Returns `true` on success.
///
/// On failure (result is `None`, destination unresolvable, or coercion failure),
/// emits a sound fallback goto instead.
///
/// This consolidates the repeated 3-level nesting pattern:
///   if let Some(result) = translate_X() {
///       if let Some((_, dest_var)) = resolve_destination() {
///           if let Some(eq) = make_coerced_eq_constraint() { emit } else { fallback }
///       } else { fallback }
///   } else { fallback }
///
/// Part of #3561: reduces 3 emit_sound_fallback_goto sites to 1 per call site.
pub(in crate::codegen_ay::chc) fn try_emit_precise_call_result(
    ctx: &mut ChcCtx<'_, '_>,
    result: Option<Expr>,
    dest_local: usize,
    from_app: &RelationApp,
    target: usize,
    modified_locals: &HashSet<usize>,
    stmt_constraints: &[Expr],
    extra: impl IntoIterator<Item = Expr>,
    label: &'static str,
) -> bool {
    if let Some(result_expr) = result {
        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            if let Some(eq) = ctx.make_coerced_eq_constraint(
                &dest_var,
                result_expr,
                dest_var.sort(),
                dest_local,
                label,
            ) {
                let out = ctx.build_output_args(modified_locals, &[dest_local]);
                ctx.emit_goto_rule_extra(
                    from_app,
                    target,
                    &out,
                    stmt_constraints,
                    extra.into_iter().chain(std::iter::once(eq)),
                );
                return true;
            }
        }
    }
    emit_sound_fallback_goto(
        ctx,
        from_app,
        target,
        modified_locals,
        &[dest_local],
        stmt_constraints,
    );
    false
}
