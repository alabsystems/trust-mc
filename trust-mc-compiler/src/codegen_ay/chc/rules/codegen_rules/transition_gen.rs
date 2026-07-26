// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CFG transition rule generation — the main `generate_transition_rules` loop.
//!
//! Walks MIR basic blocks, encodes statements into constraints, and dispatches
//! terminator kinds (Goto, SwitchInt, Call, Assert, Drop, etc.) to rule emission.
//!
//! Terminator-specific handlers (SwitchInt, Assert, unwind edges) are in
//! `transition_gen_terminators.rs` — Part of #3927.
//!
//! Drop terminator semantics are in `transition_drop.rs` — Part of #3254.
//!
//! Extracted from codegen_rules.rs — Part of #2408.

use std::sync::Arc;

use rustc_public::mir::TerminatorKind;

use ay_bindings::Expr;
use tracing::{debug, warn};

use super::super::chc_call_context::DispatchCallContext;
use super::super::collect_constructor_guards;
use super::super::{CallTerminator, ChcCtx};
use super::transition_gen_terminators::{
    codegen_assert, codegen_switchint, emit_assert_unwind_edge, emit_unwind_edge,
};
use super::{CodegenRules, TransitionContext};
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};

/// Implementation of `generate_transition_rules` for `ChcCtx`.
///
/// Separated from the trait impl block to keep the rule emission methods
/// in `mod.rs` under 500 LOC.
pub(in crate::codegen_ay::chc) fn generate_transition_rules(ctx: &mut ChcCtx<'_, '_>) {
    // Part of #3839: Pre-scan for constant-foldable math calls (block-order independent).
    crate::codegen_ay::chc::call::codegen_call_cmp_string::math_const_prescan::prescan_const_foldable_math_calls(ctx);
    // Part of #3905: Identify single-assignment locals for safe cross-block propagation.
    crate::codegen_ay::chc::call::codegen_call_cmp_string::math_const_prescan::compute_single_assign_locals(ctx);
    // FC-06: locate modifies-frame markers and compute checked-extent blocks.
    crate::codegen_ay::chc::modifies_frame::prescan_modifies_frames(ctx);

    // Part of #3979: Process blocks in topological (control-flow) order rather than
    // MIR index order. Side-table population (const_ref_values, subslice_offset/len)
    // during block encoding creates implicit ordering dependencies. MIR index order
    // can violate these when the compiler reorders blocks (e.g., bb5 defines local 2
    // but bb1 < bb5 reads it). Topological order ensures definitions precede uses.
    // Blocks in cycles (loop bodies) are appended in MIR index order as fallback —
    // Kahn's algorithm excludes them, but their CHC rules are self-contained.
    let block_order = {
        use crate::codegen_ay::loop_unroll::Cfg;
        let cfg = Cfg::from_body(ctx.body);
        let topo_set: std::collections::HashSet<usize> = cfg.topo_order.iter().copied().collect();
        let mut order = cfg.topo_order;
        // Append remaining blocks not in topo_order: cyclic blocks (in loops,
        // excluded by Kahn's algorithm) and unreachable blocks (cleanup/unwind
        // blocks only reachable via unwind edges, which Cfg omits from successors).
        // Both categories need processing — cleanup blocks may have block_relations.
        for bb in 0..ctx.body.blocks.len() {
            if !topo_set.contains(&bb) {
                order.push(bb);
            }
        }
        order
    };

    // Contract-shim dead-island skip: blocks with no path from bb0 over ANY
    // MIR successor edge (including unwind/cleanup) are statically
    // unexecutable. Contract instrumentation keeps the unused closure island
    // in the harness MIR (check-mode body under a replace harness and vice
    // versa); encoding those blocks emits rules that orphan-pruning removes
    // from the final VC anyway, but the sound-fallback / translation-drop
    // counters recorded while encoding them phantom-demote live proofs to
    // OverApproximation. Skipping statically unreachable blocks is
    // behavior-preserving on the live VC and keeps the demotion nets exact.
    let entry_reachable = entry_reachable_blocks(ctx.body);

    for bb_idx in block_order {
        let Some(from_rel) = ctx.block_relations.get(&bb_idx).cloned() else {
            continue;
        };

        if !entry_reachable.contains(&bb_idx) {
            debug!(bb_idx, "[block] skipping statically unreachable block (dead contract island)");
            continue;
        }

        // Debug: trace block processing (#1889)
        debug!("[block] bb{} terminator={:?}", bb_idx, ctx.body.blocks[bb_idx].terminator.kind);

        // Encode block statements to get constraints, output state, and modified locals (#648, #656)
        let (stmt_constraints, output_args, modified_locals, safety_checks) =
            ctx.encode_block_statements(bb_idx);

        // Part of #3691: Build from_app AFTER encode_block_statements.
        // Late-created type arrays (via push_late_state_var_pair) extend
        // live_state_indices and relation declarations during encoding.
        // Building from_app before encoding produces stale arity that
        // causes sort mismatches after per-block pruning.
        let from_app = RelationApp::new(&from_rel, ctx.project_state_args(bb_idx));

        // Part of #112 Direction 2: When int_lift is enabled, add range bounds
        // (0 <= var < 2^width) for all Int-lifted BV variables. This prevents
        // PDR from picking Int values outside the unsigned BV range.
        let range_bounds = ctx.int_lift_range_constraints(bb_idx);
        let mut all_constraints: Vec<Expr> = if range_bounds.is_empty() {
            stmt_constraints
        } else {
            let mut combined = range_bounds;
            combined.extend(stmt_constraints);
            combined
        };

        // Part of #3207: Z3 PDR requires explicit ((_ is Constructor) x) guards
        // before using datatype accessor functions on multi-constructor types.
        let guards = collect_constructor_guards(&all_constraints);
        all_constraints.extend(guards);

        // Part of #2507: Wrap block constraints in Arc for O(1) sharing across
        // all rules emitted from this block. For SwitchInt with K branches,
        // this avoids K-1 full copies of the constraint vector.
        let shared_constraints: Arc<[Expr]> = all_constraints.into();
        let tctx = TransitionContext {
            from_app: &from_app,
            output_args: &output_args,
            shared_constraints: &shared_constraints,
            modified_locals: &modified_locals,
            bb_idx,
        };

        // Emit memory safety error rules for any checks gathered during statement
        // encoding. A check that `push_copy_nonoverlapping_span_checks` marked
        // eligible (`span_check_exprs`: the precise, provenance-independent
        // alignment / count-overflow / allocation-bound obligations of a
        // copy_nonoverlapping statement) has its per-property relation tagged so
        // `translate()` can discharge this function's offset-provenance doubt if
        // scalarization later folds it to a DEFINITE violation — a genuine bug
        // (see `ChcDiagnostics::intrinsic_span_property_ids`). The disjointness
        // obligation is intentionally NOT eligible (spurious for `copy`).
        for check in safety_checks {
            let eligible = ctx.diagnostics.span_check_exprs.contains(&check);
            let id_before = ctx.vc.properties.len();
            ctx.emit_error_rule_for_condition_shared(&from_app, check, &shared_constraints, bb_idx);
            if eligible && ctx.vc.properties.len() == id_before + 1 {
                ctx.diagnostics.intrinsic_span_property_ids.push(id_before as u32);
            }
        }
        // Kinded checks (explicit PropertyKind + Kani-parity message), e.g. the
        // rvalue-offset lane's isize-overflow obligations: emit with the kinded
        // API so the check gets a named per-property line + exact-derivation
        // attribution instead of the anonymous aggregate.
        let kinded: Vec<_> = ctx.heap_state.pending_kinded_checks.drain(..).collect();
        for (cond, kind, msg) in kinded {
            ctx.emit_error_rule_for_condition_with_kind(
                &from_app,
                cond,
                &shared_constraints,
                bb_idx,
                kind,
                msg,
            );
        }

        dispatch_block_terminator(ctx, &tctx);
    }
}

/// Dispatch the terminator of a basic block, emitting CHC rules for each
/// successor edge.
///
/// Shared between Small-mode per-block rule generation and Large-mode
/// fragment composition (dispatches the last block's terminator with
/// composed constraints).
///
/// Part of #112: shared terminator dispatch for fragment composition.
pub(in crate::codegen_ay::chc) fn dispatch_block_terminator(
    ctx: &mut ChcCtx<'_, '_>,
    tctx: &TransitionContext<'_>,
) {
    let bb_data = &ctx.body.blocks[tctx.bb_idx];
    match &bb_data.terminator.kind {
        TerminatorKind::Goto { target } => {
            ctx.emit_goto_rule_shared(
                tctx.from_app,
                *target,
                tctx.output_args,
                tctx.shared_constraints,
            );
        }

        TerminatorKind::SwitchInt { discr, targets } => {
            codegen_switchint(ctx, discr, targets, tctx);
        }

        TerminatorKind::Return => {
            // Part of #3052: Emit a self-transition rule for return blocks so
            // statement constraints (e.g., `_0 = Copy(_1.0)` from Pattern 5
            // field projections) are captured in the VC. Without this,
            // single-block functions have their assignment constraints
            // discarded, producing vacuously true VCs.
            let has_nontrivial = tctx
                .shared_constraints
                .iter()
                .any(|c| !matches!(c.value(), ay_bindings::ExprValue::BoolConst(true)));
            if has_nontrivial {
                let projected = ctx.project_full_output_to_block(tctx.bb_idx, tctx.output_args);
                if let Some(to_rel) = ctx.block_relations.get(&tctx.bb_idx).map(|s| &**s) {
                    let to_app = RelationApp::new(to_rel, projected);
                    let body = RuleBody::from_shared_base(
                        Some(tctx.from_app.clone()),
                        Arc::clone(tctx.shared_constraints),
                        [],
                    );
                    ctx.vc.add_rule(Rule::new(body, to_app));
                    debug!(
                        bb_idx = tctx.bb_idx,
                        n_constraints = tctx.shared_constraints.len(),
                        "return terminator - emitted self-transition with constraints"
                    );
                } else {
                    warn!(
                        bb_idx = tctx.bb_idx,
                        "return terminator - block relation missing, constraints discarded"
                    );
                }
            } else {
                debug!(bb_idx = tctx.bb_idx, "return terminator - no non-trivial constraints");
            }
        }

        TerminatorKind::Unreachable => {
            // Emit unconditional error rule: reachable unreachable is a bug.
            // Matches BMC behavior (record_violation_guarded(true, "unreachable")).
            // Part of #3015.
            let error_app = RelationApp::new("error", Vec::new());
            let body = RuleBody::from_shared_base(
                Some(tctx.from_app.clone()),
                Arc::clone(tctx.shared_constraints),
                [],
            );
            ctx.vc.add_rule(Rule::new(body, error_app));
            debug!(bb_idx = tctx.bb_idx, "unreachable terminator - error rule emitted");
        }

        TerminatorKind::Drop { place, target, unwind: _, .. } => {
            super::transition_drop::codegen_drop(ctx, place, *target, tctx);
            // Part of #3783: suppress Drop unwind edge.
            // `codegen_drop()` models the drop semantics (precise inlining or
            // sound fallback). The unwind edge represents "Drop::drop() panics"
            // — a second-order failure mode we don't model. Emitting it
            // unconditionally creates spurious error() reachability through
            // Resume/Abort for harnesses with live cleanup blocks (same pattern
            // as the Assert unwind fix above, and consistent with #3470 which
            // suppresses Call unwind edges for dispatched calls).
        }

        TerminatorKind::Call { func, args, destination, target, unwind, .. } => {
            let callee_path = ctx.resolve_callee_path(func);
            let dcx = DispatchCallContext {
                bb_idx: tctx.bb_idx,
                func,
                args,
                destination,
                target,
                from_app: tctx.from_app,
                stmt_constraints: tctx.shared_constraints,
                modified_locals: tctx.modified_locals,
                callee_path,
            };
            let dispatched = ctx.codegen_call_terminator(&dcx);
            // Part of #3470: suppress unwind edges for dispatched non-diverging calls.
            // Those handlers fully model the normal-return semantics and an extra
            // cleanup edge creates spurious error() reachability.
            // Part of #3301: preserve unwind edges for fallthrough calls AND
            // diverging dispatched calls (target=None), whose cleanup path is the
            // only continuation after panic.
            if !dispatched || dcx.target.is_none() {
                emit_unwind_edge(ctx, tctx, unwind);
            }
        }

        TerminatorKind::Assert { cond, expected, msg, target, unwind, .. } => {
            let failure_guard = codegen_assert(ctx, cond, *expected, msg, *target, tctx);
            // Part of #3783: condition the unwind edge on assertion failure.
            // Without the guard, the cleanup path is unconditionally reachable,
            // creating a spurious error() path through Resume/Abort even when
            // the assertion holds. This caused CTREX in harnesses with live
            // cleanup blocks (e.g., Vec allocation drop cleanup).
            emit_assert_unwind_edge(ctx, tctx, unwind, failure_guard.as_ref());
        }

        TerminatorKind::Resume | TerminatorKind::Abort => {
            // Part of #3301: fail-closed error rule for panic-unwind cleanup paths.
            debug!(bb_idx = tctx.bb_idx, "resume/abort terminator - emitting error rule");
            ctx.emit_untranslatable_assert_rule_shared(
                tctx.from_app,
                tctx.shared_constraints,
                tctx.bb_idx,
                "TerminatorKind::Resume/Abort",
            );
            // Part of #3814: upgrade to reason-coded recording.
            ctx.record_sound_fallback_reason("resume_abort");
        }

        TerminatorKind::InlineAsm { destination: Some(target), operands, template, .. }
            if operands.is_empty() && is_nop_inline_asm_template(template) =>
        {
            // Operand-free fallthrough inline asm, such as `asm!("nop")`, has no
            // MIR-visible state effects. Preserve control flow as a no-op edge.
            ctx.emit_goto_rule_shared(
                tctx.from_app,
                *target,
                tctx.output_args,
                tctx.shared_constraints,
            );
        }

        TerminatorKind::InlineAsm { destination, .. } => {
            warn!(bb_idx = tctx.bb_idx, "inline asm not supported in CHC mode");
            // Fail-closed: emit conservative error rule so InlineAsm blocks
            // never produce vacuous PROOF results. Part of #2756.
            ctx.emit_untranslatable_assert_rule_shared(
                tctx.from_app,
                tctx.shared_constraints,
                tctx.bb_idx,
                "TerminatorKind::InlineAsm",
            );
            // SOUND AUDIT (#3369): InlineAsm may modify locals not in output_args;
            // those retain identity (under-approx), not universally quantified.
            // Reclassified from record_sound_fallback (was #3099).
            ctx.record_fallback();
            // Preserve reachability: if InlineAsm has a fallthrough
            // destination, emit a successor edge so downstream blocks
            // remain reachable for verification.
            if let Some(target) = destination {
                ctx.emit_goto_rule_shared(
                    tctx.from_app,
                    *target,
                    tctx.output_args,
                    tctx.shared_constraints,
                );
            }
        }
    }
}

fn is_nop_inline_asm_template(template: &str) -> bool {
    template == r#"[String("nop")]"#
}

/// Blocks reachable from `bb0` over ALL MIR successor edges, including
/// unwind/cleanup edges (`Terminator::successors` covers goto/switch/call/
/// assert/drop targets plus `UnwindAction::Cleanup` landing pads).
///
/// Used to skip statically unexecutable blocks — dead contract-closure
/// islands would otherwise record phantom sound-fallback counters that
/// demote live proofs (their rules are orphan-pruned regardless).
fn entry_reachable_blocks(body: &rustc_public::mir::Body) -> std::collections::HashSet<usize> {
    let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut work = vec![0usize];
    seen.insert(0);
    while let Some(bb) = work.pop() {
        for succ in body.blocks[bb].terminator.successors() {
            if succ < body.blocks.len() && seen.insert(succ) {
                work.push(succ);
            }
        }
    }
    seen
}
