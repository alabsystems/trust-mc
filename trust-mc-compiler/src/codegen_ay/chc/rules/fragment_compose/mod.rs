// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Fragment composition engine for large-step CHC encoding (#112).
//!
//! Composes a linear chain of basic blocks [B0, B1, ..., BN-1] into a single
//! CHC rule by name-swapping intermediate state variables. Intermediate
//! variables are existentially quantified by CHC semantics.
//!
//! Extracted from `fragment_gen.rs` as part of #3199.

use std::collections::HashSet;
use std::sync::Arc;

use ay_bindings::Expr;
use rustc_public::mir::{Operand, TerminatorKind};
use tracing::{debug, warn};

use super::ChcCtx;
use super::codegen_rules::{TransitionContext, dispatch_block_terminator};
use super::collect_constructor_guards;
use super::fragment_gen::{InlineableCallKind, classify_inlineable_call};
use super::fragment_switchint::{
    SwitchIntExitContext, compose_range_next_constraints, emit_intermediate_switchint_exits,
    emit_unguarded_switchint_exits, switchint_guard_for_target,
};
use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;
use trust_mc_core::chc::{RelationApp, VarDecl};

/// Generate composed rules for a linear chain fragment via name-swapping.
///
/// For a chain [B0, B1, ..., BN-1]:
/// - B0 encodes with original input names, intermediate output `__mid_bb{B0}`
/// - B1..BN-2 encode with `__mid_bb{prev}` input, `__mid_bb{current}` output
/// - BN-1 encodes with `__mid_bb{prev}` input, original `__out` output
///
/// Unmodified state variables get explicit frame constraints linking each
/// intermediate point to the previous one. Modified variables are already
/// constrained by the block's encoding. Intermediate variables are
/// existentially quantified by CHC semantics.
///
/// The last block's terminator is dispatched with the accumulated constraints
/// to emit rules for each exit edge.
pub(super) fn generate_composed_rules(ctx: &mut ChcCtx<'_, '_>, entry_bb: usize, blocks: &[usize]) {
    debug_assert!(!blocks.is_empty(), "generate_composed_rules called with empty blocks");
    if blocks.is_empty() {
        return;
    }
    let Some(from_rel) = ctx.block_relations.get(&entry_bb).map(Arc::clone) else {
        return;
    };

    let pre_encode_var_count = ctx.state_var_mgr.state_vars.len();
    debug!(
        entry_bb,
        block_count = blocks.len(),
        chain = ?blocks,
        "generating composed large-step rules for linear chain"
    );
    // Composition semantics REQUIRE blocks[i] to flow into blocks[i+1]: each
    // segment's inputs are named `__mid_bb{blocks[i-1]}`. A list that is not
    // the actual control-flow path produces frame chains between unrelated
    // blocks, leaving the real path unconstrained (state havoc at the head —
    // observed as spurious loop-contract counterexamples, #44). Verify the
    // successor property and fail closed to per-block rules if violated.
    for w in blocks.windows(2) {
        let succs = ctx.body.blocks[w[0]].terminator.successors();
        if !succs.contains(&w[1]) {
            warn!(
                entry_bb,
                from = w[0],
                to = w[1],
                chain = ?blocks,
                "composed chain is not a control-flow path; falling back to per-block rules (#44)"
            );
            for &bb in blocks {
                super::fragment_fallback::declare_block_relation_if_needed(ctx, bb);
            }
            for &bb in blocks {
                super::fragment_gen::generate_single_block_rules(ctx, bb);
            }
            return;
        }
    }
    // Save original state variable names for restoration.
    let original_input_names: Vec<Arc<str>> =
        ctx.state_var_mgr.state_vars.iter().map(|(name, _)| Arc::clone(name)).collect();
    let original_output_names: Vec<Arc<str>> =
        ctx.state_var_mgr.output_state_vars.iter().map(|(name, _)| Arc::clone(name)).collect();

    // Part of #3157: Protect name-swapping with catch_unwind — a panic between
    // set_names_to_mid and restore_names would leave corrupted __mid_bb{N} names.
    let composition_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut all_constraints: Vec<Expr> = Vec::new();
        let mut all_safety_checks: Vec<Expr> = Vec::new();
        let mut last_output_args: Vec<Expr> = Vec::new();
        let mut last_block_modified: HashSet<usize> = HashSet::new();
        let last_block_idx = blocks.len() - 1;

        for (i, &bb_idx) in blocks.iter().enumerate() {
            let is_first = i == 0;
            let is_last = i == last_block_idx;

            ctx.fragment_mid_output_bb = (!is_last).then_some(bb_idx);

            // Swap input names: first block keeps original __in; others use __mid_bb{prev}.
            if !is_first {
                let prev_bb = blocks[i - 1];
                set_names_to_mid(ctx, prev_bb, true);
            }

            // Swap output names: last block restores original __out; others use __mid_bb{current}.
            if !is_last {
                set_names_to_mid(ctx, bb_idx, false);
            } else {
                restore_names(ctx, &original_output_names, false);
            }

            let (constraints, output_args, mut modified, safety_checks) =
                ctx.encode_block_statements(bb_idx);

            // Part of #3696: fresh from_app after encode captures late state vars.
            let from_app = rebuild_entry_from_app(
                ctx,
                entry_bb,
                &from_rel,
                &original_input_names,
                pre_encode_var_count,
            );

            all_constraints.extend(constraints);
            all_safety_checks.extend(safety_checks);

            // Part of #112: For non-last blocks, add Call destination to `modified`.
            // Snapshot before adding so RangeNext resolves iterator to INPUT names.
            let pre_call_modified = modified.clone();
            if !is_last {
                if let TerminatorKind::Call { func, destination, args, .. } =
                    &ctx.body.blocks[bb_idx].terminator.kind
                {
                    if let Some(kind) = classify_inlineable_call(ctx, func) {
                        modified.insert(destination.local);
                        if matches!(kind, InlineableCallKind::RangeNext) {
                            // Mark iterator receiver local as modified.
                            if let Some(Operand::Copy(place) | Operand::Move(place)) = args.first()
                            {
                                let ref_local: usize = place.local;
                                let iter_local = ctx
                                    .ref_resolution
                                    .ref_targets
                                    .get(&ref_local)
                                    .map_or(ref_local, |rt| rt.local);
                                modified.insert(iter_local);
                            }
                        }
                    }
                }
            }

            // Frame constraints for unmodified state vars: link __mid to __in.
            if !is_last {
                let modified_vec = build_modified_vec_indices(ctx, &modified);
                let mut frames_emitted = 0usize;
                for (idx, out_arg) in output_args.iter().enumerate() {
                    if modified_vec.contains(&idx) {
                        continue;
                    }
                    let (out_name, out_sort) = &ctx.state_var_mgr.output_state_vars[idx];
                    let mid_var = Expr::var(&**out_name, out_sort.clone());
                    all_constraints.push(mid_var.eq(out_arg.clone()));
                    frames_emitted += 1;
                }
                debug!(
                    bb_idx,
                    frames_emitted,
                    outputs = output_args.len(),
                    modified = modified_vec.len(),
                    constraints_total = all_constraints.len(),
                    sample_out = ?ctx.state_var_mgr.output_state_vars.first().map(|(n, _)| n.to_string()),
                    "fragment segment encoded"
                );
            }

            if is_last {
                last_output_args = output_args;
                last_block_modified = modified;
            } else {
                // Part of #112: intermediate terminator guard extraction + exit rules.
                let bb_data = &ctx.body.blocks[bb_idx];
                match &bb_data.terminator.kind {
                    TerminatorKind::Goto { .. } | TerminatorKind::Drop { .. } => {
                        // No guard needed — path continues linearly.
                    }
                    TerminatorKind::SwitchInt { discr, targets } => {
                        let next_bb = blocks[i + 1]; // in-fragment successor
                        if let Some(discr_expr) =
                            ctx.translate_operand_with_modified(discr, &modified)
                        {
                            // Emit exit rules for out-of-fragment SwitchInt targets.
                            let snapshot: Arc<[Expr]> = all_constraints.clone().into();
                            let exit_ctx = SwitchIntExitContext {
                                from_app: &from_app,
                                output_args: &output_args,
                                accumulated_constraints: &snapshot,
                                bb_idx,
                            };
                            emit_intermediate_switchint_exits(
                                ctx,
                                &discr_expr,
                                targets,
                                next_bb,
                                &exit_ctx,
                            );

                            // Add the in-fragment path guard as a composition constraint.
                            if let Some(guard) =
                                switchint_guard_for_target(&discr_expr, targets, next_bb, bb_idx)
                            {
                                all_constraints.push(guard);
                            }
                        } else {
                            // Fail-closed: emit unguarded exit rules (#3265).
                            warn!(
                                bb = bb_idx,
                                "fragment composition: SwitchInt discriminant translation failed; \
                                 emitting unguarded exit rules for out-of-fragment targets"
                            );
                            let snapshot: Arc<[Expr]> = all_constraints.clone().into();
                            emit_unguarded_switchint_exits(
                                ctx,
                                &from_app,
                                targets,
                                next_bb,
                                &output_args,
                                &snapshot,
                                bb_idx,
                            );
                        }
                    }
                    TerminatorKind::Assert { cond, expected, msg, .. } => {
                        if let Some(bool_cond) =
                            ctx.translate_assert_condition(cond, &modified, bb_idx)
                        {
                            let guard = if *expected { bool_cond } else { bool_cond.not() };

                            // Emit error rule for assertion violation at this intermediate point.
                            let snapshot: Arc<[Expr]> = all_constraints.clone().into();
                            ctx.emit_assert_error_rule_shared(
                                &from_app,
                                guard.clone(),
                                true,
                                &snapshot,
                                bb_idx,
                                Some(msg),
                            );

                            // Add success guard as composition constraint (path continues
                            // only when the assertion holds).
                            all_constraints.push(guard);
                        } else {
                            // Nondet choice: emit error AND continue (P1:1437 fix).
                            ctx.diagnostics.assert_untranslatable.inc();
                            debug!(
                                ?bb_idx,
                                "fragment composition: Assert untranslatable, \
                                 non-deterministic choice (error ∨ successor)"
                            );
                            let snapshot: Arc<[Expr]> = all_constraints.clone().into();
                            ctx.emit_untranslatable_assert_rule_shared(
                                &from_app,
                                &snapshot,
                                bb_idx,
                                "fragment composition: untranslatable Assert condition",
                            );
                            // Path continues without guard (unconstrained).
                        }
                    }
                    TerminatorKind::Call { func, args, destination, .. } => {
                        // Part of #112: compose inlineable call effects after marking the
                        // destination as modified above.
                        match classify_inlineable_call(ctx, func) {
                            Some(InlineableCallKind::Assume) => {
                                // kani::assume(cond): the path continues only when the guard holds.
                                if let Some(bool_cond) = args.first().and_then(|cond| {
                                    ctx.translate_assert_condition(cond, &modified, bb_idx)
                                }) {
                                    all_constraints.push(bool_cond);
                                }
                                if let Some(dest_eq) = ctx.canonical_zst_call_dest_constraint(
                                    destination.local,
                                    "fragment_compose::kani_assume::zst_dest",
                                ) {
                                    all_constraints.push(dest_eq);
                                }
                            }
                            Some(InlineableCallKind::AssertOrCheck) => {
                                // kani::assert/check(cond): emit error rule for
                                // condition violation, add success guard.
                                if let Some(bool_cond) = args.first().and_then(|cond| {
                                    ctx.translate_assert_condition(cond, &modified, bb_idx)
                                }) {
                                    let snapshot: Arc<[Expr]> = all_constraints.clone().into();
                                    // kani::assert/check: genuine assertion (panic) kind.
                                    ctx.emit_assert_error_rule_shared(
                                        &from_app,
                                        bool_cond.clone(),
                                        true,
                                        &snapshot,
                                        bb_idx,
                                        None,
                                    );
                                    all_constraints.push(bool_cond);
                                } else {
                                    // Fail-closed: same pattern as Assert terminator
                                    // (#3256). Emit conservative error rule so the
                                    // solver reports FAILURE instead of a false PROOF.
                                    let snapshot: Arc<[Expr]> = all_constraints.clone().into();
                                    ctx.emit_untranslatable_assert_rule_shared(
                                        &from_app,
                                        &snapshot,
                                        bb_idx,
                                        "fragment composition: kani::assert/check condition \
                                         translation failed",
                                    );
                                }
                            }
                            Some(InlineableCallKind::Cover) => {
                                // Part of #1162: Register cover property on ChcVc.
                                // No path constraints — control flow passes through.
                                if let Some(bool_cond) = args.first().and_then(|cond| {
                                    ctx.translate_assert_condition(cond, &modified, bb_idx)
                                }) {
                                    let cover_id = ctx.vc.cover_assertions.len();
                                    let name = format!("ay_cover_{cover_id}");
                                    ctx.vc.add_cover_assertion(name, bool_cond);
                                }
                            }
                            Some(InlineableCallKind::Noop) => {
                                // No constraints — destination is free, no side effects.
                            }
                            Some(InlineableCallKind::Any) => {
                                // Destination is free (nondet). Part of #112 Direction 2
                                // step 3: bound nondet output to BV range when Int-lifted.
                                // Note: At Mem track level, classify_inlineable_call returns
                                // None for kani::any(), so this branch is only reached at
                                // Var/Ref levels where no memory store is needed.
                                if let TerminatorKind::Call { destination, .. } =
                                    &ctx.body.blocks[bb_idx].terminator.kind
                                {
                                    all_constraints
                                        .extend(ctx.int_lift_nondet_bounds(destination.local));
                                }
                            }
                            Some(InlineableCallKind::RangeNext) => {
                                // Part of #112: compose through Range::spec_next.
                                // Build constraints for both the destination (Option
                                // result) and the iterator state (start += 1).
                                // Uses pre_call_modified so the iterator expression
                                // resolves to INPUT names, not OUTPUT names.
                                if let TerminatorKind::Call { destination, .. } =
                                    &ctx.body.blocks[bb_idx].terminator.kind
                                {
                                    if !compose_range_next_constraints(
                                        ctx,
                                        args,
                                        destination.local,
                                        &pre_call_modified,
                                        &mut all_constraints,
                                        bb_idx,
                                    ) {
                                        let snapshot: Arc<[Expr]> = all_constraints.clone().into();
                                        ctx.emit_untranslatable_assert_rule_shared(
                                            &from_app,
                                            &snapshot,
                                            bb_idx,
                                            "fragment composition: RangeNext translation failed",
                                        );
                                    }
                                }
                            }
                            None => {
                                warn!(
                                    bb_idx,
                                    "unexpected non-inlineable Call in composable fragment"
                                );
                            }
                        }
                    }
                    _ => {
                        // Should not happen — is_composable_fragment rejects other terminators.
                        warn!(bb_idx, "unexpected intermediate terminator in composable fragment");
                    }
                }
            }
        }

        // Part of #3207: Z3 PDR requires explicit ((_ is Constructor) x) guards
        // before using datatype accessor functions on multi-constructor types.
        let guards = collect_constructor_guards(&all_constraints);
        all_constraints.extend(guards);

        let shared_constraints: Arc<[Expr]> = all_constraints.into();

        // Part of #3696: Final from_app rebuild for post-loop dispatch.
        let from_app = rebuild_entry_from_app(
            ctx,
            entry_bb,
            &from_rel,
            &original_input_names,
            pre_encode_var_count,
        );

        // Emit error rules for safety checks (baked Exprs, name-safe).
        for check in all_safety_checks {
            ctx.emit_error_rule_for_condition_shared(
                &from_app,
                check,
                &shared_constraints,
                entry_bb,
            );
        }

        // Dispatch last block's terminator BEFORE restoring names (R1:2614).
        // state_var_mgr has __mid_bb{prev} inputs and __out outputs here.
        // Use last_block_modified (not all) so earlier-modified vars resolve
        // to __mid_bb{prev} (constrained), not __out (free).
        let last_bb = blocks[last_block_idx];
        let tctx = TransitionContext {
            from_app: &from_app,
            output_args: &last_output_args,
            shared_constraints: &shared_constraints,
            modified_locals: &last_block_modified,
            bb_idx: last_bb,
        };
        dispatch_block_terminator(ctx, &tctx);
    })); // end catch_unwind (Part of #3157)

    // Unconditionally restore all original names — even after panic.
    ctx.fragment_mid_output_bb = None;
    restore_names(ctx, &original_input_names, true);
    restore_names(ctx, &original_output_names, false);

    if let Err(panic) = composition_result {
        std::panic::resume_unwind(panic);
    }
}

/// Rebuild entry relation app with current arity. Pre-existing vars use saved
/// `__in` names; late vars use base name (stripped of `__mid_bb*`). Part of #3696.
fn rebuild_entry_from_app(
    ctx: &ChcCtx<'_, '_>,
    entry_bb: usize,
    from_rel: &Arc<str>,
    original_input_names: &[Arc<str>],
    pre_encode_var_count: usize,
) -> RelationApp {
    RelationApp::new(
        &**from_rel,
        ctx.state_var_mgr.live_state_indices[entry_bb]
            .iter()
            .map(|&idx| {
                let sort = &ctx.state_var_mgr.state_vars[idx].1;
                let name: &str = if idx < pre_encode_var_count {
                    &original_input_names[idx]
                } else {
                    state_var_mid_base(&ctx.state_var_mgr.state_vars[idx].0)
                };
                Expr::var(name, sort.clone())
            })
            .collect(),
    )
}

/// Set input or output state variable names to `__mid_bb{bb_idx}`.
fn set_names_to_mid(ctx: &mut ChcCtx<'_, '_>, bb_idx: usize, is_input: bool) {
    let vc = &mut ctx.vc;
    let vars = if is_input {
        &mut ctx.state_var_mgr.state_vars
    } else {
        &mut ctx.state_var_mgr.output_state_vars
    };
    use std::fmt::Write;
    let mut buf = String::new();
    for (name, sort) in vars.iter_mut() {
        let base_name = state_var_mid_base(name.as_ref());
        buf.clear();
        buf.push_str(base_name);
        buf.push_str("__mid_bb");
        let _ = write!(buf, "{bb_idx}");
        vc.add_var(VarDecl::new(buf.as_str(), sort.clone()));
        *name = Arc::from(buf.as_str());
    }
}

/// Restore state variable names from saved originals.
fn restore_names(ctx: &mut ChcCtx<'_, '_>, originals: &[Arc<str>], is_input: bool) {
    let vars = if is_input {
        &mut ctx.state_var_mgr.state_vars
    } else {
        &mut ctx.state_var_mgr.output_state_vars
    };
    for (idx, (name, _sort)) in vars.iter_mut().enumerate() {
        if let Some(original) = originals.get(idx) {
            *name = Arc::clone(original);
            continue;
        }

        let base = state_var_mid_base(name.as_ref());
        let restored =
            if is_input { base.to_owned() } else { crate::codegen_ay::names::out_name(base) };
        *name = Arc::from(restored);
    }
}

fn state_var_mid_base(name: &str) -> &str {
    if let Some(base) = name.strip_suffix("__in") {
        return base;
    }
    if let Some(base) = name.strip_suffix("__out") {
        return base;
    }
    if let Some((base, suffix)) = name.rsplit_once("__mid_bb")
        && suffix.bytes().all(|b| b.is_ascii_digit())
    {
        return base;
    }
    name
}

/// Compute the set of state var indices modified by a block.
///
/// Combines MIR-local modifications (from `encode_block_statements`) with
/// state-level modifications (from `encode.modified_state_indices`), matching
/// the logic in `build_block_output_args`.
fn build_modified_vec_indices(
    ctx: &ChcCtx<'_, '_>,
    modified_locals: &HashSet<usize>,
) -> HashSet<usize> {
    let mut indices = HashSet::new();
    for &local_idx in modified_locals {
        let Some(vec_idx) = ctx.try_state_idx_for_local(local_idx) else {
            continue;
        };
        indices.insert(vec_idx);
        if ctx.flatten.flattened_tuple_locals.contains(&local_idx) {
            let n = ctx.flattened_field_count(local_idx);
            for j in 1..n {
                indices.insert(vec_idx + j);
            }
        }
    }
    indices.extend(ctx.encode.modified_state_indices.iter());
    indices
}

#[cfg(test)]
mod tests;
