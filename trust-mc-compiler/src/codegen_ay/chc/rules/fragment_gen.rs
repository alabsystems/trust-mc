// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Fragment-based CHC rule generation for large-step encoding (#112).
//!
//! When `ChcStepMode::Large` is active, this module generates CHC rules at
//! fragment granularity instead of per basic block:
//!
//! - **Single-block fragments**: delegate to per-block rule generation.
//! - **Composable linear chains** (all intermediate blocks have Goto terminators):
//!   compose block constraints via intermediate variable naming and dispatch
//!   the last block's terminator with the accumulated constraints.
//! - **Non-composable fragments** (internal branching/calls): fallback to
//!   declaring intermediate block relations and per-block rule generation.
//!
//! For `Small` mode, the existing per-block generation in `transition_gen.rs`
//! is used instead.
//!
//! The composition engine, fallback strategies, and SwitchInt/Range::next
//! handling are in sibling modules split out as part of #3199:
//! - `fragment_compose` — composition engine + name helpers
//! - `fragment_fallback` — sub-fragment splitting + per-block fallback
//! - `fragment_switchint` — SwitchInt guards + Range::next composition

use std::collections::HashSet;
use std::sync::Arc;

use ay_bindings::Expr;
use rustc_public::mir::{Operand, TerminatorKind};
use tracing::debug;

use crate::args::ChcTrackLevel;
use crate::codegen_ay::stubs::StubKind;

use super::ChcCtx;
use super::codegen_rules::{CodegenRules, TransitionContext, dispatch_block_terminator};
use super::codegen_rules_helpers::CodegenRulesHelpers;
use super::collect_constructor_guards;
use super::fragment_compose::generate_composed_rules;
use super::fragment_fallback::{
    declare_block_relation_if_needed, generate_fallback_fragment_rules,
};
use super::{KaniHook, KaniModel};

/// Classification of Call terminators that can be inlined during fragment
/// composition instead of requiring sub-fragment splitting.
///
/// Part of #112: Call-through composition reduces predicate count by composing
/// through kani stub calls (any, assume) instead of creating separate relations
/// for each Call block. This can reduce predicates from ~10 to ~3, enabling
/// PDR convergence on harnesses that currently time out as UNKNOWN.
#[derive(Debug, Clone, Copy)]
pub(super) enum InlineableCallKind {
    /// `kani::any()` / `KaniHook::AnyRaw` — destination local is unconstrained
    /// (nondeterministic). No constraint added; the intermediate variable is
    /// existentially quantified by CHC semantics.
    Any,
    /// `kani::assume(cond)` — condition becomes a guard constraint on the
    /// composed rule. Path continues only when the condition holds.
    Assume,
    /// `kani::assert(cond)` / `KaniHook::Check` — emit error rule for
    /// condition violation, add success guard as constraint.
    AssertOrCheck,
    /// `kani::cover!(cond)` — registers cover property on ChcVc. No path
    /// constraints; control flow passes through like a noop. Part of #1162.
    Cover,
    /// No-op transitions (InitContracts, ValueView, UntrackedDeref) —
    /// no constraints, destination unconstrained.
    Noop,
    /// `Range<T>::spec_next` — range iterator advancement. Constrains both
    /// the destination (Option result) and the iterator state (start += 1).
    /// Part of #112: composing through Range::next eliminates the sub-fragment
    /// split that prevents loop body composition for `for` loops.
    RangeNext,
}

/// Classify a Call terminator's function operand as inlineable for composition.
///
/// Returns `Some(kind)` if the call is a kani stub that can be inlined during
/// fragment composition, `None` if the call requires full dispatch (sub-fragment
/// splitting or per-block fallback).
///
/// At `Mem` track level, `kani::any()` has heap side effects (memory store,
/// pending updates) that cannot be inlined. The `Any` variant is only returned
/// when `track_level < Mem`.
pub(super) fn classify_inlineable_call(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
) -> Option<InlineableCallKind> {
    // Check kani models first (kani::any() is the most common inlineable call).
    // At Mem track level, kani::any() has heap side effects (memory store +
    // pending updates) that can't be composed through.
    if let Some(KaniModel::Any) = ctx.detect_kani_model(func) {
        if ctx.track_level < ChcTrackLevel::Mem {
            return Some(InlineableCallKind::Any);
        }
    }

    // Check kani hooks.
    if let Some(hook) = ctx.detect_kani_hook(func) {
        match hook {
            KaniHook::Assume => return Some(InlineableCallKind::Assume),
            KaniHook::AnyRaw => {
                if ctx.track_level >= ChcTrackLevel::Mem {
                    return None;
                }
                return Some(InlineableCallKind::Any);
            }
            KaniHook::Assert | KaniHook::Check => {
                return Some(InlineableCallKind::AssertOrCheck);
            }
            KaniHook::Cover => {
                return Some(InlineableCallKind::Cover);
            }
            KaniHook::InitContracts | KaniHook::ValueView | KaniHook::UntrackedDeref => {
                return Some(InlineableCallKind::Noop);
            }
            _ => {} // SafetyCheck, Panic, etc. are complex.
        }
    }

    // Check iterator adapter stubs (Range::spec_next).
    // Part of #112: composing through Range::next eliminates the sub-fragment
    // split that prevents loop body composition for `for` loops.
    if let Some(StubKind::RangeSpecNext) = ctx.detect_stub(func) {
        return Some(InlineableCallKind::RangeNext);
    }

    None
}

/// Generate CHC transition rules using large-step fragment encoding.
///
/// Part of #112: SeaHorn-style large-step CHC encoding.
pub(in crate::codegen_ay::chc) fn generate_fragment_rules(ctx: &mut ChcCtx<'_, '_>) {
    // Part of #3839: Pre-scan all blocks for constant-foldable math intrinsic calls.
    // This must run before any block encoding so that cross-block constant
    // propagation works regardless of block encoding order.
    crate::codegen_ay::chc::call::codegen_call_cmp_string::math_const_prescan::prescan_const_foldable_math_calls(ctx);
    // Part of #3905: Identify single-assignment locals for safe cross-block propagation.
    crate::codegen_ay::chc::call::codegen_call_cmp_string::math_const_prescan::compute_single_assign_locals(ctx);

    let analysis = match ctx.fragment_analysis.as_ref() {
        Some(a) => a,
        None => {
            debug!(
                "generate_fragment_rules called without fragment analysis; \
                 falling back to small-step"
            );
            ctx.generate_transition_rules();
            return;
        }
    };

    // Clone fragment metadata to avoid borrow conflict with ctx methods.
    #[allow(clippy::type_complexity)]
    let fragments: Vec<(usize, Vec<usize>, Vec<(usize, usize)>)> = analysis
        .fragments
        .iter()
        .map(|f| (f.entry_bb, f.blocks.clone(), f.exits.clone()))
        .collect();

    for (entry_bb, blocks, exits) in &fragments {
        if blocks.len() == 1 {
            generate_single_block_rules(ctx, blocks[0]);
        } else if is_composable_linear_chain(ctx, blocks) {
            generate_composed_rules(ctx, *entry_bb, blocks);
        } else if let Some((path_blocks, dead_end_blocks)) =
            extract_composable_path(ctx, blocks, *entry_bb)
        {
            // Part of #112: dead-end blocks (exit branches) need separate
            // relations and rules, since they're excluded from composition.
            for &bb in &dead_end_blocks {
                declare_block_relation_if_needed(ctx, bb);
                generate_single_block_rules(ctx, bb);
            }
            generate_composed_rules(ctx, *entry_bb, &path_blocks);
        } else {
            generate_fallback_fragment_rules(ctx, blocks);
        }
        let _ = exits; // Exit edges are handled by the last block's terminator dispatch.
    }
}

/// Generate rules for a single-block fragment using per-block Small-mode logic.
pub(super) fn generate_single_block_rules(ctx: &mut ChcCtx<'_, '_>, bb_idx: usize) {
    let Some(from_rel) = ctx.block_relations.get(&bb_idx).cloned() else {
        return;
    };
    let (mut stmt_constraints, output_args, modified_locals, safety_checks) =
        ctx.encode_block_statements(bb_idx);
    // Part of #3691: Build from_app AFTER encode_block_statements to capture
    // late-created state vars. Same fix as transition_gen.rs.
    let from_app = trust_mc_core::chc::RelationApp::new(&from_rel, ctx.project_state_args(bb_idx));

    // Part of #3207: Z3 PDR requires explicit ((_ is Constructor) x) guards
    // before using datatype accessor functions on multi-constructor types.
    let guards = collect_constructor_guards(&stmt_constraints);
    stmt_constraints.extend(guards);

    let shared_constraints: Arc<[Expr]> = stmt_constraints.into();
    let tctx = TransitionContext {
        from_app: &from_app,
        output_args: &output_args,
        shared_constraints: &shared_constraints,
        modified_locals: &modified_locals,
        bb_idx,
    };
    for check in safety_checks {
        ctx.emit_error_rule_for_condition_shared(&from_app, check, &shared_constraints, bb_idx);
    }
    // Kinded checks — see transition_gen.rs; same drain for the fragment path.
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

/// Check if a fragment's blocks form a composable linear chain.
///
/// A linear chain requires all blocks except the last to have a `Goto`
/// terminator targeting the next block in topological order. The last block
/// can have any terminator — it's dispatched via `dispatch_block_terminator`.
pub(super) fn is_composable_linear_chain(ctx: &ChcCtx<'_, '_>, blocks: &[usize]) -> bool {
    if blocks.len() <= 1 {
        return true;
    }
    for i in 0..blocks.len() - 1 {
        let bb_idx = blocks[i];
        let next_bb = blocks[i + 1];
        let bb_data = &ctx.body.blocks[bb_idx];
        if !matches!(&bb_data.terminator.kind, TerminatorKind::Goto { target } if *target == next_bb)
        {
            return false;
        }
    }
    true
}

/// Compute dead-end blocks within a fragment.
///
/// A dead-end block has ALL successors outside the fragment and no back-edge
/// to the entry. These represent exit branches (e.g., the None path of a
/// SwitchInt on an Option discriminant in a for-loop body). Blocks with
/// back-edges to entry are valid last blocks, not dead-ends.
fn compute_dead_end_blocks(
    ctx: &ChcCtx<'_, '_>,
    blocks: &[usize],
    block_set: &HashSet<usize>,
    entry_bb: usize,
) -> HashSet<usize> {
    blocks
        .iter()
        .filter(|&&bb| {
            let succs = ctx.body.blocks[bb].terminator.successors();
            !succs.into_iter().any(|s| s == entry_bb || (block_set.contains(&s) && s != bb))
        })
        .copied()
        .collect()
}

/// Extract the composable path from a fragment, separating dead-end blocks.
///
/// Returns `Some((path_blocks, dead_end_blocks))` if the fragment has a
/// composable main path after excluding dead-end blocks, `None` otherwise.
///
/// Part of #112: enables full loop body composition for `for` loops by
/// excluding exit branches (e.g., None path of Option SwitchInt) from the
/// composable path and handling them as separate single-block rules.
fn extract_composable_path(
    ctx: &ChcCtx<'_, '_>,
    blocks: &[usize],
    entry_bb: usize,
) -> Option<(Vec<usize>, Vec<usize>)> {
    if !is_composable_fragment(ctx, blocks, entry_bb) {
        return None;
    }
    let block_set: HashSet<usize> = blocks.iter().copied().collect();
    let dead_end_set = compute_dead_end_blocks(ctx, blocks, &block_set, entry_bb);
    if dead_end_set.is_empty() {
        Some((blocks.to_vec(), Vec::new()))
    } else {
        let dead_ends: Vec<usize> = dead_end_set.iter().copied().collect();
        let path: Vec<usize> =
            blocks.iter().filter(|bb| !dead_end_set.contains(bb)).copied().collect();
        if path.len() <= 1 {
            return None; // Degenerate: no real path after dead-end removal.
        }
        Some((path, dead_ends))
    }
}

/// Check if a fragment has a composable in-fragment path (extended check).
///
/// More permissive than `is_composable_linear_chain`: allows SwitchInt, Assert,
/// and non-Box Drop terminators at intermediate blocks, as long as each has
/// exactly ONE non-dead-end successor within the fragment. Out-of-fragment
/// targets from intermediate terminators are handled as separate exit rules
/// during composition.
///
/// A "dead-end" block is one whose all successors are outside the fragment
/// (cut points, function exits). These represent exit branches (e.g., the
/// None path of a SwitchInt on an Option discriminant in a for-loop body)
/// and are excluded from the composable path, with their exits handled by
/// `emit_intermediate_switchint_exits`.
///
/// The linear chain check iterates over `path_blocks` (blocks excluding
/// dead-ends) rather than the full topo-sorted block list. Dead-end blocks
/// can appear between path blocks in topological order (Kahn's algorithm
/// assigns them positions based on in-degree, not path structure), which
/// would break the `path_blocks[i+1]` linear chain invariant if checked
/// against the full list.
///
/// Part of #112: extend large-step composition to handle loop bodies with
/// condition checks (SwitchInt) and bounds checks (Assert).
pub(super) fn is_composable_fragment(
    ctx: &ChcCtx<'_, '_>,
    blocks: &[usize],
    entry_bb: usize,
) -> bool {
    if blocks.len() <= 1 {
        return true;
    }

    let block_set: HashSet<usize> = blocks.iter().copied().collect();
    let dead_end_set = compute_dead_end_blocks(ctx, blocks, &block_set, entry_bb);

    // Build path blocks: topo-ordered blocks excluding dead-ends.
    // Dead-end blocks may interleave with path blocks in topo order (e.g.,
    // bb6 appearing between bb3 and bb4), which would break the blocks[i+1]
    // check. Filtering them first ensures the linear chain check only
    // considers blocks on the composable path.
    let path_blocks: Vec<usize> =
        blocks.iter().filter(|bb| !dead_end_set.contains(bb)).copied().collect();

    if path_blocks.len() <= 1 {
        return false; // Degenerate: no composable path after dead-end removal.
    }

    for i in 0..path_blocks.len() - 1 {
        let bb_idx = path_blocks[i];
        let bb_data = &ctx.body.blocks[bb_idx];

        // Count unique successors within the fragment, excluding:
        // - back-edge to fragment entry
        // - dead-end blocks (exit branches handled by emit_intermediate_switchint_exits)
        let in_frag_succs: HashSet<usize> = bb_data
            .terminator
            .successors()
            .into_iter()
            .filter(|&s| block_set.contains(&s) && s != entry_bb && !dead_end_set.contains(&s))
            .collect();

        // Must have exactly one in-fragment successor to maintain a linear path.
        if in_frag_succs.len() != 1 {
            return false;
        }
        let in_frag_target = *in_frag_succs.iter().next().expect("invariant: len == 1");
        if in_frag_target != path_blocks[i + 1] {
            return false;
        }

        // Reject terminators we cannot compose through.
        match &bb_data.terminator.kind {
            TerminatorKind::Goto { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Assert { .. } => {}
            TerminatorKind::Drop { place, .. } => {
                // Box drops require full dealloc transition handling.
                use crate::codegen_ay::shared::IntoOption;
                let drop_ty = place.ty(ctx.body.locals()).into_option();
                if drop_ty.is_some_and(ChcCtx::is_box_ty) {
                    return false;
                }
            }
            TerminatorKind::Call { func, target, .. } => {
                // Part of #112: compose through inlineable kani stubs
                // (any, assume, assert, noop) to reduce predicate count.
                // Diverging calls (target=None) cannot be composed through.
                if target.is_none() || classify_inlineable_call(ctx, func).is_none() {
                    return false;
                }
            }
            // Other terminators have side effects we can't compose through.
            _ => return false,
        }
    }

    true
}
