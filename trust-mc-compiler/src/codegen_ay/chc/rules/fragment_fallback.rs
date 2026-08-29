// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Fallback rule generation for non-composable fragments (#112).
//!
//! When a fragment cannot be composed into a single large-step rule (internal
//! branching, non-inlineable calls), this module provides fallback strategies:
//!
//! - **Sub-fragment splitting**: splits at Call boundaries, builds composable
//!   sub-chains via linear-path walking from each Call's landing pad.
//! - **Per-block fallback**: declares all intermediate relations and generates
//!   Small-mode per-block rules.
//!
//! Extracted from `fragment_gen.rs` as part of #3199.

use std::collections::HashSet;
use std::sync::Arc;

use rustc_public::mir::TerminatorKind;
use tracing::debug;

use super::ChcCtx;
use super::codegen_rules_helpers::CodegenRulesHelpers;
use super::fragment_compose::generate_composed_rules;
use super::fragment_gen::{
    classify_inlineable_call, generate_single_block_rules, is_composable_fragment,
    is_composable_linear_chain,
};
use trust_mc_core::chc::{RelationDecl, VarDecl};

/// Predecessors of every block, counted over the blocks reachable from the
/// body entry only.
///
/// Chain composition fuses a block into its predecessor's rule and gives it NO
/// relation of its own, so an edge that enters the block from anywhere else has
/// nowhere to land: `try_emit_unreachable_error` cannot tell "absorbed into a
/// chain" from "error-only block" and routes that edge to `error()`. Fusing is
/// therefore only sound for a block whose sole way in is the chain edge, and
/// answering that question needs the real predecessor relation.
///
/// Unreachable-from-entry blocks are skipped: `FunctionWithContractPass` and
/// the CHC inliner strand whole copies of a body (see `reachable_blocks` in
/// `codegen_function.rs`), and counting those stranded copies' edges would
/// split chains that really do have a single live predecessor.
fn reachable_predecessors(ctx: &ChcCtx<'_, '_>) -> Vec<HashSet<usize>> {
    let n = ctx.body.blocks.len();
    let mut preds: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    if n == 0 {
        return preds;
    }
    let mut seen = vec![false; n];
    seen[0] = true;
    let mut worklist = vec![0usize];
    while let Some(bb) = worklist.pop() {
        for succ in ctx.body.blocks[bb].terminator.successors() {
            if succ >= n {
                continue;
            }
            preds[succ].insert(bb);
            if !seen[succ] {
                seen[succ] = true;
                worklist.push(succ);
            }
        }
    }
    preds
}

/// Fallback: try sub-fragment splitting at Call boundaries, else per-block.
///
/// For non-composable fragments (internal branching/calls), builds composable
/// sub-chains via linear-path walking from each Call's landing pad.
/// Unreachable blocks (error dead-ends) are excluded from chains — SwitchInt
/// targets to them become out-of-chain exits that emit error rules directly,
/// improving composability of loop bodies containing Option match patterns.
///
/// If no Call terminators (non-composable for other reasons), falls back to
/// declaring all intermediate relations and per-block rule generation.
///
/// Part of #3101: make large-step encoding effective for loop bodies.
pub(super) fn generate_fallback_fragment_rules(ctx: &mut ChcCtx<'_, '_>, blocks: &[usize]) {
    // Collect non-inlineable Call blocks as splitting boundaries (non-last only —
    // last block's terminator is dispatched by whoever generates its rules).
    //
    // Part of #112: Only NON-inlineable Calls create splitting boundaries.
    // Inlineable calls (kani::assume, kani::any at Var level, noop stubs) are
    // included in chains and composed through, reducing predicate count.
    let call_blocks: Vec<usize> = blocks
        .iter()
        .enumerate()
        .filter_map(|(i, &bb_idx)| {
            if i < blocks.len() - 1 {
                if let TerminatorKind::Call { func, .. } = &ctx.body.blocks[bb_idx].terminator.kind
                {
                    // Only split at non-inlineable Calls.
                    if classify_inlineable_call(ctx, func).is_none() {
                        return Some(bb_idx);
                    }
                }
            }
            None
        })
        .collect();

    if call_blocks.is_empty() {
        generate_perblock_fallback(ctx, blocks);
        return;
    }

    // Part of #3101: Identify Unreachable blocks (error dead-ends).
    // Excluding them from chains improves composability because SwitchInt
    // targets to Unreachable blocks become out-of-chain exits handled by
    // emit_intermediate_switchint_exits as direct error rules.
    let unreachable_set: HashSet<usize> = blocks
        .iter()
        .filter(|&&bb_idx| {
            matches!(ctx.body.blocks[bb_idx].terminator.kind, TerminatorKind::Unreachable)
        })
        .copied()
        .collect();

    let call_set: HashSet<usize> = call_blocks.iter().copied().collect();
    let fragment_set: HashSet<usize> = blocks.iter().copied().collect();
    let entry_bb = blocks[0];

    debug!(
        call_count = call_blocks.len(),
        unreachable_count = unreachable_set.len(),
        block_count = blocks.len(),
        "sub-fragment splitting: CFG-based chain building (#3101)"
    );

    // Build chains by linear-path following from each Call's landing pad.
    //
    // Part of #112: The previous BFS approach collected ALL reachable blocks
    // into one chain, including both branches of SwitchInt forks. This made
    // chains non-composable (SwitchInt with 2+ in-chain successors violates
    // the linear chain requirement). The fix: walk linearly, picking ONE
    // successor at forks. The in-chain successor closest to the next topo
    // position is chosen as the main path; other in-chain successors become
    // "orphaned" blocks that get their own chains or single-block treatment.
    //
    // This enables composing the main loop body path (landing_pad → SwitchInt
    // → loop body → back-edge) as a single composed rule, with exit branches
    // handled by emit_intermediate_switchint_exits during composition.
    let mut assigned: HashSet<usize> = HashSet::new();
    let mut chain_entries: Vec<Vec<usize>> = Vec::new();

    // Build a position map for topological ordering within the fragment.
    let topo_position: std::collections::HashMap<usize, usize> =
        blocks.iter().enumerate().map(|(pos, &bb)| (bb, pos)).collect();

    // Join points may not be absorbed into a chain — see [`reachable_predecessors`].
    let preds = reachable_predecessors(ctx);

    for &call_bb in &call_blocks {
        let landing_pad = match &ctx.body.blocks[call_bb].terminator.kind {
            TerminatorKind::Call { target: Some(t), .. } => *t,
            _ => continue,
        };

        if !fragment_set.contains(&landing_pad)
            || call_set.contains(&landing_pad)
            || unreachable_set.contains(&landing_pad)
            || assigned.contains(&landing_pad)
        {
            continue;
        }

        // Linear-path walk from landing pad.
        // At each block, collect eligible in-chain successors. If there's
        // exactly one, continue the chain. If there are multiple (SwitchInt
        // fork), pick the one closest to the next topo position and leave
        // others as orphaned blocks for separate treatment.
        let mut chain_set = HashSet::new();
        // Control-flow order of the walk. Composition semantics REQUIRE
        // blocks[i] to flow into blocks[i+1]; the original block-list order is
        // NOT that path when transform passes (loop contracts, inlining)
        // append blocks whose CFG position precedes lower-indexed blocks (#44).
        let mut chain_path: Vec<usize> = Vec::new();
        let mut current = landing_pad;
        loop {
            if chain_set.contains(&current)
                || assigned.contains(&current)
                || !fragment_set.contains(&current)
                || call_set.contains(&current)
                || unreachable_set.contains(&current)
            {
                break;
            }
            // Avoid crossing back to fragment entry (back-edge).
            if current != landing_pad && current == entry_bb {
                break;
            }
            chain_set.insert(current);
            chain_path.push(current);

            // Collect eligible in-chain successors.
            let eligible_succs: Vec<usize> = ctx.body.blocks[current]
                .terminator
                .successors()
                .into_iter()
                .filter(|&s| {
                    fragment_set.contains(&s)
                        && !call_set.contains(&s)
                        && !unreachable_set.contains(&s)
                        && !chain_set.contains(&s)
                        && !assigned.contains(&s)
                        && (s == landing_pad || s != entry_bb)
                        // A join point keeps its own relation: absorbing it
                        // would strand every edge that reaches it from off the
                        // chain, and those edges are then emitted as `error()`
                        // (a `slice[i] == 0` if/else re-join proved a false
                        // counterexample this way).
                        && preds
                            .get(s)
                            .is_none_or(|p| p.iter().all(|&pred| pred == current))
                })
                .collect();

            match eligible_succs.len() {
                0 => break,
                1 => current = eligible_succs[0],
                _ => {
                    // Fork: pick the successor closest to the next topo position.
                    // This follows the "main path" (typically the loop body for
                    // SwitchInt on Option discriminant) and leaves the exit path
                    // as an orphan handled by emit_intermediate_switchint_exits
                    // during composition.
                    let current_pos = topo_position.get(&current).copied().unwrap_or(usize::MAX);
                    let best = eligible_succs
                        .iter()
                        .copied()
                        .min_by_key(|&s| {
                            let pos = topo_position.get(&s).copied().unwrap_or(usize::MAX);
                            // Prefer the successor immediately after current in topo order.
                            if pos > current_pos { pos } else { usize::MAX }
                        })
                        .unwrap_or(eligible_succs[0]);
                    current = best;
                }
            }
        }

        // Use the CONTROL-FLOW walk order — composition names each segment's
        // inputs after its list predecessor, so any other order (the previous
        // code filtered by the original block-list order) links frame
        // constraints between non-adjacent blocks and leaves the real path
        // unconstrained (state havoc; spurious loop-contract ctrex, #44).
        let chain_blocks: Vec<usize> = chain_path;

        assigned.extend(&chain_set);
        if !chain_blocks.is_empty() {
            chain_entries.push(chain_blocks);
        }
    }

    // Declare relations for ALL non-Unreachable blocks that need them:
    // Call blocks, Call target blocks, chain entries, and orphaned blocks
    // (blocks not in any chain). Relations must be declared BEFORE rule
    // generation because composed chains may emit exit rules targeting
    // orphaned blocks (e.g., SwitchInt None-path targets that were not
    // included in the main chain).
    for &call_bb in &call_blocks {
        declare_block_relation_if_needed(ctx, call_bb);
    }
    // Part of #1739: Declare relations for Call target (landing pad) blocks.
    // A Call's landing pad might have been consumed as an interior block of
    // a chain built from a different Call's landing pad. Without a relation,
    // the Call block's rule emission silently drops the transition edge,
    // causing incomplete CHC encodings that fall through to BMC.
    for &call_bb in &call_blocks {
        if let TerminatorKind::Call { target: Some(t), .. } =
            &ctx.body.blocks[call_bb].terminator.kind
        {
            declare_block_relation_if_needed(ctx, *t);
        }
    }
    for chain in &chain_entries {
        if !chain.is_empty() {
            declare_block_relation_if_needed(ctx, chain[0]);
        }
    }
    for &bb_idx in blocks {
        if !assigned.contains(&bb_idx)
            && !call_set.contains(&bb_idx)
            && !unreachable_set.contains(&bb_idx)
        {
            declare_block_relation_if_needed(ctx, bb_idx);
        }
    }

    // Generate rules: Call blocks get single-block treatment.
    for &call_bb in &call_blocks {
        generate_single_block_rules(ctx, call_bb);
    }

    // Generate rules: chains get composed or per-block fallback.
    for chain in &chain_entries {
        if chain.len() == 1 {
            generate_single_block_rules(ctx, chain[0]);
        } else {
            let chain_entry = chain[0];
            if is_composable_linear_chain(ctx, chain)
                || is_composable_fragment(ctx, chain, chain_entry)
            {
                generate_composed_rules(ctx, chain_entry, chain);
            } else {
                generate_perblock_fallback(ctx, chain);
            }
        }
    }

    // Generate rules for orphaned blocks (not in any chain, not Call/Unreachable).
    // Relations were already declared above.
    for &bb_idx in blocks {
        if !assigned.contains(&bb_idx)
            && !call_set.contains(&bb_idx)
            && !unreachable_set.contains(&bb_idx)
        {
            generate_single_block_rules(ctx, bb_idx);
        }
    }
}

/// Declare a CHC relation for a block if one doesn't already exist.
///
/// Used by sub-fragment splitting to declare relations at sub-chain entry
/// points and Call blocks that aren't cut points.
pub(super) fn declare_block_relation_if_needed(ctx: &mut ChcCtx<'_, '_>, bb_idx: usize) {
    if ctx.block_relations.contains_key(&bb_idx) {
        return;
    }
    let rel_name = ctx.block_relation_name(bb_idx);
    let arg_sorts: Vec<_> = ctx.state_var_mgr.live_state_indices[bb_idx]
        .iter()
        .map(|&idx| ctx.state_var_mgr.state_vars[idx].1.clone())
        .collect();
    let relation = RelationDecl::new(&rel_name, arg_sorts);
    ctx.vc.add_relation(relation);

    // Declare VarDecls for variables in this block's live set.
    // Some may already be declared (from cut point live sets);
    // ChcVc::add_var deduplicates by name.
    for &idx in &ctx.state_var_mgr.live_state_indices[bb_idx] {
        let (name, sort) = &ctx.state_var_mgr.state_vars[idx];
        ctx.vc.add_var(VarDecl::new(name.clone(), sort.clone()));
        let (out_name, out_sort) = &ctx.state_var_mgr.output_state_vars[idx];
        ctx.vc.add_var(VarDecl::new(out_name.clone(), out_sort.clone()));
    }

    ctx.block_relations.insert(bb_idx, Arc::from(rel_name));
}

/// Full per-block fallback: declare all intermediate relations and generate
/// Small-mode per-block rules.
fn generate_perblock_fallback(ctx: &mut ChcCtx<'_, '_>, blocks: &[usize]) {
    debug!(
        block_count = blocks.len(),
        "non-composable fragment — declaring intermediate relations (fallback)"
    );

    for &bb_idx in blocks {
        declare_block_relation_if_needed(ctx, bb_idx);
    }

    for &bb_idx in blocks {
        generate_single_block_rules(ctx, bb_idx);
    }
}
