// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Natural loop detection, terminator rewriting, and loop body unrolling.

use std::collections::HashMap;

use super::LoopUnrollError;
use super::cfg::Cfg;
use rustc_public::mir::{
    BasicBlock, Body, SwitchTargets, Terminator, TerminatorKind, UnwindAction,
};

/// Context for target remapping during loop unrolling (Part of #3517).
///
/// Bundles the shared parameters that `remap_target` and `rewrite_terminator`
/// pass together on every call, reducing both from 9 → 4 parameters.
pub(super) struct UnrollContext<'a> {
    pub(super) lp: &'a NaturalLoop,
    pub(super) maps: &'a [BlockMap],
    pub(super) unwind_depth: usize,
    pub(super) fail_bb: usize,
    pub(super) silent_fail_bb: usize,
    pub(super) unwinding_assertions: bool,
}

#[cfg(test)]
impl<'a> UnrollContext<'a> {
    /// Standard test defaults: depth=1, fail_bb=99, silent_fail_bb=100, unwinding=true.
    pub(super) fn test_default(lp: &'a NaturalLoop, maps: &'a [BlockMap]) -> Self {
        Self {
            lp,
            maps,
            unwind_depth: 1,
            fail_bb: 99,
            silent_fail_bb: 100,
            unwinding_assertions: true,
        }
    }
}

/// Sparse block remapping for loop unrolling (Part of #2130).
///
/// Stores only remapped block indices; unmapped blocks return identity.
/// For a loop with L blocks in a function with N blocks, each iteration
/// stores L entries instead of N, reducing memory from O(depth × N) to
/// O(depth × L).
#[derive(Debug)]
pub(super) struct BlockMap {
    remaps: HashMap<usize, usize>,
}

impl BlockMap {
    /// Create an identity map (no remappings).
    pub(super) fn identity() -> Self {
        Self { remaps: HashMap::new() }
    }

    /// Create a map with specific block remappings.
    pub(super) fn with_remaps(remaps: HashMap<usize, usize>) -> Self {
        Self { remaps }
    }

    /// Look up a block index, returning identity if not remapped.
    pub(super) fn get(&self, block: usize) -> usize {
        self.remaps.get(&block).copied().unwrap_or(block)
    }
}

#[derive(Debug)]
pub(super) struct NaturalLoop {
    pub(super) header: usize,
    pub(super) latches: Vec<usize>,
    pub(super) in_loop: Vec<bool>,
    pub(super) blocks: Vec<usize>,
}

pub(super) fn natural_loop(cfg: &Cfg, header: usize, latches: &[usize]) -> NaturalLoop {
    let n = cfg.successors.len();
    let mut in_loop = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();

    in_loop[header] = true;
    for &latch in latches {
        in_loop[latch] = true;
        stack.push(latch);
    }

    while let Some(node) = stack.pop() {
        for &pred in &cfg.predecessors[node] {
            if !cfg.reachable[pred] || in_loop[pred] {
                continue;
            }
            in_loop[pred] = true;
            if pred != header {
                stack.push(pred);
            }
        }
    }

    let blocks: Vec<usize> = (0..n).filter(|&bb| in_loop[bb]).collect();
    NaturalLoop { header, latches: latches.to_vec(), in_loop, blocks }
}

pub(super) fn check_single_entry(cfg: &Cfg, lp: &NaturalLoop) -> Result<(), LoopUnrollError> {
    for &bb in &lp.blocks {
        if bb == lp.header {
            continue;
        }
        for &pred in &cfg.predecessors[bb] {
            if !cfg.reachable[pred] {
                continue;
            }
            if !lp.in_loop[pred] {
                return Err(LoopUnrollError::MultipleEntries {
                    header: lp.header,
                    entry: bb,
                    pred,
                });
            }
        }
    }
    Ok(())
}

pub(super) fn remap_unwind_action(action: &UnwindAction, map: &BlockMap) -> UnwindAction {
    match action {
        UnwindAction::Continue => UnwindAction::Continue,
        UnwindAction::Unreachable => UnwindAction::Unreachable,
        UnwindAction::Terminate => UnwindAction::Terminate,
        UnwindAction::Cleanup(bb) => UnwindAction::Cleanup(map.get(*bb)),
    }
}

pub(super) fn remap_target(
    target: usize,
    iter: usize,
    src: usize,
    ucx: &UnrollContext<'_>,
) -> usize {
    if !ucx.lp.in_loop[target] {
        return target;
    }

    // Final iteration: do not allow starting a new iteration.
    // Part of #4175: when unwinding_assertions is false (--no-default-checks),
    // redirect to silent_fail_bb (Return) instead of the old truncate_target.
    // truncate_target sent control to the loop's exit block, allowing paths
    // where the loop didn't terminate to reach user assertions with wrong values.
    // silent_fail_bb silently terminates the path without an error rule — matching
    // CBMC's --no-unwinding-assertions where un-terminated paths are infeasible.
    if iter == ucx.unwind_depth && src == ucx.lp.header {
        return if ucx.unwinding_assertions { ucx.fail_bb } else { ucx.silent_fail_bb };
    }

    // Back-edge to loop header becomes edge to next iteration header.
    if target == ucx.lp.header {
        if iter < ucx.unwind_depth {
            return ucx.maps[iter + 1].get(ucx.lp.header);
        }
        return if ucx.unwinding_assertions { ucx.fail_bb } else { ucx.silent_fail_bb };
    }

    // Internal edge within the loop stays within this iteration's copy.
    ucx.maps[iter].get(target)
}

fn rewrite_terminator(
    term: &Terminator,
    iter: usize,
    src: usize,
    ucx: &UnrollContext<'_>,
) -> Terminator {
    let span = term.span;
    let kind = match &term.kind {
        TerminatorKind::Goto { target } => {
            TerminatorKind::Goto { target: remap_target(*target, iter, src, ucx) }
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            let new_branches: Vec<_> = targets
                .branches()
                .map(|(val, target)| (val, remap_target(target, iter, src, ucx)))
                .collect();
            let new_otherwise = remap_target(targets.otherwise(), iter, src, ucx);
            TerminatorKind::SwitchInt {
                discr: discr.clone(),
                targets: SwitchTargets::new(new_branches, new_otherwise),
            }
        }
        TerminatorKind::Drop { place, target, unwind } => TerminatorKind::Drop {
            place: place.clone(),
            target: remap_target(*target, iter, src, ucx),
            unwind: remap_unwind_action(unwind, &ucx.maps[iter]),
        },
        TerminatorKind::Call { func, args, destination, target, unwind } => TerminatorKind::Call {
            func: func.clone(),
            args: args.clone(),
            destination: destination.clone(),
            target: target.map(|t| remap_target(t, iter, src, ucx)),
            unwind: remap_unwind_action(unwind, &ucx.maps[iter]),
        },
        TerminatorKind::Assert { cond, expected, msg, target, unwind } => TerminatorKind::Assert {
            cond: cond.clone(),
            expected: *expected,
            msg: msg.clone(),
            target: remap_target(*target, iter, src, ucx),
            unwind: remap_unwind_action(unwind, &ucx.maps[iter]),
        },
        TerminatorKind::Return => TerminatorKind::Return,
        TerminatorKind::Unreachable => TerminatorKind::Unreachable,
        TerminatorKind::Resume => TerminatorKind::Resume,
        TerminatorKind::Abort => TerminatorKind::Abort,
        TerminatorKind::InlineAsm { .. } => term.kind.clone(),
    };
    Terminator { kind, span }
}

pub(super) fn unroll_natural_loop(
    body: &mut Body,
    _cfg: &Cfg,
    lp: &NaturalLoop,
    unwind_depth: usize,
    unwinding_assertions: bool,
) {
    // Template loop blocks (current versions).
    let templates: Vec<BasicBlock> = lp.blocks.iter().map(|&bb| body.blocks[bb].clone()).collect();

    // Sparse block maps: only store remapped loop blocks per iteration (Part of #2130).
    // Previously each iteration allocated a full identity Vec of orig_block_count entries;
    // now each stores only L entries (loop block count) via HashMap.
    let mut maps: Vec<BlockMap> = Vec::with_capacity(unwind_depth + 1);
    maps.push(BlockMap::identity());

    // Create copies 1..=unwind_depth.
    for _iter in 1..=unwind_depth {
        let mut remaps = HashMap::with_capacity(lp.blocks.len());
        for (idx, &bb) in lp.blocks.iter().enumerate() {
            let new_bb = body.blocks.len();
            body.blocks.push(templates[idx].clone());
            remaps.insert(bb, new_bb);
        }
        maps.push(BlockMap::with_remaps(remaps));
    }

    let span = body.blocks[lp.header].terminator.span;

    // Add a shared failure block for this loop (Unreachable → error rule in CHC).
    // Used when unwinding_assertions is true: signals insufficient unwind.
    let fail_bb = body.blocks.len();
    body.blocks.push(BasicBlock {
        statements: Vec::new(),
        terminator: Terminator { kind: TerminatorKind::Unreachable, span },
    });

    // Part of #4175: Add a silent dead-end block (Return → no error rule in CHC).
    // Used when unwinding_assertions is false (--no-default-checks): paths that
    // exceed the unwind budget terminate silently without reaching user assertions.
    // This matches CBMC's --no-unwinding-assertions behavior where un-terminated
    // loop paths are simply infeasible (not explored).
    let silent_fail_bb = body.blocks.len();
    body.blocks.push(BasicBlock {
        statements: Vec::new(),
        terminator: Terminator { kind: TerminatorKind::Return, span },
    });

    let ucx = UnrollContext {
        lp,
        maps: &maps,
        unwind_depth,
        fail_bb,
        silent_fail_bb,
        unwinding_assertions,
    };

    // Rewrite terminators in all copies.
    // `iter` is a semantic unroll-iteration counter passed to remap_target, not just an index.
    #[allow(clippy::needless_range_loop)]
    for iter in 0..=unwind_depth {
        for (idx, &orig_bb) in lp.blocks.iter().enumerate() {
            let bb = maps[iter].get(orig_bb);
            let template_term = &templates[idx].terminator;
            body.blocks[bb].terminator = rewrite_terminator(template_term, iter, orig_bb, &ucx);
        }
    }
}

/// Memory bound heuristic: limit total block expansion per unroll pass.
/// Each unroll creates (unwind_depth * loop_blocks) new blocks.
/// 10,000 blocks is a reasonable upper bound before memory pressure becomes critical.
/// For nested loops (k^n explosion), this ensures each outer unroll stays bounded.
pub(super) const MAX_EXPANDED_BLOCKS: usize = 10_000;

/// Compute the effective unwind depth for a loop, applying memory bounds heuristic.
///
/// Returns `(effective_depth, was_reduced)` where `was_reduced` indicates if the
/// depth was capped due to memory bounds.
///
/// The heuristic prevents quadratic/exponential memory growth from loop unrolling:
/// - For a loop with n blocks unrolled to depth k, we create k*n new blocks
/// - If k*n > MAX_EXPANDED_BLOCKS, we reduce k to MAX_EXPANDED_BLOCKS/n
/// - At minimum, we always unroll at least once to make progress
#[inline]
pub(super) fn compute_effective_unwind_depth(
    requested_depth: usize,
    loop_blocks: usize,
) -> (usize, bool) {
    let projected_expansion = requested_depth.saturating_mul(loop_blocks);
    if projected_expansion > MAX_EXPANDED_BLOCKS {
        let reduced = MAX_EXPANDED_BLOCKS / loop_blocks.max(1);
        (reduced.max(1), true)
    } else {
        (requested_depth, false)
    }
}
