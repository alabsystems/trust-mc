// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Panic-path filtering for CHC state variable pre-declaration and pruning.
//!
//! Computes return-reachable blocks (blocks that can reach a Return terminator)
//! and identifies MIR locals only referenced in error-only blocks. Used by:
//! - `collect_deref_type_arrays` and `collect_local_type_arrays` to exclude
//!   panic-formatting infrastructure types from CHC relation signatures
//! - `prune_vc_unused_type_arrays` to prune dead scalar state variables
//!
//! Part of #3436: dead state elimination for panic-path state variables.

use std::collections::HashSet;

use rustc_public::mir::{Body, Operand, Rvalue, StatementKind, TerminatorKind, UnwindAction};

fn all_successors(kind: &TerminatorKind) -> Vec<usize> {
    match kind {
        TerminatorKind::Goto { target } => vec![*target],
        TerminatorKind::SwitchInt { targets, .. } => {
            let mut succs: Vec<usize> =
                targets.branches().map(|(_case_val, target)| target).collect();
            succs.push(targets.otherwise());
            succs
        }
        TerminatorKind::Call { target, unwind, .. } => {
            let mut succs: Vec<usize> = target.iter().copied().collect();
            if let UnwindAction::Cleanup(cleanup_bb) = unwind {
                succs.push(*cleanup_bb);
            }
            succs
        }
        TerminatorKind::Drop { target, unwind, .. } => {
            let mut succs = vec![*target];
            if let UnwindAction::Cleanup(cleanup_bb) = unwind {
                succs.push(*cleanup_bb);
            }
            succs
        }
        TerminatorKind::Assert { target, unwind, .. } => {
            let mut succs = vec![*target];
            if let UnwindAction::Cleanup(cleanup_bb) = unwind {
                succs.push(*cleanup_bb);
            }
            succs
        }
        TerminatorKind::InlineAsm { destination, .. } => destination.iter().copied().collect(),
        TerminatorKind::Return
        | TerminatorKind::Resume
        | TerminatorKind::Abort
        | TerminatorKind::Unreachable => Vec::new(),
    }
}

fn predecessor_map(body: &Body) -> Vec<Vec<usize>> {
    let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); body.blocks.len()];
    for (bb_idx, bb_data) in body.blocks.iter().enumerate() {
        for succ in all_successors(&bb_data.terminator.kind) {
            predecessors[succ].push(bb_idx);
        }
    }
    predecessors
}

fn reverse_reachable_from_seeds(
    predecessors: &[Vec<usize>],
    seeds: impl IntoIterator<Item = usize>,
) -> Vec<bool> {
    let mut reachable = vec![false; predecessors.len()];
    let mut work = Vec::new();
    for bb in seeds {
        if !reachable[bb] {
            reachable[bb] = true;
            work.push(bb);
        }
    }
    while let Some(bb) = work.pop() {
        for &pred in &predecessors[bb] {
            if !reachable[pred] {
                reachable[pred] = true;
                work.push(pred);
            }
        }
    }
    reachable
}

/// Compute which basic blocks can reach a Return terminator via ANY edge.
///
/// Uses reverse BFS: seeds with Return blocks, then walks predecessors through
/// ALL edges (normal + unwind/cleanup). Blocks NOT in the returned set are
/// "error-only" — they can only reach error/panic/unreachable terminators.
///
/// A block can be forward-reachable from bb0 via normal edges but still lead
/// only to a dead end (e.g., assert failure → panic formatting → Unreachable).
/// Reverse from Return correctly identifies such blocks as error-only.
///
/// Part of #3436: used by error-path-aware state variable pruning.
pub(in crate::codegen_ay::chc) fn compute_return_reachable_blocks(body: &Body) -> Vec<bool> {
    let predecessors = predecessor_map(body);
    reverse_reachable_from_seeds(
        &predecessors,
        body.blocks.iter().enumerate().filter_map(|(bb_idx, bb_data)| {
            matches!(bb_data.terminator.kind, TerminatorKind::Return).then_some(bb_idx)
        }),
    )
}

/// Compute blocks on panic-unwind cleanup chains.
///
/// Seeds from direct `Cleanup(bb)` targets on Call/Drop/Assert terminators, then
/// walks all CFG successors from those cleanup entries. This retains semantically
/// relevant cleanup code (Drop bodies, Resume/Abort tails) without pulling in
/// unrelated panic-formatting blocks that are not on cleanup paths.
fn compute_cleanup_chain_blocks_filtered(
    body: &Body,
    mut retain_seed: impl FnMut(usize, &TerminatorKind) -> bool,
) -> Vec<bool> {
    let n = body.blocks.len();
    let mut cleanup_chain = vec![false; n];
    let mut work = Vec::new();

    for (bb_idx, bb_data) in body.blocks.iter().enumerate() {
        let cleanup_target = match &bb_data.terminator.kind {
            TerminatorKind::Call { unwind: UnwindAction::Cleanup(cleanup_bb), .. }
            | TerminatorKind::Drop { unwind: UnwindAction::Cleanup(cleanup_bb), .. }
            | TerminatorKind::Assert { unwind: UnwindAction::Cleanup(cleanup_bb), .. } => {
                Some(*cleanup_bb)
            }
            _ => None,
        };
        if let Some(cleanup_bb) = cleanup_target
            && retain_seed(bb_idx, &bb_data.terminator.kind)
            && !cleanup_chain[cleanup_bb]
        {
            cleanup_chain[cleanup_bb] = true;
            work.push(cleanup_bb);
        }
    }

    while let Some(bb) = work.pop() {
        for succ in all_successors(&body.blocks[bb].terminator.kind) {
            if !cleanup_chain[succ] {
                cleanup_chain[succ] = true;
                work.push(succ);
            }
        }
    }

    cleanup_chain
}

/// Compute all blocks that can reach a panic-unwind cleanup chain.
///
/// This includes the cleanup chain itself plus predecessor blocks that branch
/// into it (for example, diverging panic-call blocks whose only continuation is
/// `Cleanup(bb)`).
pub(in crate::codegen_ay::chc) fn compute_cleanup_relevant_blocks_with_filter(
    body: &Body,
    retain_seed: impl FnMut(usize, &TerminatorKind) -> bool,
) -> Vec<bool> {
    let cleanup_chain = compute_cleanup_chain_blocks_filtered(body, retain_seed);
    let predecessors = predecessor_map(body);
    reverse_reachable_from_seeds(
        &predecessors,
        cleanup_chain.iter().enumerate().filter_map(|(bb_idx, keep)| keep.then_some(bb_idx)),
    )
}

pub(in crate::codegen_ay::chc) fn compute_cleanup_relevant_blocks(body: &Body) -> Vec<bool> {
    compute_cleanup_relevant_blocks_with_filter(body, |_bb_idx, _term| true)
}

/// Compute basic blocks whose semantics must be preserved in the VC.
///
/// This is the union of:
/// - blocks that can reach `Return`
/// - blocks on panic-unwind cleanup chains and their predecessors
///
/// Part of #3886: cleanup-only blocks remain semantically relevant even when
/// they cannot reach `Return`, because their `Drop`/assert effects contribute to
/// the proof outcome.
pub(in crate::codegen_ay::chc) fn compute_semantically_relevant_blocks(body: &Body) -> Vec<bool> {
    let return_reachable = compute_return_reachable_blocks(body);
    let cleanup_relevant = compute_cleanup_relevant_blocks(body);
    return_reachable
        .into_iter()
        .zip(cleanup_relevant)
        .map(|(ret, cleanup)| ret || cleanup)
        .collect()
}

fn compute_locals_in_blocks(body: &Body, kept_blocks: &[bool]) -> HashSet<usize> {
    let mut used = HashSet::new();

    // Function return value and arguments are always relevant.
    let arg_count = body.arg_locals().len();
    for i in 0..=arg_count {
        used.insert(i);
    }

    for (bb_idx, bb_data) in body.blocks.iter().enumerate() {
        if !kept_blocks[bb_idx] {
            continue;
        }

        for stmt in &bb_data.statements {
            if let StatementKind::Assign(lhs, rhs) = &stmt.kind {
                used.insert(lhs.local);
                collect_locals_from_rvalue(rhs, &mut used);
            }
        }

        match &bb_data.terminator.kind {
            TerminatorKind::Call { func, args, destination, .. } => {
                used.insert(destination.local);
                collect_locals_from_operand(func, &mut used);
                for arg in args {
                    collect_locals_from_operand(arg, &mut used);
                }
            }
            TerminatorKind::SwitchInt { discr, .. } => {
                collect_locals_from_operand(discr, &mut used);
            }
            TerminatorKind::Drop { place, .. } => {
                used.insert(place.local);
            }
            TerminatorKind::Assert { cond, .. } => {
                collect_locals_from_operand(cond, &mut used);
            }
            TerminatorKind::Return => {
                used.insert(0);
            }
            _ => {}
        }
    }

    used
}

/// Compute the set of MIR local indices that appear in normal-reachable blocks.
///
/// A local is "used" if it appears as a Place local in any statement or
/// terminator operand within a normal-reachable block. Function arguments
/// (locals 0..=arg_count) are always included.
///
/// Part of #3436: locals only referenced in cleanup blocks should not
/// contribute type arrays to CHC relation signatures.
pub(in crate::codegen_ay::chc) fn compute_locals_in_normal_blocks(
    body: &Body,
    normal_reachable: &[bool],
) -> HashSet<usize> {
    compute_locals_in_blocks(body, normal_reachable)
}

/// Compute the set of MIR local indices that appear in semantically relevant blocks.
///
/// Part of #3886: locals used only on panic-unwind cleanup paths must remain
/// visible to later declaration/pruning passes even though those blocks do not
/// reach `Return`.
pub(in crate::codegen_ay::chc) fn compute_locals_in_relevant_blocks(body: &Body) -> HashSet<usize> {
    let relevant_blocks = compute_semantically_relevant_blocks(body);
    compute_locals_in_blocks(body, &relevant_blocks)
}

fn collect_locals_from_operand(op: &Operand, used: &mut HashSet<usize>) {
    if let Operand::Copy(place) | Operand::Move(place) = op {
        used.insert(place.local);
    }
}

fn collect_locals_from_rvalue(rvalue: &Rvalue, used: &mut HashSet<usize>) {
    match rvalue {
        Rvalue::Use(op)
        | Rvalue::Repeat(op, _)
        | Rvalue::Cast(_, op, _)
        | Rvalue::UnaryOp(_, op)
        | Rvalue::ShallowInitBox(op, _) => {
            collect_locals_from_operand(op, used);
        }
        Rvalue::Ref(_, _, place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => {
            used.insert(place.local);
        }
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            collect_locals_from_operand(lhs, used);
            collect_locals_from_operand(rhs, used);
        }
        Rvalue::Aggregate(_, ops) => {
            for op in ops {
                collect_locals_from_operand(op, used);
            }
        }
        Rvalue::NullaryOp(_) | Rvalue::ThreadLocalRef(_) => {}
    }
}
