// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-block live state variable index computation.
//!
//! Extracted from codegen_decl.rs per #4119. This module computes which state
//! variables are live at each basic block's entry, enabling per-block projected
//! relation signatures that exclude dead Datatype sorts.
//!
//! Part of #2214: eliminates Datatype sort pollution in loop headers.

use std::collections::{HashMap, HashSet, VecDeque};

use tracing::{debug, trace};

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Phase 1: Build reverse map from state variable index to MIR local.
    ///
    /// Includes flattened field slots, auxiliary pointee state vars, static mut
    /// state vars, and collection length/capacity state vars so they survive
    /// non-local pruning.
    pub(in crate::codegen_ay::chc) fn build_state_idx_to_local_map(&self) -> HashMap<usize, usize> {
        // Build reverse map: state_var_idx -> MIR local (if any).
        // Only MIR-local-backed state vars have entries in local_to_state_idx.
        let mut state_idx_to_local: HashMap<usize, usize> = HashMap::new();
        for (&local_idx, &vec_idx) in &self.state_var_mgr.local_to_state_idx {
            state_idx_to_local.insert(vec_idx, local_idx);
            // For flattened locals, mark all field slots too.
            if self.flatten.flattened_tuple_locals.contains(&local_idx) {
                let n = self.flattened_field_count(local_idx);
                for i in 1..n {
                    state_idx_to_local.insert(vec_idx + i, local_idx);
                }
            }
        }

        // Part of #2978: Associate auxiliary pointee state vars with their
        // argument locals so they are treated as "local-backed" and survive
        // the non-local pruning.
        for (&arg_local, &pointee_vec_idx) in &self.ref_resolution.ref_arg_pointee_idx {
            state_idx_to_local.insert(pointee_vec_idx, arg_local);
        }

        // Part of #2978: Protect static mut state vars from non-local pruning.
        for (&ref_local, &state_idx) in &self.ref_resolution.static_ref_to_state_idx {
            state_idx_to_local.insert(state_idx, ref_local);
        }

        // Part of #2978: Protect collection length/capacity state vars from pruning.
        // Part of #2267: Use O(1) HashMap lookup instead of O(n) linear scan.
        for (&local_idx, len_name) in &self.collections.len_state.len_var_names {
            if let Some(idx) = self.state_var_mgr.state_var_index_by_name(len_name) {
                state_idx_to_local.insert(idx, local_idx);
            }
        }
        for (&local_idx, cap_name) in &self.collections.len_state.cap_var_names {
            if let Some(idx) = self.state_var_mgr.state_var_index_by_name(cap_name) {
                state_idx_to_local.insert(idx, local_idx);
            }
        }

        state_idx_to_local
    }

    /// Phase 2: Compute initial per-block live state variable indices.
    ///
    /// For each basic block, determines which state variables are live at entry
    /// using the forward dead-locals analysis. Heap metadata, vtable, and
    /// mutable static state vars are always live. Storage-dead-but-used locals
    /// are rescued.
    pub(in crate::codegen_ay::chc) fn compute_forward_per_block_liveness(
        &self,
        state_idx_to_local: &HashMap<usize, usize>,
    ) -> Vec<Vec<usize>> {
        let block_count = self.body.blocks.len();
        let state_count = self.state_var_mgr.state_vars.len();

        // Part of #112: Build per-block used-local sets via backward use analysis.
        let used_locals_per_block = Self::compute_used_locals_per_block(self.body);

        // Part of #3728: Heap metadata must stay live in every block relation.
        // MEMUB-24/25/27: shadow-memory init state (when declared) is ambient
        // global state and must equally survive liveness pruning.
        let heap_metadata_indices: HashSet<usize> = ["obj_valid", "obj_size"]
            .into_iter()
            .chain(
                crate::codegen_ay::chc::shadow_mem_state::SHADOW_MEM_STATE_VARS
                    .iter()
                    .map(|(name, _, _)| *name),
            )
            .filter_map(|name| self.state_var_mgr.state_var_index_by_name(name))
            .collect();

        // Part of #3589: Collect vtable state var indices for always-live protection.
        let vtable_sv_indices: HashSet<usize> = self
            .vtable_state_vars
            .values()
            .filter_map(|(in_name, _)| self.state_var_mgr.state_var_index_by_name(in_name))
            .collect();

        // Part of #3793: Mutable static state vars must be live in ALL blocks.
        let mutable_static_indices: &HashSet<usize> =
            &self.ref_resolution.mutable_static_state_idxs;

        let mut result = Vec::with_capacity(block_count);
        for bb_idx in 0..block_count {
            let dead_set = self.liveness.dead_locals_at_entry.get(bb_idx);
            let used_set = used_locals_per_block.get(bb_idx);
            let mut live_indices = Vec::with_capacity(state_count);
            for idx in 0..state_count {
                if heap_metadata_indices.contains(&idx) {
                    live_indices.push(idx);
                    continue;
                }
                if vtable_sv_indices.contains(&idx) {
                    live_indices.push(idx);
                    continue;
                }
                if mutable_static_indices.contains(&idx) {
                    live_indices.push(idx);
                    continue;
                }
                if let Some(&mir_local) = state_idx_to_local.get(&idx)
                    && let Some(dead) = dead_set
                    && dead.contains(&mir_local)
                {
                    // Flattened locals are pruned as a unit when dead; if any field
                    // is genuinely live, enforce_atomic_flattened_liveness restores
                    // the complete field group after backward propagation.
                    if let Some(used) = used_set {
                        if used.contains(&mir_local) {
                            debug!(
                                bb = bb_idx,
                                local = mir_local,
                                state_idx = idx,
                                "rescued: storage-dead but used local kept in relation"
                            );
                            live_indices.push(idx);
                            continue;
                        }
                    }
                    debug!(
                        bb = bb_idx,
                        local = mir_local,
                        state_idx = idx,
                        "excluded: storage-dead and not used"
                    );
                    continue;
                }
                live_indices.push(idx);
            }
            result.push(live_indices);
        }

        result
    }

    /// Phase 3: Backward liveness propagation via worklist fixpoint.
    ///
    /// Part of #3474. Propagates live locals backward through the CFG: if a
    /// local is live at a successor and not killed in the current block, it
    /// becomes live in the current block. Falls back to conservative (all
    /// non-killed locals live) if the iteration bound is exceeded.
    pub(in crate::codegen_ay::chc) fn propagate_backward_liveness(
        &self,
        result: &mut Vec<Vec<usize>>,
        state_idx_to_local: &HashMap<usize, usize>,
        retained_blocks: &[bool],
    ) {
        let block_count = self.body.blocks.len();
        let state_count = self.state_var_mgr.state_vars.len();

        // Part of #3474: Backward liveness propagation.
        let mut live_locals: Vec<HashSet<usize>> = result
            .iter()
            .map(|indices| {
                indices.iter().filter_map(|idx| state_idx_to_local.get(idx).copied()).collect()
            })
            .collect();
        let killed_per_block: Vec<HashSet<usize>> = self
            .body
            .blocks
            .iter()
            .map(|block| {
                let mut killed = HashSet::new();
                for stmt in &block.statements {
                    if let rustc_public::mir::StatementKind::StorageDead(local) = &stmt.kind {
                        killed.insert(*local);
                    }
                }
                killed
            })
            .collect();
        let successors: Vec<Vec<usize>> = self
            .body
            .blocks
            .iter()
            .map(|block| Self::block_successors(&block.terminator.kind))
            .collect();
        let mut predecessors: Vec<Vec<usize>> = vec![vec![]; block_count];
        for (bb, succs) in successors.iter().enumerate() {
            for &succ in succs {
                if succ < block_count {
                    predecessors[succ].push(bb);
                }
            }
        }
        let max_preds = predecessors.iter().map(|p| p.len()).max().unwrap_or(0);
        let all_locals: HashSet<usize> =
            live_locals.iter().flat_map(|s| s.iter().copied()).collect();
        let num_locals = all_locals.len();
        let max_iters = block_count * num_locals * (max_preds + 1) + block_count;

        let mut worklist: VecDeque<usize> = (0..block_count)
            .filter(|&bb| retained_blocks.get(bb).copied().unwrap_or(true))
            .collect();
        let mut iterations = 0;
        while let Some(bb) = worklist.pop_front() {
            iterations += 1;
            if iterations > max_iters {
                tracing::warn!(
                    iterations,
                    max_iters,
                    "MIR local backward liveness exceeded bound — falling back to conservative"
                );
                for (bb_live, killed) in live_locals.iter_mut().zip(killed_per_block.iter()) {
                    for &local in &all_locals {
                        if !killed.contains(&local) {
                            bb_live.insert(local);
                        }
                    }
                }
                break;
            }
            for &succ in &successors[bb] {
                if succ >= block_count {
                    continue;
                }
                if !retained_blocks.get(succ).copied().unwrap_or(true) {
                    continue;
                }
                let succ_locals: Vec<usize> = live_locals[succ].iter().copied().collect();
                for local in succ_locals {
                    if !live_locals[bb].contains(&local) && !killed_per_block[bb].contains(&local) {
                        live_locals[bb].insert(local);
                        for &pred in &predecessors[bb] {
                            worklist.push_back(pred);
                        }
                    }
                }
            }
        }
        for (live_set, live_locs) in result.iter_mut().zip(live_locals.iter()) {
            for idx in 0..state_count {
                if let Some(&local) = state_idx_to_local.get(&idx) {
                    if live_locs.contains(&local) && !live_set.contains(&idx) {
                        live_set.push(idx);
                    }
                }
            }
            live_set.sort_unstable();
        }
        for live_set in result.iter_mut() {
            live_set.sort_unstable();
            live_set.dedup();
        }
    }

    /// Phase 4: Enforce atomic liveness for flattened locals.
    ///
    /// Part of #3474. If any field slot of a flattened local (tuple, Range,
    /// Option, Result, ADT) is live, all N field slots must be live together.
    pub(in crate::codegen_ay::chc) fn enforce_atomic_flattened_liveness(
        &self,
        result: &mut Vec<Vec<usize>>,
        state_idx_to_local: &HashMap<usize, usize>,
    ) {
        // Part of #3474: Atomic liveness for flattened locals.
        for (bb_idx, live_set) in result.iter_mut().enumerate() {
            let mut to_add: Vec<usize> = Vec::new();
            for &idx in live_set.iter() {
                if let Some(&local) = state_idx_to_local.get(&idx)
                    && self.flatten.flattened_tuple_locals.contains(&local)
                {
                    if let Some(&base) = self.state_var_mgr.local_to_state_idx.get(&local) {
                        let n = self.flattened_field_count(local);
                        for f in 0..n {
                            let field_idx = base + f;
                            if !live_set.contains(&field_idx) {
                                to_add.push(field_idx);
                            }
                        }
                    }
                }
            }
            if !to_add.is_empty() {
                debug!(
                    bb = bb_idx,
                    added = to_add.len(),
                    "atomic liveness: added missing flattened fields"
                );
                live_set.extend(to_add);
                live_set.sort_unstable();
                live_set.dedup();
            }
        }
    }

    /// Phase 5: Propagate liveness through reference targets.
    ///
    /// Part of #3741. If any pointer local referencing a pointee is live, the
    /// pointee's state variable (and its flattened fields) must also be live.
    pub(in crate::codegen_ay::chc) fn propagate_ref_target_liveness(
        &self,
        result: &mut Vec<Vec<usize>>,
        state_idx_to_local: &HashMap<usize, usize>,
    ) {
        // Part of #3741: ref_target liveness propagation.
        let mut pointee_to_ptrs: HashMap<usize, Vec<usize>> = HashMap::new();
        for (&ptr_local, ref_target) in &self.ref_resolution.ref_targets {
            if ref_target.projections.is_empty() {
                pointee_to_ptrs.entry(ref_target.local).or_default().push(ptr_local);
            }
        }
        tracing::debug!(
            ref_targets_count = self.ref_resolution.ref_targets.len(),
            pointee_count = pointee_to_ptrs.len(),
            "ref_target liveness: phase start"
        );
        for (bb_idx, live_set) in result.iter_mut().enumerate() {
            let live_locals_at_bb: HashSet<usize> =
                live_set.iter().filter_map(|idx| state_idx_to_local.get(idx).copied()).collect();
            let mut to_add: Vec<usize> = Vec::new();
            for (&pointee_local, ptr_locals) in &pointee_to_ptrs {
                let any_ptr_live = ptr_locals.iter().any(|ptr| live_locals_at_bb.contains(ptr));
                if any_ptr_live {
                    if let Some(&vec_idx) =
                        self.state_var_mgr.local_to_state_idx.get(&pointee_local)
                    {
                        if bb_idx < 6 {
                            tracing::debug!(
                                bb = bb_idx,
                                pointee_local,
                                vec_idx,
                                in_live_set = live_set.contains(&vec_idx),
                                live_set_len = live_set.len(),
                                "ref_target liveness: vec_idx check"
                            );
                        }
                        if !live_set.contains(&vec_idx) {
                            to_add.push(vec_idx);
                            if self.flatten.flattened_tuple_locals.contains(&pointee_local) {
                                let n = self.flattened_field_count(pointee_local);
                                for f in 1..n {
                                    let field_idx = vec_idx + f;
                                    if !live_set.contains(&field_idx) {
                                        to_add.push(field_idx);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if !to_add.is_empty() {
                tracing::debug!(
                    bb = bb_idx,
                    added = to_add.len(),
                    "ref_target liveness: pointer-mediated pointee locals added"
                );
                live_set.extend(to_add);
                live_set.sort_unstable();
                live_set.dedup();
            }
        }
    }

    /// Compute per-block live state variable indices from `dead_locals_at_entry`.
    ///
    /// For each basic block, determines which state variables are live at entry:
    /// - MIR-local-backed state variables are live unless the local is dead at
    ///   block entry per the forward must-analysis in `dead_locals_at_entry`.
    /// - Flattened locals (tuples, Range, Option, Result, ADTs) expand to N
    ///   consecutive state var slots; all N are removed together when the
    ///   local is dead.
    /// - Non-local state variables (heap metadata, memory arrays) are always live.
    ///
    /// Part of #2214: eliminates Datatype sort pollution in loop headers.
    pub(in crate::codegen_ay::chc) fn compute_live_state_indices(
        &mut self,
        retained_blocks: &[bool],
    ) {
        let block_count = self.body.blocks.len();
        let state_count = self.state_var_mgr.state_vars.len();
        let state_idx_to_local = self.build_state_idx_to_local_map();
        let mut result = self.compute_forward_per_block_liveness(&state_idx_to_local);
        self.propagate_backward_liveness(&mut result, &state_idx_to_local, retained_blocks);
        self.enforce_atomic_flattened_liveness(&mut result, &state_idx_to_local);
        self.propagate_ref_target_liveness(&mut result, &state_idx_to_local);

        trace!(block_count, state_count, "computed per-block live state indices");
        self.state_var_mgr.live_state_indices = result;
    }
}
