// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Post-codegen pruning of dead state variables from CHC VCs.
//!
//! Part of #3184: Dead array parameter elimination with read-only criterion.
//! Part of #3436: Error-path-aware pruning for both type arrays and scalar locals.
//!
//! The CHC encoder pre-declares state variables for every MIR local and type
//! array visible in a function. Many of these are never actually used on paths
//! that can reach the function's Return terminator — they serve only panic
//! formatting infrastructure or cleanup paths. Each such variable adds
//! parameters to relation signatures, causing PDR to struggle with
//! high-arity invariant synthesis.
//!
//! This module removes dead state variables from the already-built ChcVc by:
//! 1. Identifying state var indices for dead type arrays (never-read, write-only,
//!    or error-path-only via `read_used_type_arrays`)
//! 2. Identifying state var indices for scalar MIR locals only used in
//!    error-only blocks (blocks that cannot reach Return)
//! 3. Building per-relation keep masks from `live_state_indices`
//! 4. Rewriting relation declarations and rule relation applications
//!
//! Note: `declare-var` entries are intentionally kept for all variables
//! (including pruned ones) because fragment composition creates identity
//! constraints like `(= __mid_bb0 bare_name)` that reference bare input names.
//! Removing those declarations causes Z3 "unknown constant" errors.

use std::collections::{HashMap, HashSet, VecDeque};

use ay_bindings::{Expr, ExprFold, ExprValue, fold_expr, rebuild_with_children};
use tracing::debug;
use trust_mc_core::chc::RelationApp;
use trust_mc_core::constraints::Constraints;

use super::codegen_ctx::ChcCtx;
use super::codegen_decl_panic_filter::{
    compute_locals_in_normal_blocks, compute_return_reachable_blocks,
};

fn is_heap_metadata_var(name: &str) -> bool {
    matches!(name, "obj_valid" | "obj_size")
        || name.starts_with("obj_valid__")
        || name.starts_with("obj_size__")
}

fn expr_mentions_heap_metadata(expr: &Expr) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Var { name } if is_heap_metadata_var(name) => return true,
            _ => stack.extend(node.children()),
        }
    }
    false
}

fn is_flat_mem_var(name: &str) -> bool {
    matches!(name, "mem" | "mem__out")
}

/// A pure identity copy `(= A B)` between two Array-sorted variables of the
/// flat-mem / heap-metadata families (`mem`, `mem__out`, `obj_valid*`,
/// `obj_size*`, or their `__mid_bbN` fragment-composition intermediates).
///
/// Part of #40: fragment composition emits these as frame chains for
/// unmodified state variables. They carry no information — treating them as
/// "use" kept dead arrays in every relation signature (Array-sorted PDR
/// blockers), defeating Phase A'/A'' global pruning for any function with a
/// loop.
fn is_pure_array_identity_copy(expr: &Expr) -> bool {
    let ExprValue::Eq(lhs, rhs) = expr.value() else {
        return false;
    };
    let (ExprValue::Var { name: a }, ExprValue::Var { name: b }) = (lhs.value(), rhs.value())
    else {
        return false;
    };
    if !lhs.sort().is_array() || !rhs.sort().is_array() {
        return false;
    }
    let in_family =
        |n: &str| is_flat_mem_var(n) || is_heap_metadata_var(n) || n.contains("__mid_bb");
    in_family(a) && in_family(b)
}

/// Check whether an expression tree references the flat memory array (`mem` or `mem__out`).
fn expr_mentions_flat_mem(expr: &Expr) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Var { name } if is_flat_mem_var(name) => return true,
            _ => stack.extend(node.children()),
        }
    }
    false
}

fn expr_mentions_prunable_relation_app(expr: &Expr, keep_map: &HashMap<&str, Vec<bool>>) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ExprValue::FuncApp { name, .. } = node.value()
            && keep_map.contains_key(name.as_str())
        {
            return true;
        }
        stack.extend(node.children());
    }
    false
}

fn prune_relation_apps_in_expr(expr: &Expr, keep_map: &HashMap<&str, Vec<bool>>) -> (Expr, bool) {
    let mut folder = PruneRelationAppsInExpr { keep_map, any_pruned: false };
    let rewritten = fold_expr(&mut folder, expr);
    (rewritten, folder.any_pruned)
}

struct PruneRelationAppsInExpr<'a, 'b> {
    keep_map: &'a HashMap<&'b str, Vec<bool>>,
    any_pruned: bool,
}

impl ExprFold for PruneRelationAppsInExpr<'_, '_> {
    fn fold_post(&mut self, original: &Expr, children: Vec<Expr>) -> Expr {
        if let ExprValue::FuncApp { name, .. } = original.value()
            && let Some(keep) = self.keep_map.get(name.as_str())
        {
            let old_len = children.len();
            let new_args: Vec<_> = children
                .into_iter()
                .enumerate()
                .filter(|(idx, _)| keep.get(*idx).copied().unwrap_or(true))
                .map(|(_, arg)| arg)
                .collect();
            if new_args.len() != old_len {
                self.any_pruned = true;
                return Expr::func_app_with_sort(name.clone(), new_args, original.sort().clone());
            }
            return rebuild_with_children(original, new_args);
        }
        rebuild_with_children(original, children)
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Remove dead state variables from the built CHC VC.
    ///
    /// Called after `generate_transition_rules()` completes, before returning
    /// the VC. Prunes two categories of dead state:
    ///
    /// **Type arrays** that are:
    /// - Never referenced at all (neither stored nor loaded), OR
    /// - Write-only (stored to but never loaded via SELECT), OR
    /// - Error-path-only: read (SELECT) but only in blocks that cannot reach
    ///   the function's Return terminator (panic/formatting dead ends)
    ///
    /// **Scalar locals** (MIR local state variables) that are only used in
    /// error-only blocks — blocks that cannot reach Return. These are typically
    /// panic formatting temporaries and constitute the majority of arity bloat.
    ///
    /// Dead state variables' values are never observed on any normal execution
    /// path. The solver need not maintain invariants over them, reducing arity
    /// and improving PDR convergence.
    ///
    /// Part of #3184: dead array parameter elimination with read-only criterion.
    /// Part of #3436: error-path-aware pruning for panic formatting state.
    pub(super) fn prune_vc_unused_type_arrays(&mut self) {
        let read_used = &self.heap_state.read_used_type_arrays;
        let write_used = &self.heap_state.write_used_type_arrays;

        // --- Phase A: Dead type array identification ---
        // A type array is dead if it was never read (SELECT).
        // Type arrays have names like `_<fn>_mem_<type>` (from mem_array_name).
        // Part of #3436: Include region arrays (per-allocation heap arrays) in
        // the prunable set. Region arrays are tracked via the same
        // read_used/write_used maps as type arrays since #3436.
        let type_array_names: HashSet<&str> = self
            .heap_state
            .type_arrays
            .values()
            .map(|(name, _)| &**name)
            .chain(self.heap_state.region_arrays.values().map(|(name, _)| &**name))
            .collect();

        let mut prunable: HashSet<usize> = (0..self.state_var_mgr.state_vars.len())
            .filter(|&idx| {
                let name = &self.state_var_mgr.state_vars[idx].0;
                type_array_names.contains(&**name) && !read_used.contains_key(&**name)
            })
            .collect();

        // Part of #3436: Extend prunable set with error-path-only arrays.
        // Arrays whose ALL reads occur in blocks that cannot reach Return are
        // dead on normal paths — they only serve panic formatting infrastructure.
        let return_reachable = compute_return_reachable_blocks(self.body);
        let mut error_path_only_array_count = 0usize;
        for (arr_name, read_blocks) in read_used {
            if read_blocks.iter().all(|&bb| !return_reachable.get(bb).copied().unwrap_or(false)) {
                // All reads are in error-only blocks
                let state_idx = self.state_var_mgr.state_var_index_by_name(arr_name);
                if let Some(idx) = state_idx {
                    if !prunable.contains(&idx) {
                        prunable.insert(idx);
                        error_path_only_array_count += 1;
                    }
                }
            }
        }

        let type_array_prunable_count = prunable.len();
        let relation_to_bb: HashMap<String, usize> = self
            .block_relations
            .iter()
            .map(|(&bb_idx, rel_name)| (rel_name.to_string(), bb_idx))
            .collect();
        let metadata_rule_blocks: HashSet<usize> = self
            .vc
            .rules
            .iter()
            .filter_map(|rule| {
                let body_rel = rule.body.relation.as_ref()?;
                let body_rel_name = body_rel.name.to_string();
                rule.body
                    .constraints
                    .iter()
                    .any(expr_mentions_heap_metadata)
                    .then(|| relation_to_bb.get(body_rel_name.as_str()).copied())
                    .flatten()
            })
            .collect();

        // Scan transition rules for flat memory array references.
        // Entry rules (body.relation == None) are excluded because their
        // constraints seed initial values but don't affect invariant synthesis.
        // Part of #40: pure identity frame-chain copies (`(= mem__mid_bbN mem)`)
        // are not uses — ignoring them lets a never-accessed `mem` prune even
        // in looping functions whose fragment composition threads it through.
        let flat_mem_used_in_transitions = self.vc.rules.iter().any(|rule| {
            rule.body.relation.is_some()
                && rule
                    .body
                    .constraints
                    .iter()
                    .any(|c| !is_pure_array_identity_copy(c) && expr_mentions_flat_mem(c))
        });

        // Check if any TRANSITION rule constrains heap metadata.
        // Entry rules (body.relation == None) are excluded because their
        // metadata constraints (e.g., `obj_valid = const_array(true)`,
        // `obj_size[id] = N`) only seed initial values — if no transition
        // rule reads these arrays, the seeded values are dead state that
        // never propagates and can be pruned from relation signatures.
        // Part of #40: identity frame-chain copies are not metadata uses.
        let metadata_used_in_any_rule = self.vc.rules.iter().any(|rule| {
            rule.body.relation.is_some()
                && rule
                    .body
                    .constraints
                    .iter()
                    .any(|c| !is_pure_array_identity_copy(c) && expr_mentions_heap_metadata(c))
        });

        // --- Phase A': Dead heap metadata array identification ---
        // Part of #3221: obj_valid and obj_size are unconditionally added for
        // non-int-lift functions, but many functions never perform heap
        // operations. If metadata_accessed_blocks is empty (no block accessed
        // obj_valid/obj_size during rule generation), these arrays are dead
        // state that inflates relation arity — add them to the global prunable
        // set. This reduces arity by 4 (2 in + 2 out) for non-allocating
        // functions, helping PDR's invariant synthesis threshold.
        //
        // Relaxed guard: at Mem track level, obj_valid/obj_size are only
        // prunable if BOTH (a) no rule constrains them and (b) the flat `mem`
        // array is unused in transitions. If the entry rule seeds metadata
        // values (e.g., obj_valid[obj_id] = true), those must propagate
        // through relation parameters even if no transition rule accesses them.
        let metadata_globally_pruned = if self.heap_state.metadata_accessed_blocks.is_empty()
            && metadata_rule_blocks.is_empty()
            && !metadata_used_in_any_rule
            && (self.track_level < crate::args::ChcTrackLevel::Mem || !flat_mem_used_in_transitions)
        {
            let mut count = 0usize;
            for name in ["obj_valid", "obj_size"] {
                if let Some(idx) = self.state_var_mgr.state_var_index_by_name(name) {
                    if prunable.insert(idx) {
                        count += 1;
                    }
                }
            }
            if count > 0 {
                debug!(
                    fn_name = %self.fn_name,
                    pruned_metadata_arrays = count,
                    "CHC: globally pruning unused obj_valid/obj_size (#3221)"
                );
            }
            count
        } else {
            0
        };

        // --- Phase A'': Dead flat memory array identification ---
        // At Mem track level, the `mem` state variable (Array(BV64, BV8)) is
        // declared unconditionally. If no transition rule actually references
        // `mem` or `mem__out`, the flat memory array is dead state that blocks
        // PDR invariant synthesis (Array-sorted parameters). Prune it.
        let flat_mem_pruned = if !flat_mem_used_in_transitions
            && self.track_level >= crate::args::ChcTrackLevel::Mem
        {
            let mut count = 0usize;
            if let Some(idx) = self.state_var_mgr.state_var_index_by_name("mem") {
                if prunable.insert(idx) {
                    count += 1;
                }
            }
            if count > 0 {
                debug!(
                    fn_name = %self.fn_name,
                    "CHC: globally pruning unused flat mem array (Array-sorted PDR blocker)"
                );
            }
            count
        } else {
            0
        };

        // --- Phase B: Dead scalar local identification ---
        // Most CHC relation arity comes from MIR local scalars (Bool, BitVec),
        // not type arrays. Locals only used in error-only blocks (panic formatting,
        // assert failure paths) are dead on return-reachable paths.
        let live_locals = compute_locals_in_normal_blocks(self.body, &return_reachable);

        // Build reverse map: state_var index → MIR local (if any).
        // Mirrors the logic in compute_live_state_indices().
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
        // Associate auxiliary state vars with their parent locals.
        for (&arg_local, &pointee_vec_idx) in &self.ref_resolution.ref_arg_pointee_idx {
            state_idx_to_local.insert(pointee_vec_idx, arg_local);
        }
        for (&ref_local, &state_idx) in &self.ref_resolution.static_ref_to_state_idx {
            state_idx_to_local.insert(state_idx, ref_local);
        }
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

        let mut error_path_scalar_count = 0usize;
        for idx in 0..self.state_var_mgr.state_vars.len() {
            if prunable.contains(&idx) {
                continue; // Already pruned (type array)
            }
            if let Some(&mir_local) = state_idx_to_local.get(&idx) {
                if !live_locals.contains(&mir_local) {
                    prunable.insert(idx);
                    error_path_scalar_count += 1;
                }
            }
            // Non-local state vars (no entry in state_idx_to_local) are NOT
            // pruned — they include heap metadata, alloc pointers, etc.
        }

        // --- Phase B': Per-block non-local state variable liveness ---
        // Part of #3436: Non-local state variables (type arrays, region arrays,
        // heap metadata) that survive global pruning (Phase A) are still included
        // in EVERY block's relation. But most blocks only use a few of them.
        // This phase computes per-block liveness using read_used/write_used
        // tracking (populated during rule generation).
        //
        // For each surviving non-local state var, determine which blocks use it,
        // then backward-propagate through the CFG so intermediate blocks carry
        // the value through transitions.
        //
        // Build state_idx → state variable name for surviving (non-globally-pruned)
        // non-local state vars. Part of #3495: Use sv_name (state variable name
        // like "_main_mem_slice_i32"), NOT arr_name (type key like "slice_i32").
        // read_used_type_arrays and write_used_type_arrays are keyed by state
        // variable name (from mark_type_array_read).
        let mut state_idx_to_type_arr: HashMap<usize, &str> = HashMap::new();
        // Part of #3436: Include type arrays, region arrays, and heap metadata
        // in per-block liveness.
        for (sv_name, _sort) in
            self.heap_state.type_arrays.values().chain(self.heap_state.region_arrays.values())
        {
            if let Some(idx) = self.state_var_mgr.state_var_index_by_name(sv_name) {
                if !prunable.contains(&idx) {
                    state_idx_to_type_arr.insert(idx, sv_name);
                }
            }
        }
        // Part of #3872: heap metadata that survives global pruning stays live in
        // every block. Stack-local validity facts are seeded at entry and later
        // heap checks may need them after metadata-free blocks; per-block pruning
        // can drop those facts and later recreate a fresh metadata array, which
        // makes stack locals spuriously appear invalid.
        let mut metadata_indices: Vec<usize> = Vec::new();
        for name in ["obj_valid", "obj_size"] {
            if let Some(idx) = self.state_var_mgr.state_var_index_by_name(name) {
                if !prunable.contains(&idx) {
                    state_idx_to_type_arr.insert(idx, name);
                    metadata_indices.push(idx);
                }
            }
        }

        // Part of #4217: Reachability-based vtable SV pruning.
        // Only vtable SVs on a capture->dispatch propagation chain are kept.
        // "Leaf" vtable locals are those NOT used as a source in any propagation
        // edge — they are terminal/dispatch nodes. We backward-trace from leaves
        // through vtable_propagation_edges to find the full reachable set.
        let propagation_sources: HashSet<usize> =
            self.vtable_propagation_edges.values().copied().collect();
        let leaf_vtable_locals: Vec<usize> = self
            .vtable_state_vars
            .keys()
            .copied()
            .filter(|local| !propagation_sources.contains(local))
            .collect();
        // Backward-trace from leaves to find all reachable vtable locals.
        let mut reachable_vtable_locals: HashSet<usize> = HashSet::new();
        let mut trace_stack: Vec<usize> = leaf_vtable_locals.clone();
        while let Some(local) = trace_stack.pop() {
            if reachable_vtable_locals.insert(local) {
                if let Some(&src) = self.vtable_propagation_edges.get(&local) {
                    trace_stack.push(src);
                }
            }
        }
        // Convert reachable locals to state var indices; globally prune unreachable.
        let vtable_sv_indices: Vec<usize> = self
            .vtable_state_vars
            .iter()
            .filter(|(local, _)| reachable_vtable_locals.contains(local))
            .filter_map(|(_, (in_name, _))| self.state_var_mgr.state_var_index_by_name(in_name))
            .filter(|idx| !prunable.contains(idx))
            .collect();
        for (local, (in_name, _)) in &self.vtable_state_vars {
            if !reachable_vtable_locals.contains(local) {
                if let Some(idx) = self.state_var_mgr.state_var_index_by_name(in_name) {
                    prunable.insert(idx);
                }
            }
        }
        tracing::debug!(
            fn_name = %self.fn_name,
            total_vtable_svs = self.vtable_state_vars.len(),
            reachable = reachable_vtable_locals.len(),
            pruned = self.vtable_state_vars.len() - reachable_vtable_locals.len(),
            "vtable SV reachability pruning (#4217)"
        );

        // Compute per-block type array liveness with backward propagation.
        let block_count = self.state_var_mgr.live_state_indices.len();
        let mut per_block_prunable: Vec<HashSet<usize>> = vec![HashSet::new(); block_count];

        if !state_idx_to_type_arr.is_empty() && block_count > 0 {
            // Seed: a non-local state var is live at block B if B reads or writes it.
            let mut ta_live: Vec<HashSet<usize>> = vec![HashSet::new(); block_count];
            for (&idx, &arr_name) in &state_idx_to_type_arr {
                // Type arrays and region arrays: use read_used/write_used tracking.
                let read_blocks = read_used.get(arr_name);
                let write_blocks = write_used.get(arr_name);
                for (bb, bb_live) in ta_live.iter_mut().enumerate() {
                    let read_here = read_blocks.map_or(false, |bs| bs.contains(&bb));
                    let write_here = write_blocks.map_or(false, |bs| bs.contains(&bb));
                    if read_here || write_here {
                        bb_live.insert(idx);
                    }
                }
            }
            // Part of #3872: once metadata arrays survive global pruning, every
            // relation must carry them. Recreating `obj_valid`/`obj_size` after a
            // metadata-free block severs the entry-seeded stack-local facts and
            // produces false invalid-object counterexamples.
            for bb_live in &mut ta_live {
                for &idx in &metadata_indices {
                    bb_live.insert(idx);
                }
            }
            // Part of #3589: Vtable state vars are live in ALL blocks.
            for bb_live in &mut ta_live {
                for &idx in &vtable_sv_indices {
                    bb_live.insert(idx);
                }
            }

            // Build CFG successors/predecessors for backward propagation.
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

            // Backward propagation: if a successor needs a type array, the
            // predecessor must carry it through (so the transition rule can pass
            // the value). Fixed-point worklist iteration.
            //
            // Sound bound: each block can acquire at most D type arrays. Each
            // acquisition pushes at most max_preds predecessors. Total iterations
            // bounded by V * D * max_preds + V (initial worklist).
            let max_preds = predecessors.iter().map(|p| p.len()).max().unwrap_or(0);
            let num_ta = state_idx_to_type_arr.len();
            let max_iters = block_count * num_ta * (max_preds + 1) + block_count;

            let mut worklist: VecDeque<usize> = (0..block_count).collect();
            let mut iterations = 0;
            while let Some(bb) = worklist.pop_front() {
                iterations += 1;
                if iterations > max_iters {
                    // Sound fallback: if we somehow exceed the theoretical
                    // bound, make all type arrays live everywhere (no per-block
                    // pruning) to avoid unsound over-pruning.
                    tracing::warn!(
                        fn_name = %self.fn_name,
                        iterations,
                        max_iters,
                        "per-block type array liveness exceeded bound — falling back to conservative"
                    );
                    for bb_live in &mut ta_live {
                        for &idx in state_idx_to_type_arr.keys() {
                            bb_live.insert(idx);
                        }
                    }
                    break;
                }
                for &succ in &successors[bb] {
                    if succ >= block_count {
                        continue;
                    }
                    let succ_live: Vec<usize> = ta_live[succ].iter().copied().collect();
                    for idx in succ_live {
                        if !ta_live[bb].contains(&idx) {
                            ta_live[bb].insert(idx);
                            for &pred in &predecessors[bb] {
                                worklist.push_back(pred);
                            }
                        }
                    }
                }
            }

            // Build per-block prunable sets: type arrays NOT live at each block.
            let mut per_block_ta_pruned = 0usize;
            for (bb_prunable, bb_live) in per_block_prunable.iter_mut().zip(ta_live.iter()) {
                for &idx in state_idx_to_type_arr.keys() {
                    if !bb_live.contains(&idx) {
                        bb_prunable.insert(idx);
                        per_block_ta_pruned += 1;
                    }
                }
            }

            // Diagnostic: per-block arity reduction summary (Part of #3436)
            if per_block_ta_pruned > 0 || !state_idx_to_type_arr.is_empty() {
                let arities: Vec<usize> = (0..block_count)
                    .filter(|bb| self.block_relations.contains_key(bb))
                    .map(|bb| {
                        let live = &self.state_var_mgr.live_state_indices[bb];
                        let global_kept = live.iter().filter(|idx| !prunable.contains(idx)).count();
                        let per_block_removed = per_block_prunable[bb].len();
                        global_kept - per_block_removed.min(global_kept)
                    })
                    .collect();
                let max_arity = arities.iter().copied().max().unwrap_or(0);
                let min_arity = arities.iter().copied().min().unwrap_or(0);
                let mean_arity = if arities.is_empty() {
                    0
                } else {
                    arities.iter().sum::<usize>() / arities.len()
                };
                let metadata_per_block_pruned = metadata_indices
                    .iter()
                    .map(|&idx| per_block_prunable.iter().filter(|s| s.contains(&idx)).count())
                    .sum::<usize>();
                debug!(
                    fn_name = %self.fn_name,
                    surviving_nonlocal_vars = state_idx_to_type_arr.len(),
                    metadata_vars = metadata_indices.len(),
                    blocks = block_count,
                    per_block_ta_pruned,
                    metadata_per_block_pruned,
                    min_arity,
                    mean_arity,
                    max_arity,
                    "CHC: per-block non-local state var liveness (#3436)"
                );
            }
        }

        // Count write-only arrays for diagnostics.
        let write_only_count = (0..self.state_var_mgr.state_vars.len())
            .filter(|&idx| {
                let name = &self.state_var_mgr.state_vars[idx].0;
                type_array_names.contains(&**name)
                    && write_used.contains_key(&**name)
                    && !read_used.contains_key(&**name)
            })
            .count();

        let has_global_prunable = !prunable.is_empty();
        let has_per_block_prunable = per_block_prunable.iter().any(|s| !s.is_empty());

        if !has_global_prunable && !has_per_block_prunable {
            return;
        }

        debug!(
            fn_name = %self.fn_name,
            total_state_vars = self.state_var_mgr.state_vars.len(),
            total_type_arrays = self.heap_state.type_arrays.len(),
            total_region_arrays = self.heap_state.region_arrays.len(),
            type_array_pruned = type_array_prunable_count,
            error_path_only_arrays = error_path_only_array_count,
            write_only_arrays = write_only_count,
            metadata_globally_pruned,
            flat_mem_pruned,
            error_path_scalars = error_path_scalar_count,
            total_pruned = prunable.len(),
            "CHC: pruning dead state vars from VC (#3184 + #3436 + #3221)"
        );

        // --- Phase C: Rewrite relation declarations and rules ---
        // Build per-relation keep mask: for each relation name, which
        // positional indices in the relation's arg list should be kept.
        // A relation's args correspond to live_state_indices[bb], so we
        // filter those to exclude:
        // 1. Globally prunable indices (dead type arrays + error-path scalars)
        // 2. Per-block prunable type array indices (not live at this block)
        let empty_set: HashSet<usize> = HashSet::new();
        let mut relation_keep: HashMap<&str, Vec<bool>> = HashMap::new();
        for (&bb_idx, rel_name) in &self.block_relations {
            if bb_idx >= self.state_var_mgr.live_state_indices.len() {
                continue;
            }
            let live = &self.state_var_mgr.live_state_indices[bb_idx];
            let bb_prunable = per_block_prunable.get(bb_idx).unwrap_or(&empty_set);
            let keep: Vec<bool> = live
                .iter()
                .map(|idx| !prunable.contains(idx) && !bb_prunable.contains(idx))
                .collect();
            relation_keep.insert(rel_name, keep);
        }

        // Rewrite relation declarations: remove pruned arg_sorts.
        for rel in &mut self.vc.relations {
            if let Some(keep) = relation_keep.get(rel.name.as_str()) {
                let new_sorts: Vec<_> = rel
                    .arg_sorts
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| keep.get(*i).copied().unwrap_or(true))
                    .map(|(_, s)| s.clone())
                    .collect();
                let old_arity = rel.arg_sorts.len();
                rel.arg_sorts = new_sorts;
                debug!(
                    relation = %rel.name,
                    old_arity,
                    new_arity = rel.arg_sorts.len(),
                    "CHC: pruned relation arity (#3184 + #3436)"
                );
            }
        }

        // Rewrite rules: filter args from head and body relation applications.
        for rule in &mut self.vc.rules {
            // Rewrite head
            Self::prune_relation_app(&mut rule.head, &relation_keep);

            // Rewrite body relation (if any)
            if let Some(ref mut body_rel) = rule.body.relation {
                Self::prune_relation_app(body_rel, &relation_keep);
            }

            // Fragment composition can encode the predecessor relation app as
            // a body constraint. Keep these embedded apps in lockstep with the
            // pruned declarations so the CHC remains well-formed.
            if rule
                .body
                .constraints
                .iter()
                .any(|expr| expr_mentions_prunable_relation_app(expr, &relation_keep))
            {
                let mut any_pruned = false;
                let rewritten_constraints: Vec<_> = rule
                    .body
                    .constraints
                    .iter()
                    .map(|expr| {
                        let (rewritten, pruned) = prune_relation_apps_in_expr(expr, &relation_keep);
                        any_pruned |= pruned;
                        rewritten
                    })
                    .collect();
                if any_pruned {
                    rule.body.constraints = Constraints::Owned(rewritten_constraints);
                }
            }
        }

        // Keep ALL declare-var entries — do NOT remove them for pruned state vars.
        // Even pruned vars have their bare input names referenced in fragment
        // composition identity constraints (e.g., `__mid_bb0 = bare_name`).
        // Removing the declare-var for the bare name while keeping __mid_bb*
        // variants causes Z3 "unknown constant" errors. The performance win
        // comes from reducing relation arity (above), not from fewer declare-vars.
    }

    /// Filter a RelationApp's args based on the keep mask for its relation name.
    pub(super) fn prune_relation_app(app: &mut RelationApp, keep_map: &HashMap<&str, Vec<bool>>) {
        let Some(keep) = keep_map.get(app.name.as_str()) else {
            return; // Not a block relation (e.g., "error") — leave unchanged
        };
        let new_args: Vec<_> = app
            .args
            .iter()
            .enumerate()
            .filter(|(i, _)| keep.get(*i).copied().unwrap_or(true))
            .map(|(_, e)| e.clone())
            .collect();
        *app = RelationApp::new(app.name.as_str(), new_args);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::{expr_mentions_flat_mem, expr_mentions_heap_metadata, prune_relation_apps_in_expr};
    use ay_bindings::{Expr, Sort};

    fn metadata_bool_array(name: &str) -> Expr {
        Expr::var(name, Sort::array(Sort::bv32(), Sort::bool()))
    }

    fn metadata_bv32_array(name: &str) -> Expr {
        Expr::var(name, Sort::array(Sort::bv32(), Sort::bv32()))
    }

    #[test]
    fn test_expr_mentions_heap_metadata_finds_nested_metadata_vars() {
        let obj_id = Expr::bitvec_const(7u64, 32);
        let obj_valid = metadata_bool_array("obj_valid");
        let obj_valid_out = metadata_bool_array("obj_valid__out");
        let nested_valid =
            obj_valid_out.eq(obj_valid.store(obj_id.clone(), Expr::bool_const(false)));
        assert!(expr_mentions_heap_metadata(&nested_valid));

        let obj_size = metadata_bv32_array("obj_size");
        let nested_size = obj_size.select(obj_id).eq(Expr::bitvec_const(8u64, 32));
        assert!(expr_mentions_heap_metadata(&nested_size));
    }

    #[test]
    fn test_expr_mentions_heap_metadata_ignores_lookalike_names() {
        let obj_id = Expr::bitvec_const(3u64, 32);
        let not_metadata_valid = metadata_bool_array("obj_validity");
        let valid_check = not_metadata_valid.select(obj_id.clone()).eq(Expr::bool_const(true));
        assert!(!expr_mentions_heap_metadata(&valid_check));

        let not_metadata_size = metadata_bv32_array("obj_size_hint");
        let size_check = not_metadata_size.select(obj_id).eq(Expr::bitvec_const(0u64, 32));
        assert!(!expr_mentions_heap_metadata(&size_check));
    }

    fn flat_mem_array(name: &str) -> Expr {
        Expr::var(name, Sort::array(Sort::bitvec(64), Sort::bitvec(8)))
    }

    #[test]
    fn test_expr_mentions_flat_mem_detects_mem_var() {
        let mem = flat_mem_array("mem");
        let addr = Expr::bitvec_const(0x1000u64, 64);
        let load = mem.select(addr);
        assert!(expr_mentions_flat_mem(&load));
    }

    #[test]
    fn test_expr_mentions_flat_mem_detects_mem_out_var() {
        let mem_out = flat_mem_array("mem__out");
        let mem = flat_mem_array("mem");
        let addr = Expr::bitvec_const(0x2000u64, 64);
        let val = Expr::bitvec_const(42u64, 8);
        let store_eq = mem_out.eq(mem.store(addr, val));
        assert!(expr_mentions_flat_mem(&store_eq));
    }

    #[test]
    fn test_expr_mentions_flat_mem_ignores_non_mem_vars() {
        let other = Expr::var("memory_state", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));
        let addr = Expr::bitvec_const(0x3000u64, 64);
        let load = other.select(addr);
        assert!(!expr_mentions_flat_mem(&load));
    }

    #[test]
    fn test_expr_mentions_flat_mem_ignores_scalar_mem_name() {
        // A BV64 var named "mem" should still match (name-based detection).
        let mem_scalar = Expr::var("mem", Sort::bitvec(64));
        assert!(expr_mentions_flat_mem(&mem_scalar));
    }

    #[test]
    fn test_expr_mentions_flat_mem_returns_false_for_no_mem() {
        let x = Expr::var("x", Sort::bitvec(32));
        let y = Expr::var("y", Sort::bitvec(32));
        let sum = x.bvadd(y);
        assert!(!expr_mentions_flat_mem(&sum));
    }

    #[test]
    fn test_prune_relation_apps_in_expr_prunes_embedded_relation_args() {
        let a = Expr::var("a", Sort::bv64());
        let b = Expr::var("b", Sort::bool());
        let c = Expr::var("c", Sort::bv64());
        let embedded = Expr::func_app("bb33", vec![a.clone(), b, c.clone()]).not();

        let mut keep = HashMap::new();
        keep.insert("bb33", vec![true, false, true]);

        let (rewritten, changed) = prune_relation_apps_in_expr(&embedded, &keep);
        assert!(changed, "embedded relation app should be pruned");

        let inner = match rewritten.value() {
            ay_bindings::ExprValue::Not(inner) => inner,
            other => panic!("expected not-wrapped relation app, got {other:?}"),
        };
        match inner.value() {
            ay_bindings::ExprValue::FuncApp { name, args } => {
                assert_eq!(name, "bb33");
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], a);
                assert_eq!(args[1], c);
            }
            other => panic!("expected pruned relation app, got {other:?}"),
        }
    }
}
