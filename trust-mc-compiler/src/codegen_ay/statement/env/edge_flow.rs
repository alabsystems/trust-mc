// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Outgoing edge recording and path condition management.
//!
//! Part of #2408: extracted from env.rs.

use super::{Expr, IncomingEdge, StatementCodegen};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Record an outgoing edge from current block to target block.
    ///
    /// Captures the current environment and path condition as an incoming edge
    /// for the target block, enabling phi merging at block entry.
    ///
    /// REQUIRES: `target_bb` is a valid block index in `self.body`
    /// ENSURES: Adds edge to `incoming_edges[target_bb]` with current env snapshot
    /// ENSURES: Updates target block's path condition with `edge_cond`
    pub(in crate::codegen_ay) fn record_outgoing_edge(
        &mut self,
        target_bb: usize,
        edge_cond: Option<Expr>,
    ) {
        // Match on references to avoid eagerly cloning current_path_condition;
        // clone only in the arms that need owned values.
        let edge_predicate = match (&self.current_path_condition, &edge_cond) {
            (None, cond) => (*cond).clone(),
            (pc, None) => (*pc).clone(),
            (Some(path), Some(branch)) => Some(path.clone().and(branch.clone())),
        };

        // SwitchInt→variant bridge (#3017): the facts live on this edge are the ones
        // live at the current point plus any fact this branch establishes (staged by
        // the terminator in `pending_edge_variant_facts`). INTERSECTION at the target
        // block entry makes them sound across merges.
        let mut variant_facts = self.current_variant_facts.clone();
        if let Some(extra) = self.pending_edge_variant_facts.remove(&target_bb) {
            variant_facts.extend(extra);
        }

        self.incoming_edges.entry(target_bb).or_default().push(IncomingEdge {
            edge_predicate,
            env: self.current_env.clone(),
            variant_facts,
        });

        self.update_block_path_condition(target_bb, edge_cond);
    }

    /// Set the path condition for processing a specific block.
    ///
    /// Retrieves the pre-computed path condition for `bb_idx` from `block_path_conditions`.
    /// This is called at block entry before processing statements.
    ///
    /// REQUIRES: `bb_idx` is a valid block index
    /// ENSURES: `current_path_condition` matches `block_path_conditions[bb_idx]`
    pub(in crate::codegen_ay::statement) fn set_block_path_condition(&mut self, bb_idx: usize) {
        self.current_path_condition =
            self.block_path_conditions.get(&bb_idx).and_then(std::clone::Clone::clone);
    }

    /// Update the path condition for a target block based on a branch condition.
    ///
    /// Combines current path condition with branch condition to form the target's
    /// path condition. If the target already has a condition (reachable via multiple
    /// paths), ORs them together.
    ///
    /// REQUIRES: `bb_idx` is a valid block index
    /// ENSURES: `block_path_conditions[bb_idx]` reflects reachability from all edges
    pub(in crate::codegen_ay::statement) fn update_block_path_condition(
        &mut self,
        bb_idx: usize,
        branch_cond: Option<Expr>,
    ) {
        let new_cond = match (&self.current_path_condition, branch_cond) {
            (None, cond) => cond,
            (Some(path), None) => Some(path.clone()),
            (Some(path), Some(branch)) => Some(path.clone().and(branch)),
        };
        // If block already has a condition, we OR them (multiple paths can reach the block).
        // Use remove() to take ownership, avoiding a clone on the existing Expr.
        if let Some(existing) = self.block_path_conditions.remove(&bb_idx) {
            let combined = match (existing, new_cond) {
                (None, _) => None, // Already unconditionally reachable
                (_, None) => None, // Now unconditionally reachable
                (Some(e), Some(n)) => Some(e.or(n)),
            };
            self.block_path_conditions.insert(bb_idx, combined);
        } else {
            self.block_path_conditions.insert(bb_idx, new_cond);
        }
    }
}
