// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer runtime check suppression for CHC codegen.
//!
//! Contains:
//! - `should_skip_reg_pointer_assert`: two-phase pointer check suppression
//! - `operand_depends_on_ref_target` / `place_depends_on_ref_target`: dependency tracing
//! - `build_bb_assignment_map` / `global_assignment_map` (memoized): assignment lookup tables
//! - `rvalue_depends_on_ref_target`: rvalue dependency tracing
//!
//! Extracted from `codegen_rules_entry.rs` to keep files under 500 lines.
//! Part of #3094.

use rustc_public::mir::{
    AggregateKind, AssertMessage, Body, Operand, Place, Rvalue, StatementKind,
};
use std::collections::{HashMap, HashSet};

use crate::args::ChcTrackLevel;

use super::ChcCtx;

/// Extension trait for pointer runtime check suppression on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CodegenRulesPointerCheck<'tcx, 'body> {
    fn should_skip_reg_pointer_assert(
        &self,
        bb_idx: usize,
        cond: &Operand,
        msg: &AssertMessage,
    ) -> bool;
}

impl<'tcx, 'body> CodegenRulesPointerCheck<'tcx, 'body> for ChcCtx<'tcx, 'body> {
    /// Skip pointer runtime checks when the asserted pointer is provably safe.
    ///
    /// Two phases:
    /// 1. At ALL track levels, skip NullPointerDereference for pointers that are
    ///    provably non-null: static addresses, heap allocations, and reference-derived
    ///    pointers. Rust references are always non-null (language guarantee), static
    ///    addresses are compile-time constants, and heap allocations return obj_id >= 2.
    ///    Part of #3094: fixes false CTREX in Drop/Array tests that access static mut.
    /// 2. At Reg track only, also skip misalignment checks for ref-derived pointers
    ///    (value-semantics surrogates at Reg level are not real addresses).
    fn should_skip_reg_pointer_assert(
        &self,
        bb_idx: usize,
        cond: &Operand,
        msg: &AssertMessage,
    ) -> bool {
        // Phase 1: At ALL track levels, skip NullPointerDereference for
        // provably non-null pointers (statics, allocations, references).
        // Uses global assignment map because the static pointer constant may
        // be assigned in an earlier block than the assert. Part of #3094.
        if matches!(msg, AssertMessage::NullPointerDereference) {
            let global_assignments = self.global_assignment_map();
            let mut visited = HashSet::new();
            if self.operand_depends_on_ref_target(cond, global_assignments, &mut visited, 8) {
                return true;
            }
        }

        // Phase 2: Reg-level only — skip misalignment + null checks for
        // ref-derived pointers (value-semantics surrogates).
        if self.track_level >= ChcTrackLevel::Ptr {
            return false;
        }
        // Part of #2793: Per-BB assignment map for Reg-level check.
        let bb_assignments = self.build_bb_assignment_map(bb_idx);
        let mut visited = HashSet::new();
        match msg {
            AssertMessage::MisalignedPointerDereference { found, .. } => {
                self.operand_depends_on_ref_target(found, &bb_assignments, &mut visited, 8)
            }
            // NullPointerDereference already checked in Phase 1 above.
            _ => false,
        }
    }
}

// Dependency tracing helpers for pointer check suppression.
impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(super) fn operand_depends_on_ref_target(
        &self,
        operand: &Operand,
        bb_assignments: &HashMap<usize, &Rvalue>,
        visited: &mut HashSet<usize>,
        depth: usize,
    ) -> bool {
        if depth == 0 {
            return false;
        }
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.place_depends_on_ref_target(place, bb_assignments, visited, depth)
            }
            Operand::Constant(_) => false,
        }
    }

    // Part of CHC null-deref obligation: also reused by
    // `emit_raw_ptr_null_deref_check` (expr/codegen_expr_deref_null_check.rs)
    // as the "provably non-null" whitelist, hence the widened visibility.
    pub(in crate::codegen_ay::chc) fn place_depends_on_ref_target(
        &self,
        place: &Place,
        bb_assignments: &HashMap<usize, &Rvalue>,
        visited: &mut HashSet<usize>,
        depth: usize,
    ) -> bool {
        if self.ref_resolution.ref_targets.contains_key(&place.local) {
            return true;
        }
        // Part of #3012: Allocation-derived pointers are always non-NULL
        // (obj_id >= 2, pointer = concat(obj_id, 0)). Skip NULL checks
        // for locals that received heap allocation results.
        //
        // Defense-in-depth (null-deref fix): require the recorded obj_id to be
        // non-null. `try_extract_data_obj_id` already filters obj_id == 0 at
        // the producer side, but consumers cross-check here in case a future
        // producer leaks the null sentinel into `alloc_result_locals`.
        if self.ref_resolution.alloc_result_locals.contains(&place.local)
            && self.known_alloc_ids.get(&place.local).copied().map(|id| id != 0).unwrap_or(true)
        {
            return true;
        }
        // Part of #3094: Static pointer locals are always non-NULL — they
        // hold addresses of statically allocated data. MIR emits raw pointer
        // NULL checks for `static mut` accesses, but these are false positives.
        if self.ref_resolution.static_ref_to_state_idx.contains_key(&place.local) {
            return true;
        }
        if depth == 0 || !visited.insert(place.local) {
            return false;
        }
        // Part of #2793: O(1) HashMap lookup replaces O(Stmt) linear scan.
        let rhs = bb_assignments.get(&place.local).copied();
        match rhs {
            Some(rvalue) => {
                self.rvalue_depends_on_ref_target(rvalue, bb_assignments, visited, depth - 1)
            }
            None => false,
        }
    }

    /// Build a map of local_idx -> last assignment Rvalue for a basic block.
    /// Part of #2793: Pre-computed O(1) lookup replacing per-call O(Stmt) scans.
    fn build_bb_assignment_map(&self, bb_idx: usize) -> HashMap<usize, &Rvalue> {
        let mut map = HashMap::new();
        if let Some(bb_data) = self.body.blocks.get(bb_idx) {
            // Forward scan: later assignments overwrite earlier ones,
            // producing the same "last assignment" semantics as the
            // original reverse-scan approach.
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.projection.is_empty()
                {
                    map.insert(lhs.local, rhs);
                }
            }
        }
        map
    }

    /// Precomputed assignment map across ALL blocks for cross-block dependency
    /// tracing. Built once at construction (a pure function of `body`) and
    /// stored on the context — the same map is reused by every raw-pointer deref
    /// null check and pointer-check suppression query. Part of the
    /// null-provenance perf fix: this was previously rebuilt (O(body)) per call.
    ///
    /// Part of #3094: NullPointerDereference conditions may depend on static
    /// pointer locals assigned in earlier blocks (e.g., constant static address
    /// in bb0, cast in bb1, null check in bb2). Single-block maps miss these chains.
    pub(in crate::codegen_ay::chc) fn global_assignment_map(
        &self,
    ) -> &HashMap<usize, &'body Rvalue> {
        &self.global_assignment_map
    }

    /// One-pass builder for [`Self::global_assignment_map`], invoked once from
    /// the `ChcCtx` constructor. Associated (not `&self`) so the returned
    /// borrows are tied to `body`'s `'body` lifetime, keeping `ChcCtx` covariant.
    pub(in crate::codegen_ay::chc) fn build_global_assignment_map(
        body: &'body Body,
    ) -> HashMap<usize, &'body Rvalue> {
        let mut map = HashMap::new();
        for bb_data in &body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.projection.is_empty()
                {
                    map.insert(lhs.local, rhs);
                }
            }
        }
        map
    }

    fn rvalue_depends_on_ref_target(
        &self,
        rvalue: &Rvalue,
        bb_assignments: &HashMap<usize, &Rvalue>,
        visited: &mut HashSet<usize>,
        depth: usize,
    ) -> bool {
        if depth == 0 {
            return false;
        }
        match rvalue {
            Rvalue::Use(operand) => {
                self.operand_depends_on_ref_target(operand, bb_assignments, visited, depth)
            }
            // Part of #1836: Trace through Cast operands for null-check suppression.
            Rvalue::Cast(_, operand, _) => {
                self.operand_depends_on_ref_target(operand, bb_assignments, visited, depth)
            }
            // Part of #1836: Trace through UnaryOp and BinaryOp operands.
            Rvalue::UnaryOp(_, operand) => {
                self.operand_depends_on_ref_target(operand, bb_assignments, visited, depth)
            }
            Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                self.operand_depends_on_ref_target(lhs, bb_assignments, visited, depth)
                    || self.operand_depends_on_ref_target(rhs, bb_assignments, visited, depth)
            }
            Rvalue::Ref(_, _, place)
            | Rvalue::AddressOf(_, place)
            | Rvalue::Len(place)
            | Rvalue::Discriminant(place) => {
                self.place_depends_on_ref_target(place, bb_assignments, visited, depth)
            }
            // A wide / `from_raw_parts` raw pointer's ADDRESS is its data
            // pointer (the metadata lane does not affect nullness), so it is
            // null iff the data pointer is null. If the data operand traces to a
            // ref/alloc/static base, the whole pointer is provably non-null.
            // Trace the FIRST (data) operand only. Sound: reaches a non-null
            // conclusion solely via a genuine base case.
            Rvalue::Aggregate(AggregateKind::RawPtr(_, _), ops) => ops.first().is_some_and(|op| {
                self.operand_depends_on_ref_target(op, bb_assignments, visited, depth)
            }),
            _ => false, // external enum: Rvalue
        }
    }
}
