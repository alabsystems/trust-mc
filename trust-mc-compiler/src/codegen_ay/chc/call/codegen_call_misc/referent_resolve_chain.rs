// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Array-chain referent resolution and raw_eq referent dispatch.
//!
//! - `resolve_ref_chain_to_array`: follows ref_targets chain + MIR scan to find
//!   array-sorted referents (max 4 hops, cycle-safe).
//! - `find_mir_source_local`: MIR statement/terminator scan for assignment sources.
//! - `resolve_raw_eq_referent_impl`: raw_eq argument resolution delegate.
//!
//! Extracted from `referent_resolve.rs` — Part of #4206.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Rvalue, StatementKind};
use std::collections::HashSet;
use tracing::warn;

use super::super::ChcCtx;
use super::CallMisc;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Follow the ref_targets chain from an operand until an Array-sorted
    /// expression is found.
    ///
    /// Slice/array comparisons arrive as `&[T; N]` references. When
    /// the MIR goes through `<&A as PartialOrd<&B>>::partial_cmp`, producing
    /// double-referenced operands (`&&[T; N]`).  `resolve_ref_or_const_referent`
    /// only peels one level, returning a BV64 pointer for the inner reference.
    /// This method follows the ref_targets chain until it finds an array-sorted
    /// expression (max 4 hops to avoid infinite loops).
    ///
    /// When ref_targets has no entry for a local, falls back to scanning MIR
    /// statements for Cast/Use/Ref patterns that created that local. This
    /// handles the Unsize coercion chain `&[T; N] → &[T]` where the cast
    /// destination is not tracked by numeric_ref_propagation.
    ///
    /// Part of #3806.
    pub(in crate::codegen_ay::chc) fn resolve_ref_chain_to_array(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let place = match arg {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }

        let mut current_local: usize = place.local;
        let mut visited = HashSet::new();
        for _hop in 0..4 {
            if !visited.insert(current_local) {
                return None; // cycle detection
            }
            // Try ref_targets first.
            if let Some(rt) = self.ref_resolution.ref_targets.get(&current_local) {
                let target_local = rt.local;
                // Always try translating the full place (with projections) — it may
                // resolve directly to an Array-sort value (e.g., Field(0) on a SIMD
                // struct gives the inner [T; N] array). Part of #3806.
                let target_place = rustc_public::mir::Place {
                    local: target_local,
                    projection: rt.projections.clone(),
                };
                if let Some(expr) =
                    self.translate_place_with_modified(&target_place, modified_locals)
                {
                    if expr.sort().is_array() {
                        return Some(expr);
                    }
                }
                // Continue the chain: for [Deref] projections (peeling one ref level),
                // follow through to the target local. For other non-empty projections
                // (Field, Index, etc.) we can't continue the local-to-local chain.
                // Part of #3806: handles `&&[T]` patterns where ref_targets has
                // Deref projections from `_N = &(*_M)` MIR patterns.
                if rt.projections.is_empty()
                    || (rt.projections.len() == 1
                        && matches!(rt.projections[0], rustc_public::mir::ProjectionElem::Deref))
                {
                    current_local = target_local;
                    continue;
                }
                return None;
            }

            // Check if the local's state var is already array-sorted.
            if let Some(&idx) = self.state_var_mgr.local_to_state_idx.get(&current_local) {
                if let Some((_, sort)) = self.state_var_mgr.state_vars.get(idx) {
                    if sort.is_array() {
                        let (name, sort) = if modified_locals.contains(&current_local) {
                            self.state_var_mgr.output_state_vars.get(idx)?
                        } else {
                            self.state_var_mgr.state_vars.get(idx)?
                        };
                        return Some(Expr::var(&**name, sort.clone()));
                    }
                }
            }

            // Fallback: scan MIR statements to find what assigned this local.
            // This handles Cast(Unsize) and Use/Ref patterns not tracked by
            // ref_targets propagation. Part of #3806.
            if let Some(src_local) = self.find_mir_source_local(current_local) {
                current_local = src_local;
                continue;
            }

            return None;
        }
        None
    }

    /// Scan MIR body to find the source local of an assignment to `dest_local`.
    ///
    /// Returns `Some(source_local)` for patterns:
    /// - `_dest = Cast(_, Copy/Move(_src), _)` (Unsize, PtrToPtr, etc.)
    /// - `_dest = Use(Copy/Move(_src))`
    /// - `_dest = Ref(_, _, Place { local: _src, .. })` (only empty projection)
    ///
    /// Part of #3806: enables resolve_ref_chain_to_array to follow through
    /// Unsize coercion chains that ref_targets propagation misses.
    fn find_mir_source_local(&self, dest_local: usize) -> Option<usize> {
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if place.local != dest_local || !place.projection.is_empty() {
                    continue;
                }
                match rvalue {
                    Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                        if src.projection.is_empty() =>
                    {
                        return Some(src.local);
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if src.projection.is_empty() =>
                    {
                        return Some(src.local);
                    }
                    // Part of #3806: handle Ref with any projection (not just empty).
                    // For `_N = &(*_M).field`, return _M as the source local.
                    Rvalue::Ref(_, _, ref_place) => {
                        return Some(ref_place.local);
                    }
                    _ => {}
                }
            }
        }
        // Phase 2 (Part of #3806): scan call terminators for dest locals.
        // When a local is assigned by a function call (e.g., `_38 = call index(&_34, ...)`),
        // the assignment doesn't appear as a statement — it's the call terminator's
        // destination. Return the first arg's local as the "source", enabling
        // resolve_ref_chain_to_array to follow through call boundaries.
        for bb in &self.body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { args, destination, .. } =
                &bb.terminator.kind
            {
                if destination.local == dest_local && destination.projection.is_empty() {
                    if let Some(
                        rustc_public::mir::Operand::Copy(src)
                        | rustc_public::mir::Operand::Move(src),
                    ) = args.first()
                    {
                        if src.projection.is_empty() {
                            warn!(
                                dest_local,
                                src_local = src.local,
                                "[#3806 chain] find_mir_source: call terminator dest"
                            );
                            return Some(src.local);
                        }
                    }
                }
            }
        }
        None
    }

    /// Resolve a `raw_eq` argument to its referent value (Part of #2173).
    ///
    /// `raw_eq<T>(a: &T, b: &T)` compares referents, not pointers.
    pub(in crate::codegen_ay::chc) fn resolve_raw_eq_referent_impl(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        self.resolve_ref_or_const_referent(arg, modified_locals)
    }
}
