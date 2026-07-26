// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Deref projection resolution for MIR place translation.
//!
//! Extracted from codegen_expr.rs per #2246 (500 LOC threshold).
//! - translate_place_with_deref: entry routing + base-expression resolution for
//!   Mem-level Deref+Field+Index handling
//!
//! Ref-target and argument-ref helpers live in `codegen_expr_deref_field.rs`;
//! static-ref helpers live in `codegen_expr_deref_static.rs` (Part of #2884).
//! Deref-resolution cascade lives in `codegen_expr_deref_resolve.rs` (Part of #4125).
//! Projection loop and array-select helpers live in
//! `codegen_expr_deref_projection.rs` (Part of #4125).
//! Subslice expression builder lives in `codegen_expr_deref_subslice.rs` (Part of #4125).
//!
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use tracing::debug;

use super::ChcCtx;
use super::codegen_expr_deref_resolve::DerefCascadeResult;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn known_deref_base_addr_expr(
        &self,
        local_idx: usize,
    ) -> Option<Expr> {
        if let Some(addr) = self.known_stack_addr_expr(local_idx) {
            debug!(local_idx, "CHC: resolved Deref base via known_stack_addr_exprs");
            return Some(addr);
        }
        self.known_alloc_ids.get(&local_idx).map(|&obj_id| {
            debug!(local_idx, obj_id, "CHC: resolved Deref base via known_alloc_ids (#3608)");
            Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32))
        })
    }

    /// Translates a MIR Place with Deref projections using memory loads.
    ///
    /// At Mem track level, this handles places like `*ptr`, `(*ptr).field`,
    /// and `*ptr[i]` by loading from type-indexed memory arrays.
    ///
    /// Part of #892: Phase 3 - Memory load/store operations.
    pub(in crate::codegen_ay::chc) fn translate_place_with_deref(
        &mut self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let local_idx: usize = place.local;

        // Check if this place has Deref projections
        let has_deref = place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref));

        // Part of #1888: Also check for Index projections that need bounds checking.
        // Array indexing (e.g., arr[idx]) must go through the full projection loop
        // to emit bounds checks, even when there's no Deref.
        let has_index = place.projection.iter().any(|p| {
            matches!(
                p,
                ProjectionElem::Index(_)
                    | ProjectionElem::ConstantIndex { .. }
                    | ProjectionElem::Subslice { .. }
            )
        });

        // If no Deref or Index, delegate to regular translation (Field-only projections)
        if !has_deref && !has_index {
            return self.translate_place_with_modified(place, modified_locals);
        }

        // Part of #3041 Category E: For non-Deref Index places on flattened locals,
        // delegate to translate_place_with_modified which has the Field+Index handler.
        // The Mem-level projection loop below uses state_idx_for_local which returns
        // the first flattened scalar slot, not the reconstructed Datatype root.
        // translate_place_with_modified reconstructs the Datatype first.
        if !has_deref && has_index && self.flatten.flattened_tuple_locals.contains(&local_idx) {
            debug!(
                local_idx,
                "CHC: #3041 Category E — delegating flattened Index place to translate_place_with_modified"
            );
            return self.translate_place_with_modified(place, modified_locals);
        }

        // Run the deref-resolution cascade (ref-targets, coroutine, const-ref,
        // arg-ref, static-ref, alloc-id, track-level guards). Part of #4125.
        if has_deref {
            match self.try_resolve_deref_cascade(place, local_idx, modified_locals) {
                DerefCascadeResult::Resolved(expr) => return Some(expr),
                DerefCascadeResult::Bail => return None,
                DerefCascadeResult::Unresolved => {}
            }
        }

        // At Mem level: handle Deref+Field projections with field-level type indexing
        // Part of #1161: Make load side symmetric with store side
        // Fix #2055: Check local_expr_env for modified locals first
        // Fix #2238: Use local_to_state_idx mapping (same fix as translate_place_with_modified)
        // Part of #3768: graceful fallback instead of panic on unregistered locals
        let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
            // Part of #4179: Raw pointer locals (from Box deref) may not be in
            // the state map but have a known allocation ID from store tracing.
            // Construct the BV64 address directly and enter the projection loop.
            if has_deref {
                if let Some(current_expr) = self.known_stack_addr_expr(local_idx) {
                    debug!(
                        local_idx,
                        "CHC: deref base local not in state map but has known stack address"
                    );
                    let current_ty = self.body.locals()[local_idx].ty;
                    return self.walk_deref_projection_loop(
                        place,
                        local_idx,
                        current_expr,
                        current_ty,
                        modified_locals,
                        has_deref,
                    );
                }
                if let Some(&obj_id) = self.known_alloc_ids.get(&local_idx) {
                    debug!(
                        local_idx,
                        obj_id,
                        "CHC: deref base local not in state map but has known alloc_id (#4179)"
                    );
                    let current_expr =
                        Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32));
                    let current_ty = self.body.locals()[local_idx].ty;
                    return self.walk_deref_projection_loop(
                        place,
                        local_idx,
                        current_expr,
                        current_ty,
                        modified_locals,
                        has_deref,
                    );
                }
            }
            debug!(local_idx, "CHC: deref base local not in state map — sound over-approx");
            self.record_sound_fallback_reason("state_idx_missing_deref_base");
            return None;
        };
        let current_expr = if modified_locals.contains(&local_idx) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&local_idx) {
                env_expr.clone()
            } else if let Some((name, sort)) = self.state_var_mgr.output_state_vars.get(vec_idx) {
                Expr::var(&**name, sort.clone())
            } else if has_deref {
                if let Some(addr) = self.known_stack_addr_expr(local_idx) {
                    addr
                } else if let Some(&obj_id) = self.known_alloc_ids.get(&local_idx) {
                    Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32))
                } else {
                    // Part of #3447: State var missing for deref base local.
                    self.record_aggregate_gap("deref_base_no_output_state_var");
                    debug!(local_idx, vec_idx, "CHC: deref base local has no output state var");
                    return None;
                }
            } else {
                // Part of #3447: State var missing for deref base local.
                self.record_aggregate_gap("deref_base_no_output_state_var_nonderef");
                debug!(local_idx, vec_idx, "CHC: deref base local has no output state var");
                return None;
            }
        } else if let Some((name, sort)) = self.state_var_mgr.state_vars.get(vec_idx) {
            Expr::var(&**name, sort.clone())
        } else if has_deref {
            if let Some(addr) = self.known_stack_addr_expr(local_idx) {
                addr
            } else if let Some(&obj_id) = self.known_alloc_ids.get(&local_idx) {
                Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32))
            } else {
                // Part of #3447: State var missing for deref base local.
                self.record_aggregate_gap("deref_base_no_state_var");
                debug!(local_idx, vec_idx, "CHC: deref base local has no state var");
                return None;
            }
        } else {
            // Part of #3447: State var missing for deref base local.
            self.record_aggregate_gap("deref_base_no_state_var_nonderef");
            debug!(local_idx, vec_idx, "CHC: deref base local has no state var");
            return None;
        };

        let current_ty = self.body.locals()[local_idx].ty;

        self.walk_deref_projection_loop(
            place,
            local_idx,
            current_expr,
            current_ty,
            modified_locals,
            has_deref,
        )
    }
}
