// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Deref+Field offset-based load optimization.
//!
//! When a Deref is followed exclusively by Field projections (no Downcast),
//! the load side can compute a cumulative byte offset and perform a single
//! field-level memory load — symmetric with the store side's
//! `try_decompose_struct_store`.
//!
//! Extracted from `codegen_expr_deref.rs` per #4125 (500 LOC threshold).

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::ProjectionElem;
use tracing::debug;

use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_ctx::record_translation_drop_site_reason_for_fn;
use super::codegen_stmt_projection::FieldProjection;

/// Result of attempting the Deref+Field offset-based load optimization.
pub(in crate::codegen_ay::chc) enum DerefFieldOffsetResult {
    /// Successfully loaded via field-offset path. Contains the loaded expression.
    Loaded(Expr),
    /// Optimization not applicable (Downcast present, offset computation failed, etc.).
    /// Caller should fall through to whole-struct load.
    NotApplicable,
    /// Hard bail: non-bitvec pointer or load failure. Caller should return None.
    Bail,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Try to load via Deref+Field offset optimization.
    ///
    /// If all remaining projections after Deref are Field projections, compute
    /// the cumulative byte offset and load from the field-level type array.
    /// This is symmetric with the store side (`try_decompose_struct_store`).
    ///
    /// Part of #1161: Make load side symmetric with store side.
    /// Part of #2323 Gap 1: Downcast projections fall through (need variant-aware selection).
    pub(in crate::codegen_ay::chc) fn try_deref_field_offset_load(
        &mut self,
        current_expr: Expr,
        pointee_ty: rustc_public::ty::Ty,
        remaining_projs: &[ProjectionElem],
    ) -> DerefFieldOffsetResult {
        // Only applies when all remaining projections are Field (no Downcast).
        let all_fields = !remaining_projs.is_empty()
            && remaining_projs.iter().all(|p| matches!(p, ProjectionElem::Field(_, _)));

        if !all_fields {
            return DerefFieldOffsetResult::NotApplicable;
        }

        // Compute cumulative field offset
        let mut total_offset: u64 = 0;
        let mut load_ty = pointee_ty;
        let mut all_offsets_computed = true;

        for remaining_proj in remaining_projs {
            if let ProjectionElem::Field(field_idx, field_ty) = remaining_proj {
                if let Some(offset) = self.get_field_offset(load_ty, *field_idx) {
                    total_offset += offset;
                    load_ty = *field_ty;
                } else {
                    debug!("CHC: cannot compute field offset for field {}", *field_idx);
                    all_offsets_computed = false;
                    break;
                }
            } else {
                all_offsets_computed = false;
                break;
            }
        }

        if !all_offsets_computed {
            return DerefFieldOffsetResult::NotApplicable;
        }

        // Part of #2007: Guard against non-bitvec sorts.
        if !current_expr.sort().is_bitvec() {
            self.diagnostics.place_translation_drop.inc();
            record_translation_drop_site_reason_for_fn(
                &self.fn_name,
                "deref_non_bitvec_field_load",
            );
            debug!(
                "CHC: translate_place_with_deref - non-bitvec sort in Deref+Field load, returning None"
            );
            return DerefFieldOffsetResult::Bail;
        }

        // Compute address with field offset
        let addr = if total_offset > 0 {
            current_expr.bvadd(Expr::bitvec_const(total_offset as i64, POINTER_WIDTH))
        } else {
            current_expr
        };

        if let Some(expr) = self.try_stack_deref_field_expr(&addr, remaining_projs) {
            debug!(
                offset = total_offset,
                "CHC: translate_place_with_deref - resolved stack Deref+Field from flattened local"
            );
            return DerefFieldOffsetResult::Loaded(expr);
        }

        // Load from field-level type array (symmetric with store).
        // Dyn-tail normalization is handled inside load_from_memory (#3974).
        match self.load_from_memory(addr, load_ty) {
            Some(expr) => {
                debug!(
                    offset = total_offset,
                    "CHC: translate_place_with_deref - Deref+Field load at offset"
                );
                DerefFieldOffsetResult::Loaded(expr)
            }
            None => {
                self.record_aggregate_gap("deref_field_load_failed");
                debug!("CHC: Deref+Field load_from_memory returned None");
                DerefFieldOffsetResult::Bail
            }
        }
    }

    fn try_stack_deref_field_expr(
        &self,
        addr: &Expr,
        remaining_projs: &[ProjectionElem],
    ) -> Option<Expr> {
        let obj_id = match Self::try_extract_obj_id(addr) {
            Some(id) => id,
            None => {
                debug!(?addr, "CHC: stack Deref+Field has no constant obj_id");
                return None;
            }
        };
        let target_local = match self.heap_state.local_idx_for_obj_id(obj_id) {
            Some(local_idx) => local_idx,
            None => {
                debug!(obj_id, "CHC: stack Deref+Field obj_id has no stack local");
                return None;
            }
        };
        let source_local = if self.flatten.flattened_tuple_locals.contains(&target_local) {
            target_local
        } else if let Some(ref_target) = self.ref_resolution.ref_targets.get(&target_local)
            && ref_target.projections.is_empty()
            && self.flatten.flattened_tuple_locals.contains(&ref_target.local)
        {
            ref_target.local
        } else {
            debug!(obj_id, target_local, "CHC: stack Deref+Field target local is not flattened");
            return None;
        };
        let root = match self.reconstruct_flattened_bare_read(source_local, &HashSet::new()) {
            Some(expr) => expr,
            None => {
                debug!(
                    obj_id,
                    source_local, "CHC: stack Deref+Field could not reconstruct flattened local"
                );
                return None;
            }
        };
        let field_selections: Option<Vec<_>> = remaining_projs
            .iter()
            .map(|proj| match proj {
                ProjectionElem::Field(field_idx, field_ty) => Some(FieldProjection {
                    field_idx: *field_idx,
                    cons_idx: None,
                    field_ty: Some(*field_ty),
                }),
                _ => None,
            })
            .collect();
        let field_selections = field_selections?;
        let selected = Self::apply_field_selections(root, &field_selections);
        if selected.is_none() {
            debug!(obj_id, source_local, "CHC: stack Deref+Field field selection failed");
        }
        selected
    }
}
