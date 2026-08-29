// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Field+Index mixed projection on flattened locals.
//!
//! Extracted from `codegen_expr_flattened.rs` — Part of #4206.

use std::collections::HashSet;

use ay_bindings::Expr;
use tracing::{debug, warn};

use super::codegen_decl_flatten::compute_nested_flat_slot;
use super::codegen_types::CodegenTypes;
use super::{ChcCtx, FieldProjection, UnknownProjectionPolicy, collect_field_projections};

use rustc_public::mir::Place;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translates Field+Index mixed projection chains on flattened locals.
    ///
    /// Handles patterns like `_5.1[_12]` where _5 is a flattened ArrayWrapper.
    /// First tries direct slot access via compute_nested_flat_slot + select(),
    /// then falls back to reconstruct_flattened_root + translate_place_field_index.
    /// Returns `None` if the projection chain doesn't match the mixed pattern.
    ///
    /// Part of #3908 Step 2: extracted from translate_place_with_modified.
    pub(in crate::codegen_ay::chc) fn translate_flattened_mixed_field_index(
        &self,
        place: &Place,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
        use rustc_public::mir::ProjectionElem;

        let has_field_and_index =
            place.projection.iter().any(|p| {
                matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
            }) && place.projection.iter().any(|p| matches!(p, ProjectionElem::Field(..)));
        if !has_field_and_index {
            return None;
        }

        // Part of #3830/#3041: Direct slot access for Field+Index on flattened locals.
        // Split at the Index and resolve the field prefix as flattened slot metadata.
        // This preserves Downcast+Field information for multi-constructor enums.
        let index_pos = place.projection.iter().position(|p| {
            matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
        });
        if let Some(index_pos) = index_pos
            && index_pos > 0
            && index_pos + 1 == place.projection.len()
        {
            let field_projections = collect_field_projections(
                &place.projection[..index_pos],
                UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
            );
            if let Some(field_ty) = field_projections.last().and_then(|fp| fp.field_ty)
                && let Some(leaf_slot) =
                    self.flattened_mixed_field_index_slot(local_idx, &field_projections)
            {
                let field_count = self.flattened_field_count(local_idx);
                if leaf_slot < field_count
                    && let Some(array_expr) =
                        self.flattened_local_field_expr(local_idx, leaf_slot, modified_locals)
                    && array_expr.sort().is_array()
                {
                    let idx_proj = &place.projection[index_pos];
                    let index_expr = match idx_proj {
                        ProjectionElem::Index(index_local) => {
                            self.resolve_local_expr(*index_local, modified_locals).map(|raw| {
                                coerce_bitvec_width_safe(
                                    raw,
                                    POINTER_WIDTH,
                                    SignExtension::ZeroExtend,
                                )
                            })
                        }
                        ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                            // #from_end needs the slice's runtime length -> fail closed (projection_path.rs)
                            super::constant_index_offset(*offset, *min_length, *from_end)
                                .map(|i| Expr::bitvec_const(i as u128, POINTER_WIDTH))
                        }
                        _ => None,
                    };
                    if let Some(idx) = index_expr {
                        debug!(
                            local_idx,
                            leaf_slot,
                            "CHC: direct slot access for Field+Index read on flattened local"
                        );
                        let mut selected = self
                            .finite_fixed_array_select(&array_expr, &idx, field_ty)
                            .unwrap_or_else(|| array_expr.select(idx));
                        if let Some(elem_ty) = self.get_array_element_ty(field_ty)
                            && selected.sort().is_bitvec()
                            && let Some(elem_sort) = Self::translate_ty(elem_ty)
                            && elem_sort.is_datatype()
                            && let Some(unflat) =
                                crate::codegen_ay::types::unflatten_bitvec_to_datatype(
                                    &selected, &elem_sort,
                                )
                        {
                            selected = unflat;
                        }
                        return Some(selected);
                    }
                }
            }
        }

        // Fallback: reconstruct the full Datatype root and apply Field+Index.
        if let Some(root) = self.reconstruct_flattened_root(local_idx, modified_locals) {
            debug!(
                local_idx,
                "CHC: #3041 Category E — Field+Index on flattened local, using reconstruct+field_index"
            );
            return self.translate_place_field_index(
                &place.projection,
                root,
                Some(self.body.locals()[local_idx].ty),
                modified_locals,
            );
        }
        let n_fields = self.flattened_field_count(local_idx);
        let has_dt =
            self.body.locals().get(local_idx).and_then(|ld| Self::translate_ty(ld.ty)).and_then(
                |s| {
                    s.datatype_sort().map(|dt| {
                        (
                            dt.constructors.len(),
                            dt.constructors.first().map(|c| c.fields.len()).unwrap_or(0),
                        )
                    })
                },
            );
        warn!(
            local_idx,
            n_fields,
            dt_info = ?has_dt,
            "CHC: #3814 Field+Index on flattened local but reconstruct_flattened_root failed"
        );
        None
    }

    fn flattened_mixed_field_index_slot(
        &self,
        local_idx: usize,
        field_projections: &[FieldProjection],
    ) -> Option<usize> {
        let first = field_projections.first()?;
        if let Some(cons_idx) = first.cons_idx {
            if !field_projections[1..].iter().all(|fp| fp.cons_idx.is_none()) {
                return None;
            }
            let remaining = &field_projections[1..];
            if let Some(layout) = self.flatten.enum_bv_layouts.get(&local_idx)
                && cons_idx < layout.ctor_field_slot.len()
                && first.field_idx < layout.ctor_field_slot[cons_idx].len()
            {
                let base_slot = layout.payload_slot(cons_idx, first.field_idx)?;
                let nested_offset = self.enum_payload_nested_slot_offset(
                    local_idx,
                    cons_idx,
                    first.field_idx,
                    remaining,
                )?;
                return Some(1 + base_slot + nested_offset);
            }

            let n_fields = self.flattened_field_count(local_idx);
            let payload_start = if n_fields == 1 {
                0
            } else if n_fields == 3 {
                let true_discr =
                    self.flatten.flattened_enum_discr.get(&local_idx).map(|(t, _)| *t).unwrap_or(0);
                if (cons_idx as u64) == true_discr { 1 } else { 2 }
            } else {
                1
            };
            let nested_offset = self.enum_payload_nested_slot_offset(
                local_idx,
                cons_idx,
                first.field_idx,
                remaining,
            )?;
            return Some(payload_start + nested_offset);
        }

        if !field_projections.iter().all(|fp| fp.cons_idx.is_none()) {
            return None;
        }
        let local_decl = self.body.locals().get(local_idx)?;
        let sort = Self::translate_ty(local_decl.ty)?;
        let field_indices: Vec<usize> = field_projections.iter().map(|fp| fp.field_idx).collect();
        compute_nested_flat_slot(&sort, &field_indices)
    }

    fn enum_payload_nested_slot_offset(
        &self,
        local_idx: usize,
        cons_idx: usize,
        field_idx: usize,
        remaining: &[FieldProjection],
    ) -> Option<usize> {
        if remaining.is_empty() {
            return Some(0);
        }
        let local_decl = self.body.locals().get(local_idx)?;
        let sort = Self::translate_ty(local_decl.ty)?;
        let dt = sort.datatype_sort()?;
        let variant = dt.constructors.get(cons_idx)?;
        let payload_sort = &variant.fields.get(field_idx)?.sort;
        let remaining_indices: Vec<usize> = remaining.iter().map(|fp| fp.field_idx).collect();
        compute_nested_flat_slot(payload_sort, &remaining_indices)
    }

    pub(in crate::codegen_ay::chc) fn finite_fixed_array_select(
        &self,
        array_expr: &Expr,
        index_expr: &Expr,
        array_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        use crate::codegen_ay::types::POINTER_WIDTH;

        let array_len = self.get_array_length(array_ty)?;
        if array_len == 0 {
            return None;
        }

        let const_select =
            |idx: usize| array_expr.clone().select(Expr::bitvec_const(idx as u128, POINTER_WIDTH));

        let mut selected = const_select(array_len - 1);
        for idx in (0..array_len - 1).rev() {
            let idx_expr = Expr::bitvec_const(idx as u128, POINTER_WIDTH);
            let is_idx = index_expr.clone().eq(idx_expr);
            selected = Expr::ite(is_idx, const_select(idx), selected);
        }
        Some(selected)
    }
}
