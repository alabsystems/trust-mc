// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Flattened place translation: projects on flattened locals (tuples, enums, etc.).
//!
//! Extracted from `codegen_expr.rs` — Part of #4206.
//! Methods in this module handle the translation of MIR Place projections
//! on locals that have been flattened into multiple scalar state variables.

use std::collections::HashSet;

use ay_bindings::Expr;
use tracing::{debug, warn};

use super::ChcCtx;
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_ctx::record_translation_drop_site_reason_for_fn;
use super::codegen_decl_flatten::{compute_nested_flat_slot, compute_nested_flat_span};
use super::codegen_expr_flattened_coroutine::FlattenedCoroutineRootProjection;
use super::codegen_types::CodegenTypes;
use super::{FieldProjection, UnknownProjectionPolicy, collect_field_projections};

use rustc_public::mir::Place;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #3041 Category E: Reconstruct a Datatype expression from flattened state vars.
    ///
    /// For a flattened local with N scalar state vars (fld0..fldN-1), reconstructs
    /// the corresponding Z3 Datatype by reading all field state vars and applying
    /// the Datatype constructor. Delegates to `reconstruct_nested_datatype_from_slots`
    /// for recursive reconstruction of nested Datatype fields that consume multiple
    /// leaf slots (e.g., LinearExpr with nested Rational → 5 leaves for 4 fields).
    /// Only supports single-constructor types (structs/tuples).
    pub(in crate::codegen_ay::chc) fn reconstruct_flattened_root(
        &self,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let local_decl = self.body.locals().get(local_idx)?;
        let local_ty = self
            .resolve_inline_local_ty(self.body, local_idx)
            .unwrap_or_else(|| self.resolve_body_ty(local_decl.ty));
        let sort = Self::translate_ty(local_ty)?;

        // Quick check: must be a single-constructor Datatype.
        let dt = sort.datatype_sort()?;
        if dt.constructors.len() != 1 {
            return None;
        }

        // Verify we have state vars for this local.
        let _vec_idx = self.try_state_idx_for_local(local_idx)?;
        let n_fields = self.flattened_field_count(local_idx);
        if n_fields == 0 {
            return None;
        }

        // Part of #3829: Use recursive reconstruction to handle nested Datatype
        // fields that consume multiple leaf slots. The recursive function walks
        // the Datatype sort tree, consuming one slot per scalar/array leaf and
        // recursing into nested Datatype fields. This replaces the flat 1:1
        // slot-to-field loop that failed when leaf count != field count.
        let (expr, consumed) =
            self.reconstruct_nested_datatype_from_slots(local_idx, 0, &sort, modified_locals)?;

        // Sanity check: all leaf slots must be consumed.
        if consumed != n_fields {
            debug!(
                local_idx,
                consumed,
                n_fields,
                "reconstruct_flattened_root: slot count mismatch after recursive reconstruction"
            );
            return None;
        }

        Some(expr)
    }

    /// Translates a MIR Place on a flattened local (tuple, Option, Result, etc.)
    /// by dispatching to the appropriate projection handler.
    ///
    /// Part of #3908 Step 5: routing method for flattened place translation.
    pub(in crate::codegen_ay::chc) fn translate_flattened_place(
        &self,
        place: &Place,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let vec_idx = self.try_state_idx_for_local(local_idx)?;

        match self.translate_flattened_coroutine_root_projection(place, local_idx, modified_locals)
        {
            FlattenedCoroutineRootProjection::Translated(expr) => return Some(expr),
            FlattenedCoroutineRootProjection::Failed => return None,
            FlattenedCoroutineRootProjection::NotApplicable => {}
        }

        // A. Mixed Field+Index on flattened locals (e.g., `_5.1[_12]`).
        if let Some(expr) =
            self.translate_flattened_mixed_field_index(place, local_idx, modified_locals)
        {
            return Some(expr);
        }

        let field_projections = collect_field_projections(
            &place.projection,
            UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
        );

        // B. Single-field projection (struct/enum).
        if field_projections.len() == 1 {
            return self.translate_flattened_single_field(
                local_idx,
                vec_idx,
                &field_projections[0],
                modified_locals,
            );
        }
        // C. Multi-level struct field projections (stays inline — 31 lines).
        if field_projections.len() > 1 && field_projections.iter().all(|fp| fp.cons_idx.is_none()) {
            if let Some(local_decl) = self.body.locals().get(local_idx)
                && let Some(sort) = Self::translate_ty(local_decl.ty)
            {
                let field_indices: Vec<usize> =
                    field_projections.iter().map(|fp| fp.field_idx).collect();
                if let Some(leaf_offset) = compute_nested_flat_slot(&sort, &field_indices) {
                    let slot = vec_idx + leaf_offset;
                    let vars = if modified_locals.contains(&local_idx) {
                        &self.state_var_mgr.output_state_vars
                    } else {
                        &self.state_var_mgr.state_vars
                    };
                    return if let Some((name, sort)) = vars.get(slot) {
                        Some(Expr::var(&**name, sort.clone()))
                    } else {
                        warn!(
                            local_idx,
                            slot, "translate_place: nested flattened field out of bounds"
                        );
                        None
                    };
                } else if let Some((offset, leaf_count)) =
                    compute_nested_flat_span(&sort, &field_indices)
                    && let Some(terminal_sort) =
                        field_indices.iter().try_fold(sort.clone(), |current_sort, &field_idx| {
                            let dt = current_sort.datatype_sort()?;
                            if dt.constructors.len() != 1 {
                                return None;
                            }
                            dt.constructors[0].fields.get(field_idx).map(|field| field.sort.clone())
                        })
                    && let Some((expr, consumed)) = self.reconstruct_nested_datatype_from_slots(
                        local_idx,
                        offset,
                        &terminal_sort,
                        modified_locals,
                    )
                    && consumed == leaf_count
                {
                    return Some(expr);
                } else if self.flattened_field_count(local_idx) == 1
                    && field_projections.iter().all(|fp| fp.field_idx == 0)
                    && let Some(expr) =
                        self.flattened_local_field_expr(local_idx, 0, modified_locals)
                {
                    // Pin<Box<T>>, Box<Unique<NonNull<T>>>, and similar transparent
                    // wrapper chains flatten to a single opaque pointer slot. A chain
                    // of `.0` projections just re-exposes that pointer — return the
                    // sole state var directly instead of dropping the projection.
                    return Some(expr);
                }
            }
            // Fall through to unsupported if type lookup or slot computation fails.
        }
        // D. Downcast + nested field on flattened enums.
        if field_projections.len() > 1
            && field_projections[0].cons_idx.is_some()
            && field_projections[1..].iter().all(|fp| fp.cons_idx.is_none())
        {
            return self.translate_flattened_downcast_nested(
                local_idx,
                vec_idx,
                &field_projections,
                modified_locals,
            );
        }
        // E. Bare read: reconstruct Datatype from field state vars.
        if place.projection.is_empty() {
            return self.reconstruct_flattened_bare_read(local_idx, modified_locals);
        }
        // F. Unsupported projection fallback.
        self.diagnostics.place_translation_drop.inc();
        record_translation_drop_site_reason_for_fn(
            &self.fn_name,
            "flattened_projection_unsupported",
        );
        warn!(
            local_idx,
            projections = ?place.projection,
            "translate_place: unsupported projection on flattened local (#3814 diag)"
        );
        None
    }

    /// Translates multi-level Downcast+Field projection chains on flattened enums.
    /// Handles patterns like `(_N as Some).0.0` in iterator desugaring.
    ///
    /// Part of #3908 Step 4: extracted from translate_place_with_modified.
    fn translate_flattened_downcast_nested(
        &self,
        local_idx: usize,
        vec_idx: usize,
        field_projections: &[FieldProjection],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let cons_idx_val =
            field_projections[0].cons_idx.expect("guarded by is_some() check in caller");

        // Compute nested field offset within the payload type.
        let remaining_indices: Vec<usize> =
            field_projections[1..].iter().map(|fp| fp.field_idx).collect();

        // Part of #3994: Use enum_bv_layouts for multi-ctor BV-flattened enums.
        // ctor_field_slot gives the payload slot for each variant's field;
        // compute_nested_flat_slot resolves nested struct fields within that slot.
        let slot = if let Some(layout) = self.flatten.enum_bv_layouts.get(&local_idx)
            && cons_idx_val < layout.ctor_field_slot.len()
            && field_projections[0].field_idx < layout.ctor_field_slot[cons_idx_val].len()
        {
            let Some(base_slot) = layout.payload_slot(cons_idx_val, field_projections[0].field_idx)
            else {
                warn!(
                    local_idx,
                    cons_idx_val,
                    field_idx = field_projections[0].field_idx,
                    "translate_place: omitted flattened enum payload has no nested slot"
                );
                return None;
            };
            let nested_offset = if let Some(local_decl) = self.body.locals().get(local_idx)
                && let Some(sort) = Self::translate_ty(local_decl.ty)
                && let Some(dt) = sort.datatype_sort()
                && cons_idx_val < dt.constructors.len()
            {
                let variant = &dt.constructors[cons_idx_val];
                let payload_field_idx = field_projections[0].field_idx;
                if payload_field_idx < variant.fields.len() {
                    let payload_sort = &variant.fields[payload_field_idx].sort;
                    compute_nested_flat_slot(payload_sort, &remaining_indices).unwrap_or(0)
                } else {
                    0
                }
            } else {
                0
            };
            vec_idx + 1 + base_slot + nested_offset
        } else {
            // Fallback: Bool-flattened 2-variant enums without enum_bv_layouts.
            let n_fields = self.flattened_field_count(local_idx);
            let payload_start = if n_fields == 1 {
                0
            } else if n_fields == 3 {
                let true_discr =
                    self.flatten.flattened_enum_discr.get(&local_idx).map(|(t, _)| *t).unwrap_or(0);
                if (cons_idx_val as u64) == true_discr { 1 } else { 2 }
            } else {
                1
            };
            let payload_offset = if let Some(local_decl) = self.body.locals().get(local_idx)
                && let Some(sort) = Self::translate_ty(local_decl.ty)
                && let Some(dt) = sort.datatype_sort()
                && cons_idx_val < dt.constructors.len()
            {
                let variant = &dt.constructors[cons_idx_val];
                let payload_field_idx = field_projections[0].field_idx;
                if payload_field_idx < variant.fields.len() {
                    let payload_sort = &variant.fields[payload_field_idx].sort;
                    compute_nested_flat_slot(payload_sort, &remaining_indices).unwrap_or(0)
                } else {
                    0
                }
            } else {
                0
            };
            vec_idx + payload_start + payload_offset
        };
        let vars = if modified_locals.contains(&local_idx) {
            &self.state_var_mgr.output_state_vars
        } else {
            &self.state_var_mgr.state_vars
        };
        if let Some((name, sort)) = vars.get(slot) {
            debug!(
                local_idx,
                cons_idx_val, slot, "translate_place: downcast + nested field on flattened enum"
            );
            Some(Expr::var(&**name, sort.clone()))
        } else {
            warn!(local_idx, slot, "translate_place: downcast+nested field out of bounds");
            None
        }
    }

    /// Translates single-field projections on flattened locals.
    /// Handles Downcast+Field (enum variants) and pure Field (struct/tuple).
    ///
    /// Part of #3908 Step 3: extracted from translate_place_with_modified.
    fn translate_flattened_single_field(
        &self,
        local_idx: usize,
        vec_idx: usize,
        fp: &FieldProjection,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let n_fields = self.flattened_field_count(local_idx);
        let slot = if let Some(cons_idx) = fp.cons_idx {
            // Part of #3215: BV-flattened multi-ctor enum read path.
            if let Some(layout) = self.flatten.enum_bv_layouts.get(&local_idx)
                && cons_idx < layout.ctor_field_slot.len()
                && fp.field_idx < layout.ctor_field_slot[cons_idx].len()
            {
                let Some(payload_slot) = layout.payload_slot(cons_idx, fp.field_idx) else {
                    debug!(
                        local_idx,
                        cons_idx,
                        field_idx = fp.field_idx,
                        "translate_place: omitted flattened enum payload -> synthetic ZST value"
                    );
                    return Self::omitted_flattened_field_expr(fp.field_ty);
                };
                let payload_offset = 1 + payload_slot;
                // Part of #3041: Check if the payload spans multiple leaf slots.
                if let Some(local_decl) = self.body.locals().get(local_idx)
                    && let Some(sort) = Self::translate_ty(local_decl.ty)
                    && let Some(dt) = sort.datatype_sort()
                    && cons_idx < dt.constructors.len()
                {
                    let variant = &dt.constructors[cons_idx];
                    if fp.field_idx < variant.fields.len() {
                        let payload_sort = &variant.fields[fp.field_idx].sort;
                        let is_leaf = payload_sort.is_bitvec()
                            || payload_sort.is_bool()
                            || payload_sort.is_int()
                            || payload_sort.is_real()
                            || payload_sort.is_array();
                        if !is_leaf {
                            return self
                                .reconstruct_nested_datatype_from_slots(
                                    local_idx,
                                    payload_offset,
                                    payload_sort,
                                    modified_locals,
                                )
                                .map(|(expr, _)| expr);
                        }
                    }
                }
                vec_idx + payload_offset
            } else {
                // Compute payload start slot for Downcast+Field on flattened enum.
                let payload_start = if n_fields == 1 {
                    vec_idx
                } else if n_fields == 3 {
                    let true_discr =
                        if let Some((t, _)) = self.flatten.flattened_enum_discr.get(&local_idx) {
                            *t
                        } else {
                            warn!(
                                local_idx,
                                "flattened_enum_discr missing for 3-field enum; \
                             defaulting to Result-like (true_discr=0)"
                            );
                            0
                        };
                    if (cons_idx as u64) == true_discr { vec_idx + 1 } else { vec_idx + 2 }
                } else {
                    vec_idx + 1
                };
                // Part of #435: Check if the payload field is a multi-slot struct.
                if let Some(local_decl) = self.body.locals().get(local_idx)
                    && let Some(sort) = Self::translate_ty(local_decl.ty)
                    && let Some(dt) = sort.datatype_sort()
                    && cons_idx < dt.constructors.len()
                {
                    let variant = &dt.constructors[cons_idx];
                    if fp.field_idx < variant.fields.len() {
                        let payload_sort = &variant.fields[fp.field_idx].sort;
                        let is_leaf = payload_sort.is_bitvec()
                            || payload_sort.is_bool()
                            || payload_sort.is_int()
                            || payload_sort.is_real()
                            || payload_sort.is_array();
                        if !is_leaf {
                            return self
                                .reconstruct_nested_datatype_from_slots(
                                    local_idx,
                                    payload_start - vec_idx,
                                    payload_sort,
                                    modified_locals,
                                )
                                .map(|(expr, _)| expr);
                        }
                    }
                }
                payload_start
            }
        } else {
            // Struct/tuple Field: compute leaf offset from type sort structure.
            if let Some(local_decl) = self.body.locals().get(local_idx)
                && let Some(sort) = Self::translate_ty(local_decl.ty)
                && let Some(dt) = sort.datatype_sort()
                && dt.constructors.len() == 1
                && fp.field_idx < dt.constructors[0].fields.len()
            {
                let fields = &dt.constructors[0].fields;
                let target_sort = &fields[fp.field_idx].sort;
                let is_leaf = target_sort.is_bitvec()
                    || target_sort.is_bool()
                    || target_sort.is_int()
                    || target_sort.is_real()
                    || target_sort.is_array();
                let leaf_offset: usize = fields[..fp.field_idx]
                    .iter()
                    .map(|f| super::codegen_decl_flatten::collect_leaf_sorts(&f.sort, 0).len())
                    .sum();
                if is_leaf {
                    vec_idx + leaf_offset
                } else {
                    return self
                        .reconstruct_nested_datatype_from_slots(
                            local_idx,
                            leaf_offset,
                            target_sort,
                            modified_locals,
                        )
                        .map(|(expr, _)| expr);
                }
            } else {
                vec_idx + fp.field_idx
            }
        };
        if let Some(field_slot) = slot.checked_sub(vec_idx)
            && let Some(expr) = self.encode.flattened_field_env.get(&(local_idx, field_slot))
        {
            return Some(expr.clone());
        }
        let vars = if modified_locals.contains(&local_idx) {
            &self.state_var_mgr.output_state_vars
        } else {
            &self.state_var_mgr.state_vars
        };
        if let Some((name, sort)) = vars.get(slot) {
            Some(Expr::var(&**name, sort.clone()))
        } else {
            warn!(local_idx, slot, "flattened tuple field out of bounds");
            None
        }
    }
}
