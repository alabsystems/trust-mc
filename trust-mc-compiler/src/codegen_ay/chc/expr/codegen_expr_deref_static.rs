// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Static-ref deref helpers extracted from `codegen_expr_deref_field.rs`.
//!
//! Keeps mutable-static root resolution and trailing projection handling
//! separate from ref-target / argument-ref helpers so the expression modules
//! stay below the repo's 500-line limit.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use tracing::debug;

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
use crate::rustc_public_bridge::IndexedVal;

use super::ChcCtx;
use super::codegen_stmt_projection::FieldProjection;
use super::codegen_types::CodegenTypes;
use super::constant_index_offset;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve the dereferenced root expression for a tracked static.
    ///
    /// For **immutable** statics with a known initial value, returns the
    /// concrete literal directly. This avoids depending on the state
    /// variable being propagated through CHC transitions — PDR may
    /// fail to synthesize the array invariant when the state variable is
    /// universally quantified in intermediate rules.
    ///
    /// Mutable statics always use state variables so prior stores are visible.
    pub(in crate::codegen_ay::chc) fn resolve_static_ref_root_expr(
        &self,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let &static_vec_idx = self.ref_resolution.static_ref_to_state_idx.get(&local_idx)?;
        let track_key = usize::MAX - static_vec_idx;

        if let Some(env_expr) = self.encode.local_expr_env.get(&track_key) {
            debug!(local_idx, static_vec_idx, "CHC: resolved *static via local_expr_env (#428)");
            return Some(env_expr.clone());
        }

        if (modified_locals.contains(&track_key)
            || self.encode.modified_state_indices.contains(&static_vec_idx))
            && let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(static_vec_idx)
        {
            debug!(local_idx, static_vec_idx, "CHC: resolved *static via output state var (#428)");
            return Some(Expr::var(&**out_name, out_sort.clone()));
        }

        // Part of #4072: For immutable statics, prefer the concrete initial
        // value literal over the state variable. The static state variable may
        // become a free universally-quantified term in CHC rules when PDR
        // cannot propagate the entry-rule constraint through all transitions.
        // Using the concrete literal directly embeds the data in each rule body,
        // making the proof independent of invariant synthesis for this variable.
        if !self.ref_resolution.mutable_static_state_idxs.contains(&static_vec_idx)
            && let Some(init_expr) = self.ref_resolution.static_initial_values.get(&static_vec_idx)
        {
            debug!(
                local_idx,
                static_vec_idx,
                "CHC: resolved *static via concrete initial value (immutable, #4072)"
            );
            return Some(init_expr.clone());
        }

        if let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(static_vec_idx) {
            debug!(local_idx, static_vec_idx, "CHC: resolved *static via input state var (#428)");
            return Some(Expr::var(&**in_name, in_sort.clone()));
        }

        None
    }

    /// Resolve deref through static pointer locals (#428).
    ///
    /// When `_N` was assigned a pointer to a `static mut`, `*_N` reads from
    /// the static's auxiliary state variable and applies any trailing
    /// value-semantics projections (`Downcast`, `Field`, `Index`, `Subslice`).
    pub(in crate::codegen_ay::chc) fn resolve_static_ref_deref(
        &mut self,
        place: &Place,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let deref_idx = place.projection.iter().position(|p| matches!(p, ProjectionElem::Deref))?;
        let remaining_projs = &place.projection[deref_idx + 1..];
        let mut current = self.resolve_static_ref_root_expr(local_idx, modified_locals)?;

        if remaining_projs.is_empty() {
            return Some(current);
        }

        let (pointee_ty, is_ref) = Self::deref_ref_ty(self.body.locals()[local_idx].ty);
        if !is_ref {
            return None;
        }
        let mut current_ty = Some(pointee_ty);
        let mut active_variant: Option<usize> = None;

        for proj in remaining_projs {
            match proj {
                ProjectionElem::Field(field_idx, field_ty) => {
                    let selections = vec![FieldProjection {
                        field_idx: *field_idx,
                        cons_idx: active_variant.take(),
                        field_ty: Some(*field_ty),
                    }];
                    current = Self::apply_field_selections(current, &selections)?;
                    current_ty = Some(*field_ty);
                }
                ProjectionElem::Downcast(variant_idx) => {
                    active_variant = Some(variant_idx.to_index());
                }
                ProjectionElem::Index(index_local) => {
                    let index_expr = self.resolve_local_expr(*index_local, modified_locals)?;
                    let index_expr = coerce_bitvec_width_safe(
                        index_expr,
                        POINTER_WIDTH,
                        SignExtension::ZeroExtend,
                    );
                    if let Some(ty) = current_ty
                        && let Some(array_len) = self.get_array_length(ty)
                    {
                        let len_expr = Expr::bitvec_const(array_len as u128, POINTER_WIDTH);
                        // clone: the same symbolic index is needed for both the bounds check
                        // and the subsequent array select.
                        self.heap_state.pending_checks.push(index_expr.clone().bvult(len_expr));
                    }
                    if !current.sort().is_array() {
                        return None;
                    }
                    current = current.select(index_expr);
                    current_ty = current_ty.and_then(|ty| self.get_array_element_ty(ty));
                    if let Some(ty) = current_ty {
                        current = self.try_unflatten_bv_to_datatype(current, ty);
                    }
                    active_variant = None;
                }
                ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                    // #from_end needs the slice's runtime length -> fail closed (projection_path.rs)
                    let Some(actual_offset) =
                        constant_index_offset(*offset, *min_length, *from_end)
                    else {
                        return None;
                    };
                    if let Some(ty) = current_ty
                        && let Some(array_len) = self.get_array_length(ty)
                    {
                        let index_expr_check =
                            Expr::bitvec_const(actual_offset as u128, POINTER_WIDTH);
                        let len_expr = Expr::bitvec_const(array_len as u128, POINTER_WIDTH);
                        self.heap_state.pending_checks.push(index_expr_check.bvult(len_expr));
                    }
                    let index_expr = Expr::bitvec_const(actual_offset as u128, POINTER_WIDTH);
                    if !current.sort().is_array() {
                        return None;
                    }
                    current = current.select(index_expr);
                    current_ty = current_ty.and_then(|ty| self.get_array_element_ty(ty));
                    if let Some(ty) = current_ty {
                        current = self.try_unflatten_bv_to_datatype(current, ty);
                    }
                    active_variant = None;
                }
                ProjectionElem::Subslice { from, to, from_end } => {
                    let ty = current_ty?;
                    current = self.build_subslice_expr(&current, ty, *from, *to, *from_end)?;
                    active_variant = None;
                }
                _ => return None,
            }
        }

        Some(current)
    }
}
