// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Struct-embedded Vec resize handling.
//!
//! When a Vec is accessed through a struct field (e.g., `m.marks.resize(n, false)`),
//! the collection_local resolves to the struct, not the Vec. This module
//! handles resize by extracting the Vec from the struct's state var, introducing
//! a fresh backing array linked by quantified growth constraints, and
//! reconstructing the struct.
//!
//! Extracted from `codegen_call_vec_ops.rs` per 500 LOC limit.
//! Part of #3647: struct-embedded Vec resize false proof.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::ProjectionElem;
use tracing::{debug, warn};

use crate::codegen_ay::names::vec_layout;

use super::ChcCtx;
use super::codegen_call_misc::CallMisc;
use super::codegen_call_vec::ChcVecFields;
use super::codegen_call_vec_ops::quantified_resize_growth_array;
use super::codegen_decl_flatten::collect_leaf_sorts;
use super::codegen_types::CodegenTypes;
use super::{UnknownProjectionPolicy, collect_field_projections};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Struct-embedded Vec resize: extract Vec from struct, invalidate data on
    /// growth, reconstruct.
    ///
    /// Handles two sub-cases mirroring `vec_push_struct_embedded`:
    /// - C1: Datatype struct — navigate Datatype selectors to Vec field
    /// - C2: Flattened struct — compute flat leaf offset to Vec's fields
    ///
    /// Part of #3647: struct-embedded Vec resize false proof.
    ///
    /// Task #69: returns `true` iff the struct's Vec state was actually
    /// updated (constraints emitted AND the output var routed into the rule
    /// head). Callers use `false` to record the fail-closed
    /// `vec_resize_state_unmodeled` marker instead of exiting silently.
    pub(in crate::codegen_ay::chc) fn vec_resize_struct_embedded(
        &mut self,
        coll_local: usize,
        args: &[rustc_public::mir::Operand],
        field_projections: &[ProjectionElem],
        new_len: Expr,
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) -> bool {
        debug!(coll_local, proj_len = field_projections.len(), "VecResize: struct-embedded entry");
        let struct_state_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied());
        let Some(struct_state_idx) = struct_state_idx else {
            debug!(coll_local, "VecResize: struct-embedded — no state var for struct local");
            return false;
        };
        let Some((_, in_sort)) = self.state_var_mgr.state_vars.get(struct_state_idx) else {
            return false;
        };
        let is_datatype = in_sort.datatype_name().is_some();

        let field_projs =
            collect_field_projections(field_projections, UnknownProjectionPolicy::Skip);
        if field_projs.is_empty() {
            return false;
        }

        let fill_value = args.get(2).and_then(|arg| {
            self.translate_operand_with_modified(arg, modified_locals)
                .or_else(|| self.resolve_ref_or_const_referent(arg, modified_locals))
        });

        if is_datatype {
            self.vec_resize_struct_embedded_datatype(
                coll_local,
                new_len,
                struct_state_idx,
                fill_value,
                &field_projs,
                extra_constraints,
                extra_dests,
            )
        } else {
            self.vec_resize_struct_embedded_flattened(
                coll_local,
                new_len,
                fill_value,
                modified_locals,
                &field_projs,
                extra_constraints,
                extra_dests,
            )
        }
    }

    /// C1: Datatype struct — navigate to Vec field, resize, reconstruct.
    /// Returns `true` iff the struct state var was updated (Task #69).
    fn vec_resize_struct_embedded_datatype(
        &mut self,
        coll_local: usize,
        new_len: Expr,
        struct_state_idx: usize,
        fill_value: Option<Expr>,
        field_projs: &[super::FieldProjection],
        extra_constraints: &mut Vec<Expr>,
        _extra_dests: &mut Vec<usize>,
    ) -> bool {
        let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(struct_state_idx) else {
            return false;
        };
        let struct_in = Expr::var(&**in_name, in_sort.clone());

        let Some(vec_expr) = Self::apply_field_selections(struct_in.clone(), field_projs) else {
            debug!(coll_local, "VecResize: struct-embedded C1 — apply_field_selections failed");
            return false;
        };

        if vec_expr.sort().datatype_name().is_none()
            || !Self::get_dt_field_sort(&vec_expr, vec_layout::FLD_DATA)
                .is_some_and(|s| s.is_array())
        {
            debug!(coll_local, "VecResize: struct-embedded C1 — field is not a Vec datatype");
            return false;
        }

        let Some(fields) = ChcVecFields::extract(vec_expr) else {
            debug!(coll_local, "VecResize: struct-embedded C1 — ChcVecFields::extract failed");
            return false;
        };
        let ChcVecFields { vec_sort, ptr, len: old_len, cap, data } = fields;

        // Resize: len' = new_len, cap' = max(cap, new_len).
        let grow_needed = cap.clone().bvult(new_len.clone());
        let new_cap = Expr::ite(grow_needed, new_len.clone(), cap);
        extra_constraints.push(new_cap.clone().bvuge(new_len.clone()));

        let (out_data, resize_relation, modeled_fill) =
            quantified_resize_growth_array(data, old_len, new_len.clone(), fill_value);
        extra_constraints.push(resize_relation);
        if !modeled_fill {
            // Part of #3447: struct resize growth without a translated fill value
            // still over-approximates the new suffix as unconstrained.
            self.record_aggregate_gap("vec_struct_resize_growth_no_fill");
        }

        // Reconstruct Vec with updated fields.
        let vec_dt_name_owned = vec_sort
            .datatype_name()
            .expect("invariant: ChcVecFields::extract ensures datatype")
            .to_owned();
        let vec_cons_name = crate::codegen_ay::names::cons_name(&vec_dt_name_owned);
        let new_vec = Expr::datatype_constructor(
            &vec_dt_name_owned,
            vec_cons_name,
            vec![ptr, new_len, new_cap, out_data],
            vec_sort,
        );

        // Reconstruct struct with updated Vec field.
        let Some(new_struct) = Self::apply_projection_update(&struct_in, field_projs, new_vec)
        else {
            warn!(coll_local, "VecResize: struct-embedded C1 — apply_projection_update failed");
            return false;
        };

        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(struct_state_idx).cloned()
        {
            let out_var = Expr::var(&*out_name, out_sort);
            extra_constraints.push(out_var.eq(new_struct));
            self.mark_state_var_modified(struct_state_idx);
            debug!(
                fn_name = %self.fn_name,
                coll_local,
                struct_state_idx,
                "VecResize: struct-embedded C1 (Datatype) — resize complete (#3647)"
            );
            return true;
        }
        false
    }

    /// C2: Flattened struct — compute flat base offset for Vec field, resize directly.
    /// Returns `true` iff the flattened Vec fields were constrained (Task #69).
    fn vec_resize_struct_embedded_flattened(
        &mut self,
        coll_local: usize,
        new_len: Expr,
        fill_value: Option<Expr>,
        modified_locals: &HashSet<usize>,
        field_projs: &[super::FieldProjection],
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) -> bool {
        if field_projs.len() != 1 {
            return false;
        }
        let target_field_idx = field_projs[0].field_idx;

        let owner_ty = match self.struct_embedded_owner_ty(coll_local) {
            Some(ty) => ty,
            None => return false,
        };
        let struct_sort = match Self::translate_ty(owner_ty) {
            Some(s) => s,
            None => return false,
        };
        let dt = match struct_sort.datatype_sort() {
            Some(d) => d,
            None => return false,
        };
        if dt.constructors.len() != 1 || target_field_idx >= dt.constructors[0].fields.len() {
            return false;
        }
        let cons = &dt.constructors[0];

        let mut flat_base = 0;
        for f in &cons.fields[..target_field_idx] {
            flat_base += collect_leaf_sorts(&f.sort, 0).len();
        }

        let target_sort = &cons.fields[target_field_idx].sort;
        let target_leaves = collect_leaf_sorts(target_sort, 0);
        if target_leaves.len() != 4 || !target_leaves[3].is_array() {
            debug!(
                coll_local,
                target_field_idx,
                leaf_count = target_leaves.len(),
                "VecResize: struct-embedded C2 — target field not a 4-field Vec"
            );
            return false;
        }

        let old_ptr = self.flattened_local_field_expr(coll_local, flat_base, modified_locals);
        let old_len = self.flattened_local_field_expr(coll_local, flat_base + 1, modified_locals);
        let old_cap = self.flattened_local_field_expr(coll_local, flat_base + 2, modified_locals);
        let old_data = self.flattened_local_field_expr(coll_local, flat_base + 3, modified_locals);

        let (Some(old_ptr_e), Some(old_len_e), Some(old_cap_e), Some(old_data_e)) =
            (old_ptr, old_len, old_cap, old_data)
        else {
            debug!(coll_local, flat_base, "VecResize: struct-embedded C2 — missing field exprs");
            return false;
        };
        if !old_data_e.sort().is_array() {
            return false;
        }

        // Resize: len' = new_len, cap' = max(cap, new_len).
        let grow_needed = old_cap_e.clone().bvult(new_len.clone());
        let new_cap = Expr::ite(grow_needed, new_len.clone(), old_cap_e);
        extra_constraints.push(new_cap.clone().bvuge(new_len.clone()));

        let (out_data, resize_relation, modeled_fill) =
            quantified_resize_growth_array(old_data_e, old_len_e, new_len.clone(), fill_value);
        extra_constraints.push(resize_relation);
        if !modeled_fill {
            // Part of #3447: struct resize growth without a translated fill value
            // still over-approximates the new suffix as unconstrained.
            self.record_aggregate_gap("vec_struct_resize_projected_growth_no_fill");
        }

        // Build full field values for the struct, carrying forward unmodified fields.
        let total_leaves: usize =
            cons.fields.iter().map(|f| collect_leaf_sorts(&f.sort, 0).len()).sum();
        let mut values: Vec<Option<Expr>> = Vec::with_capacity(total_leaves);
        for i in 0..total_leaves {
            values.push(self.flattened_local_field_expr(coll_local, i, modified_locals));
        }
        values[flat_base] = Some(old_ptr_e);
        values[flat_base + 1] = Some(new_len);
        values[flat_base + 2] = Some(new_cap);
        values[flat_base + 3] = Some(out_data);

        let emitted =
            self.constrain_flattened_fields_for_call(coll_local, &values, extra_constraints);
        if emitted {
            extra_dests.push(coll_local);
        }

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            target_field_idx,
            flat_base,
            emitted,
            "VecResize: struct-embedded C2 (flattened) — resize complete (#3647)"
        );
        emitted
    }
}
