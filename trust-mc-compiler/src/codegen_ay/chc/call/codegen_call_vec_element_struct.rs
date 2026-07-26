// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Struct-embedded Vec push handling.
//!
//! When a Vec is accessed through a struct field (e.g., `m.indices.push(var)`),
//! the collection_local resolves to the struct, not the Vec. This module
//! handles push by extracting the Vec from the struct's state var, performing
//! the push operation, and reconstructing the struct.
//!
//! Extracted from `codegen_call_vec_element.rs` per 500 LOC limit.
//! Part of #3348: VecPush on struct-embedded Vec.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::ProjectionElem;
use tracing::{debug, warn};

use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;
use super::codegen_decl_flatten::collect_leaf_sorts;
use super::codegen_types::CodegenTypes;
use super::{UnknownProjectionPolicy, collect_field_projections};

use super::codegen_call_vec::ChcVecFields;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc::call) fn rebuild_flattened_vec_expr(
        &self,
        vec_sort: &ay_bindings::Sort,
        values: &[Option<Expr>],
    ) -> Option<Expr> {
        if values.len() != vec_layout::FIELD_COUNT {
            return None;
        }
        let [Some(ptr), Some(len), Some(cap), Some(data)] = values else {
            return None;
        };
        let dt_name = vec_sort.datatype_name()?.to_owned();
        let ctor_name = crate::codegen_ay::names::cons_name(&dt_name);
        Some(Expr::datatype_constructor(
            &dt_name,
            ctor_name,
            vec![ptr.clone(), len.clone(), cap.clone(), data.clone()],
            vec_sort.clone(),
        ))
    }

    pub(in crate::codegen_ay::chc::call) fn flattened_struct_field_base(
        cons: &ay_bindings::DatatypeConstructor,
        field_idx: usize,
    ) -> usize {
        cons.fields[..field_idx].iter().map(|f| collect_leaf_sorts(&f.sort, 0).len()).sum()
    }

    /// Struct-embedded Vec push: extract Vec from struct, push val, reconstruct.
    ///
    /// Handles two sub-cases mirroring the IndexMut store handler (#3439):
    /// - C1: Datatype struct — navigate Datatype selectors to Vec field
    /// - C2: Flattened struct — compute flat leaf offset to Vec's fields
    ///
    /// Part of #3348: VecPush on struct-embedded Vec.
    pub(in crate::codegen_ay::chc) fn vec_push_struct_embedded(
        &mut self,
        coll_local: usize,
        field_projections: &[ProjectionElem],
        val: Expr,
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        debug!(coll_local, proj_len = field_projections.len(), "VecPush: struct-embedded entry");
        // Resolve struct state var index.
        let struct_state_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied());
        let Some(struct_state_idx) = struct_state_idx else {
            debug!(coll_local, "VecPush: struct-embedded — no state var for struct local");
            return;
        };
        let Some((_, in_sort)) = self.state_var_mgr.state_vars.get(struct_state_idx) else {
            return;
        };
        let is_datatype = in_sort.datatype_name().is_some();

        let field_projs =
            collect_field_projections(field_projections, UnknownProjectionPolicy::Skip);
        if field_projs.is_empty() {
            return;
        }

        if is_datatype {
            self.vec_push_struct_embedded_datatype(
                coll_local,
                val,
                struct_state_idx,
                &field_projs,
                extra_constraints,
                extra_dests,
            );
        } else {
            self.vec_push_struct_embedded_flattened(
                coll_local,
                val,
                modified_locals,
                &field_projs,
                extra_constraints,
                extra_dests,
            );
        }
    }

    /// C1: Datatype struct — navigate to Vec field, push, reconstruct Vec and struct.
    fn vec_push_struct_embedded_datatype(
        &mut self,
        coll_local: usize,
        val: Expr,
        struct_state_idx: usize,
        field_projs: &[super::FieldProjection],
        extra_constraints: &mut Vec<Expr>,
        _extra_dests: &mut Vec<usize>,
    ) {
        let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(struct_state_idx) else {
            return;
        };
        let struct_in = Expr::var(&**in_name, in_sort.clone());

        // Navigate field projections to extract the Vec sub-expression.
        let Some(vec_expr) = Self::apply_field_selections(struct_in.clone(), field_projs) else {
            debug!(coll_local, "VecPush: struct-embedded C1 — apply_field_selections failed");
            return;
        };

        // Verify it's a Vec-like datatype with fld_data Array.
        if vec_expr.sort().datatype_name().is_none()
            || !Self::get_dt_field_sort(&vec_expr, vec_layout::FLD_DATA)
                .is_some_and(|s| s.is_array())
        {
            debug!(coll_local, "VecPush: struct-embedded C1 — field is not a Vec datatype");
            return;
        }

        // Extract Vec fields.
        let Some(fields) = ChcVecFields::extract(vec_expr) else {
            debug!(coll_local, "VecPush: struct-embedded C1 — ChcVecFields::extract failed");
            return;
        };
        let ChcVecFields { vec_sort, ptr, len, cap, data } = fields;

        // Perform push: data[len] = val, new_len = len + 1, new_cap = max(cap, new_len).
        let val = super::codegen_call_vec_ops::coerce_array_element(val, &data.sort());
        let new_data = data.store(len.clone(), val);
        let new_len = len.bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH));
        let grow_needed = cap.clone().bvult(new_len.clone());
        let new_cap = Expr::ite(grow_needed, new_len.clone(), cap.clone());
        let new_ptr = self.allocate_vec_backing_on_zero_cap_growth(
            ptr,
            &cap,
            &new_cap,
            field_projs.last().and_then(|proj| proj.field_ty),
            extra_constraints,
        );
        extra_constraints.push(new_cap.clone().bvuge(new_len.clone()));

        // Reconstruct Vec with updated fields.
        let vec_dt_name_owned = vec_sort
            .datatype_name()
            .expect("invariant: ChcVecFields::extract ensures datatype")
            .to_owned();
        let vec_cons_name = crate::codegen_ay::names::cons_name(&vec_dt_name_owned);
        let new_vec = Expr::datatype_constructor(
            &vec_dt_name_owned,
            vec_cons_name,
            vec![new_ptr, new_len, new_cap, new_data],
            vec_sort,
        );

        // Reconstruct struct with updated Vec field.
        let Some(new_struct) = Self::apply_projection_update(&struct_in, field_projs, new_vec)
        else {
            warn!(coll_local, "VecPush: struct-embedded C1 — apply_projection_update failed");
            return;
        };

        // Emit constraint: output_struct = new_struct.
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
                "VecPush: struct-embedded C1 (Datatype) — push complete (#3348)"
            );
        }
    }

    /// C2: Flattened struct — compute flat base offset for Vec field, push directly.
    fn vec_push_struct_embedded_flattened(
        &mut self,
        coll_local: usize,
        val: Expr,
        modified_locals: &HashSet<usize>,
        field_projs: &[super::FieldProjection],
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        // Only single-level field projections supported for flattened structs.
        if field_projs.len() != 1 {
            return;
        }
        let target_field_idx = field_projs[0].field_idx;

        // Recover the struct's original Datatype sort from the MIR type.
        let owner_ty = match self.struct_embedded_owner_ty(coll_local) {
            Some(ty) => ty,
            None => return,
        };
        let struct_sort = match Self::translate_ty(owner_ty) {
            Some(s) => s,
            None => return,
        };
        let dt = match struct_sort.datatype_sort() {
            Some(d) => d,
            None => return,
        };
        if dt.constructors.len() != 1 || target_field_idx >= dt.constructors[0].fields.len() {
            return;
        }
        let cons = &dt.constructors[0];

        // Compute flat base offset: sum of leaf counts for preceding fields.
        let flat_base = Self::flattened_struct_field_base(cons, target_field_idx);

        // Verify the target field is a Vec-like type with 4 leaf fields.
        let target_sort = &cons.fields[target_field_idx].sort;
        let target_leaves = collect_leaf_sorts(target_sort, 0);
        if target_leaves.len() != 4 || !target_leaves[3].is_array() {
            debug!(
                coll_local,
                target_field_idx,
                leaf_count = target_leaves.len(),
                "VecPush: struct-embedded C2 — target field not a 4-field Vec"
            );
            return;
        }

        // Read Vec's 4 leaf fields: ptr, len, cap, data.
        let old_ptr = self.flattened_local_field_expr(coll_local, flat_base, modified_locals);
        let old_len = self.flattened_local_field_expr(coll_local, flat_base + 1, modified_locals);
        let old_cap = self.flattened_local_field_expr(coll_local, flat_base + 2, modified_locals);
        let old_data = self.flattened_local_field_expr(coll_local, flat_base + 3, modified_locals);

        let (Some(old_ptr_e), Some(old_len_e), Some(old_cap_e), Some(old_data_e)) =
            (old_ptr, old_len, old_cap, old_data)
        else {
            debug!(coll_local, flat_base, "VecPush: struct-embedded C2 — missing field exprs");
            return;
        };
        if !old_data_e.sort().is_array() {
            return;
        }

        // Perform push: data[len] = val, new_len = len + 1, new_cap = max(cap, new_len).
        let val = super::codegen_call_vec_ops::coerce_array_element(val, &old_data_e.sort());
        let new_data = old_data_e.store(old_len_e.clone(), val);
        let new_len = old_len_e.bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH));
        let grow_needed = old_cap_e.clone().bvult(new_len.clone());
        let new_cap = Expr::ite(grow_needed, new_len.clone(), old_cap_e.clone());
        let new_ptr = self.allocate_vec_backing_on_zero_cap_growth(
            old_ptr_e,
            &old_cap_e,
            &new_cap,
            field_projs.last().and_then(|proj| proj.field_ty),
            extra_constraints,
        );
        extra_constraints.push(new_cap.clone().bvuge(new_len.clone()));

        // Build full field values for the struct.
        // Call handler `constrain_flattened_fields_for_call` treats None leaves
        // as nondeterministic — no carry-forward is emitted. For struct fields
        // NOT being modified (e.g., `data` Vec when we push to `indices` Vec),
        // we must explicitly carry forward their input values. Part of #3348.
        let total_leaves: usize =
            cons.fields.iter().map(|f| collect_leaf_sorts(&f.sort, 0).len()).sum();

        let mut values: Vec<Option<Expr>> = Vec::with_capacity(total_leaves);
        for i in 0..total_leaves {
            values.push(self.flattened_local_field_expr(coll_local, i, modified_locals));
        }
        // Overwrite the modified Vec's fields with updated values.
        values[flat_base] = Some(new_ptr);
        values[flat_base + 1] = Some(new_len);
        values[flat_base + 2] = Some(new_cap);
        values[flat_base + 3] = Some(new_data);

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
            "VecPush: struct-embedded C2 (flattened) — push complete (#3348)"
        );
    }
}
