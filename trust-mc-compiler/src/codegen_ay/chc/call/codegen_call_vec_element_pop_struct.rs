// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Struct-embedded Vec pop handling.
//!
//! When a Vec is accessed through a struct field (for example
//! `self.scopes.pop()`), the collection local resolves to the owning struct,
//! not the Vec. This module extracts the embedded Vec, lowers the pop
//! semantics, and reconstructs the updated struct.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::ProjectionElem;
use tracing::{debug, warn};

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

use super::ChcCtx;
use super::codegen_call_vec::ChcVecFields;
use super::codegen_call_vec_element_pop_struct_array_solver::{
    ARRAYSOLVER_FIELD_ASSIGN_TERMS, ARRAYSOLVER_FIELD_ASSIGN_VALUES,
    ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT, ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES,
    ARRAYSOLVER_FIELD_TRAIL_TERMS, array_solver_pop_aux_for_scopes_field,
    array_solver_pop_restored_struct_after_scopes_pop, array_solver_pop_scope_snapshot_select,
    overwrite_flattened_vec_leaves,
};
use super::codegen_decl_flatten::collect_leaf_sorts;
use super::codegen_types::CodegenTypes;
use super::{UnknownProjectionPolicy, collect_field_projections};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn vec_pop_struct_embedded(
        &mut self,
        coll_local: usize,
        field_projections: &[ProjectionElem],
        dest_local: usize,
        modified_locals: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
    ) -> bool {
        debug!(coll_local, proj_len = field_projections.len(), "VecPop: struct-embedded entry");
        let struct_state_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied());
        let Some(struct_state_idx) = struct_state_idx else {
            debug!(coll_local, "VecPop: struct-embedded — no state var for struct local");
            return false;
        };
        let Some((_, in_sort)) = self.state_var_mgr.state_vars.get(struct_state_idx) else {
            return false;
        };

        let field_projs =
            collect_field_projections(field_projections, UnknownProjectionPolicy::Skip);
        if field_projs.is_empty() {
            return false;
        }

        if in_sort.datatype_name().is_some() {
            self.vec_pop_struct_embedded_datatype(
                coll_local,
                dest_local,
                modified_locals,
                struct_state_idx,
                &field_projs,
                acc,
            )
        } else {
            self.vec_pop_struct_embedded_flattened(
                coll_local,
                dest_local,
                modified_locals,
                &field_projs,
                acc,
            )
        }
    }

    fn vec_pop_struct_embedded_datatype(
        &mut self,
        coll_local: usize,
        dest_local: usize,
        modified_locals: &HashSet<usize>,
        struct_state_idx: usize,
        field_projs: &[super::FieldProjection],
        acc: &mut CallAccumulator<'_>,
    ) -> bool {
        let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(struct_state_idx) else {
            return false;
        };
        let struct_in = Expr::var(&**in_name, in_sort.clone());

        let Some(vec_expr) = Self::apply_field_selections(struct_in.clone(), field_projs) else {
            debug!(coll_local, "VecPop: struct-embedded C1 — apply_field_selections failed");
            return false;
        };
        if vec_expr.sort().datatype_name().is_none()
            || !Self::get_dt_field_sort(&vec_expr, vec_layout::FLD_DATA)
                .is_some_and(|s| s.is_array())
        {
            debug!(coll_local, "VecPop: struct-embedded C1 — field is not a Vec datatype");
            return false;
        }

        let Some(fields) = ChcVecFields::extract(vec_expr) else {
            debug!(coll_local, "VecPop: struct-embedded C1 — ChcVecFields::extract failed");
            return false;
        };
        let ChcVecFields { vec_sort, ptr, len, cap, data } = fields;

        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let is_nonempty = len.clone().ne(zero.clone());
        let new_len = Expr::ite(is_nonempty.clone(), len.bvsub(one), zero);
        acc.constraints.push(cap.clone().bvuge(new_len.clone()));

        let elem_sort = data.sort().array_sort().map_or_else(ptr_sort, |a| a.element_sort.clone());
        let option_result = self.build_vec_pop_option_result(
            data.clone(),
            elem_sort,
            is_nonempty.clone(),
            new_len.clone(),
        );

        let vec_dt_name_owned = vec_sort
            .datatype_name()
            .expect("invariant: ChcVecFields::extract ensures datatype")
            .to_owned();
        let vec_cons_name = crate::codegen_ay::names::cons_name(&vec_dt_name_owned);
        let new_vec = Expr::datatype_constructor(
            &vec_dt_name_owned,
            vec_cons_name,
            vec![ptr, new_len.clone(), cap, data.clone()],
            vec_sort,
        );

        let marker = data.select(new_len.clone());
        let new_struct = if let Some(aux) =
            array_solver_pop_aux_for_scopes_field(self, coll_local, field_projs)
        {
            array_solver_pop_restored_struct_after_scopes_pop(
                struct_in,
                field_projs,
                aux,
                new_vec,
                marker,
                is_nonempty,
                new_len,
            )
        } else {
            Self::apply_projection_update(&struct_in, field_projs, new_vec)
        };
        let Some(new_struct) = new_struct else {
            warn!(coll_local, "VecPop: struct-embedded C1 — apply_projection_update failed");
            return false;
        };

        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(struct_state_idx).cloned()
        {
            let out_var = Expr::var(&*out_name, out_sort);
            acc.constraints.push(out_var.eq(new_struct));
            self.mark_state_var_modified(struct_state_idx);
        }

        let dest_bound = option_result.is_some_and(|result| {
            self.bind_vec_pop_destination(dest_local, modified_locals, result, acc.constraints)
        });

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            struct_state_idx,
            "VecPop: struct-embedded C1 (Datatype) — pop complete (#4050)"
        );
        dest_bound
    }

    fn vec_pop_struct_embedded_flattened(
        &mut self,
        coll_local: usize,
        dest_local: usize,
        modified_locals: &HashSet<usize>,
        field_projs: &[super::FieldProjection],
        acc: &mut CallAccumulator<'_>,
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

        let flat_base = Self::flattened_struct_field_base(cons, target_field_idx);

        let target_sort = &cons.fields[target_field_idx].sort;
        let target_leaves = collect_leaf_sorts(target_sort, 0);
        if target_leaves.len() != vec_layout::FIELD_COUNT
            || !target_leaves[vec_layout::IDX_DATA].is_array()
        {
            debug!(
                coll_local,
                target_field_idx,
                leaf_count = target_leaves.len(),
                "VecPop: struct-embedded C2 — target field not a 4-field Vec"
            );
            return false;
        }

        let old_ptr = self.flattened_local_field_expr(
            coll_local,
            flat_base + vec_layout::IDX_PTR,
            modified_locals,
        );
        let old_len = self.flattened_local_field_expr(
            coll_local,
            flat_base + vec_layout::IDX_LEN,
            modified_locals,
        );
        let old_cap = self.flattened_local_field_expr(
            coll_local,
            flat_base + vec_layout::IDX_CAP,
            modified_locals,
        );
        let old_data = self.flattened_local_field_expr(
            coll_local,
            flat_base + vec_layout::IDX_DATA,
            modified_locals,
        );

        let (Some(old_ptr_e), Some(old_len_e), Some(old_cap_e), Some(old_data_e)) =
            (old_ptr, old_len, old_cap, old_data)
        else {
            debug!(coll_local, flat_base, "VecPop: struct-embedded C2 — missing field exprs");
            return false;
        };
        if !old_data_e.sort().is_array() {
            return false;
        }

        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let is_nonempty = old_len_e.clone().ne(zero.clone());
        let new_len = Expr::ite(is_nonempty.clone(), old_len_e.bvsub(one), zero);
        acc.constraints.push(old_cap_e.clone().bvuge(new_len.clone()));

        let elem_sort =
            old_data_e.sort().array_sort().map_or_else(ptr_sort, |a| a.element_sort.clone());
        let option_result = self.build_vec_pop_option_result(
            old_data_e.clone(),
            elem_sort,
            is_nonempty.clone(),
            new_len.clone(),
        );

        let total_leaves: usize =
            cons.fields.iter().map(|f| collect_leaf_sorts(&f.sort, 0).len()).sum();
        let mut values: Vec<Option<Expr>> = Vec::with_capacity(total_leaves);
        for i in 0..total_leaves {
            values.push(self.flattened_local_field_expr(coll_local, i, modified_locals));
        }
        values[flat_base + vec_layout::IDX_PTR] = Some(old_ptr_e);
        values[flat_base + vec_layout::IDX_LEN] = Some(new_len.clone());
        values[flat_base + vec_layout::IDX_CAP] = Some(old_cap_e);
        values[flat_base + vec_layout::IDX_DATA] = Some(old_data_e.clone());

        if let Some(aux) = array_solver_pop_aux_for_scopes_field(self, coll_local, field_projs) {
            let assign_terms_base =
                Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_ASSIGN_TERMS);
            let assign_values_base =
                Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_ASSIGN_VALUES);
            let trail_terms_base =
                Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_TRAIL_TERMS);
            let trail_prev_present_base =
                Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT);
            let trail_prev_values_base =
                Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES);

            let current_assign_terms = self.rebuild_flattened_vec_expr(
                &cons.fields[ARRAYSOLVER_FIELD_ASSIGN_TERMS].sort,
                &values[assign_terms_base..assign_terms_base + vec_layout::FIELD_COUNT],
            );
            let current_assign_values = self.rebuild_flattened_vec_expr(
                &cons.fields[ARRAYSOLVER_FIELD_ASSIGN_VALUES].sort,
                &values[assign_values_base..assign_values_base + vec_layout::FIELD_COUNT],
            );
            let Some(current_assign_terms) = current_assign_terms else {
                return false;
            };
            let Some(current_assign_values) = current_assign_values else {
                return false;
            };
            let restored_assign_terms = Expr::ite(
                is_nonempty.clone(),
                array_solver_pop_scope_snapshot_select(
                    &aux.scope_snap_assign_terms_var,
                    &cons.fields[ARRAYSOLVER_FIELD_ASSIGN_TERMS].sort,
                    new_len.clone(),
                ),
                current_assign_terms,
            );
            let restored_assign_values = Expr::ite(
                is_nonempty.clone(),
                array_solver_pop_scope_snapshot_select(
                    &aux.scope_snap_assign_values_var,
                    &cons.fields[ARRAYSOLVER_FIELD_ASSIGN_VALUES].sort,
                    new_len.clone(),
                ),
                current_assign_values,
            );
            if !overwrite_flattened_vec_leaves(
                &mut values,
                assign_terms_base,
                &restored_assign_terms,
            ) || !overwrite_flattened_vec_leaves(
                &mut values,
                assign_values_base,
                &restored_assign_values,
            ) {
                return false;
            }

            let Some(current_trail_terms_len) =
                values[trail_terms_base + vec_layout::IDX_LEN].clone()
            else {
                return false;
            };
            let Some(current_trail_prev_present_len) =
                values[trail_prev_present_base + vec_layout::IDX_LEN].clone()
            else {
                return false;
            };
            let Some(current_trail_prev_values_len) =
                values[trail_prev_values_base + vec_layout::IDX_LEN].clone()
            else {
                return false;
            };
            let marker = old_data_e.select(new_len);
            let restored_trail_len =
                Expr::ite(is_nonempty.clone(), marker, current_trail_terms_len);
            values[trail_terms_base + vec_layout::IDX_LEN] = Some(restored_trail_len.clone());
            values[trail_prev_present_base + vec_layout::IDX_LEN] = Some(Expr::ite(
                is_nonempty.clone(),
                restored_trail_len.clone(),
                current_trail_prev_present_len,
            ));
            values[trail_prev_values_base + vec_layout::IDX_LEN] =
                Some(Expr::ite(is_nonempty, restored_trail_len, current_trail_prev_values_len));
        }

        let emitted =
            self.constrain_flattened_fields_for_call(coll_local, &values, acc.constraints);
        if emitted {
            acc.dests.push(coll_local);
        }

        let dest_bound = option_result.is_some_and(|result| {
            self.bind_vec_pop_destination(dest_local, modified_locals, result, acc.constraints)
        });

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            target_field_idx,
            flat_base,
            "VecPop: struct-embedded C2 (flattened) — pop complete (#4050)"
        );
        dest_bound
    }
}
