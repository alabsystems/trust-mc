// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::codegen_types::CodegenTypes;
use super::{
    ARRAYSOLVER_FIELD_DIRTY, ARRAYSOLVER_FIELD_SCOPES, ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT,
    ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES, ARRAYSOLVER_FIELD_TRAIL_TERMS, ChcCtx, ChcVecFields, Expr,
    HashSet, POINTER_WIDTH, collect_leaf_sorts, vec_layout,
};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc::call) fn constrain_visible_array_solver_push(
        &mut self,
        receiver_local: usize,
        modified_locals: &HashSet<usize>,
        constraints: &mut Vec<Expr>,
    ) -> bool {
        let visible_local = self.resolve_flattened_array_solver_local(receiver_local);
        if self.flatten.flattened_tuple_locals.contains(&visible_local) {
            let owner_ty = match self.struct_embedded_owner_ty(visible_local) {
                Some(ty) => ty,
                None => return false,
            };
            let struct_sort = match Self::translate_ty(owner_ty) {
                Some(sort) => sort,
                None => return false,
            };
            let dt = match struct_sort.datatype_sort() {
                Some(dt) if dt.constructors.len() == 1 => dt,
                _ => return false,
            };
            let cons = &dt.constructors[0];
            let scopes_base = Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_SCOPES);
            let trail_terms_base =
                Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_TRAIL_TERMS);
            let total_leaves: usize =
                cons.fields.iter().map(|field| collect_leaf_sorts(&field.sort, 0).len()).sum();
            let mut values =
                match self.flattened_array_solver_state_var_fields(visible_local, total_leaves) {
                    Some(values) => values,
                    None => return false,
                };

            let old_ptr = match values[scopes_base + vec_layout::IDX_PTR].clone() {
                Some(expr) => expr,
                None => return false,
            };
            let old_len = match values[scopes_base + vec_layout::IDX_LEN].clone() {
                Some(expr) => expr,
                None => return false,
            };
            let old_cap = match values[scopes_base + vec_layout::IDX_CAP].clone() {
                Some(expr) => expr,
                None => return false,
            };
            let old_data = match values[scopes_base + vec_layout::IDX_DATA].clone() {
                Some(expr) if expr.sort().is_array() => expr,
                _ => return false,
            };
            let marker = match values[trail_terms_base + vec_layout::IDX_LEN].clone() {
                Some(expr) => expr,
                None => return false,
            };

            let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
            let new_data = old_data.store(old_len.clone(), marker);
            let new_len = old_len.bvadd(one);
            let new_cap =
                Expr::ite(old_cap.clone().bvult(new_len.clone()), new_len.clone(), old_cap.clone());
            let sidecar_len = new_len.clone();
            let sidecar_cap = new_cap.clone();
            let new_ptr = self.allocate_vec_backing_on_zero_cap_growth(
                old_ptr,
                &old_cap,
                &new_cap,
                None,
                constraints,
            );
            constraints.push(new_cap.clone().bvuge(new_len.clone()));

            values[scopes_base + vec_layout::IDX_PTR] = Some(new_ptr);
            values[scopes_base + vec_layout::IDX_LEN] = Some(new_len);
            values[scopes_base + vec_layout::IDX_CAP] = Some(new_cap);
            values[scopes_base + vec_layout::IDX_DATA] = Some(new_data);

            self.constrain_array_solver_field_sidecars(
                receiver_local,
                ARRAYSOLVER_FIELD_SCOPES,
                sidecar_len,
                Some(sidecar_cap),
                constraints,
            );
            self.constrain_array_solver_projected_vec_field(
                receiver_local,
                ARRAYSOLVER_FIELD_SCOPES,
                &values,
                scopes_base,
                constraints,
            );
            if !self.constrain_flattened_fields_for_call(visible_local, &values, constraints) {
                return false;
            }
            return self.constrain_array_solver_alias_output_from_flattened(
                receiver_local,
                visible_local,
                &values,
                modified_locals,
                constraints,
            );
        }

        let struct_in = match self.try_resolve_local_expr(receiver_local, modified_locals) {
            Some(expr) => expr,
            None => return false,
        };
        let scopes_proj = Self::array_solver_field_projection(ARRAYSOLVER_FIELD_SCOPES);
        let trail_terms_proj = Self::array_solver_field_projection(ARRAYSOLVER_FIELD_TRAIL_TERMS);
        let scopes_expr = match Self::apply_field_selections(struct_in.clone(), &scopes_proj) {
            Some(expr) => expr,
            None => return false,
        };
        let trail_terms_expr =
            match Self::apply_field_selections(struct_in.clone(), &trail_terms_proj) {
                Some(expr) => expr,
                None => return false,
            };
        let ChcVecFields { vec_sort, ptr, len, cap, data } =
            match ChcVecFields::extract(scopes_expr) {
                Some(fields) => fields,
                None => return false,
            };
        let marker = match ChcVecFields::extract(trail_terms_expr) {
            Some(fields) => fields.len,
            None => return false,
        };

        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let new_data = data.store(len.clone(), marker);
        let new_len = len.bvadd(one);
        let new_cap = Expr::ite(cap.clone().bvult(new_len.clone()), new_len.clone(), cap.clone());
        let sidecar_len = new_len.clone();
        let sidecar_cap = new_cap.clone();
        let new_ptr =
            self.allocate_vec_backing_on_zero_cap_growth(ptr, &cap, &new_cap, None, constraints);
        constraints.push(new_cap.clone().bvuge(new_len.clone()));
        let new_scopes = match Self::rebuild_vec_expr(vec_sort, new_ptr, new_len, new_cap, new_data)
        {
            Some(expr) => expr,
            None => return false,
        };
        let new_struct = match Self::apply_projection_update(&struct_in, &scopes_proj, new_scopes) {
            Some(expr) => expr,
            None => return false,
        };
        self.constrain_array_solver_field_sidecars(
            receiver_local,
            ARRAYSOLVER_FIELD_SCOPES,
            sidecar_len,
            Some(sidecar_cap),
            constraints,
        );
        self.constrain_array_solver_receiver_output_expr(receiver_local, new_struct, constraints)
    }

    pub(in crate::codegen_ay::chc::call) fn constrain_visible_array_solver_pop(
        &mut self,
        receiver_local: usize,
        modified_locals: &HashSet<usize>,
        is_empty: Expr,
        constraints: &mut Vec<Expr>,
    ) -> bool {
        let visible_local = self.resolve_flattened_array_solver_local(receiver_local);
        if self.flatten.flattened_tuple_locals.contains(&visible_local) {
            let owner_ty = match self.struct_embedded_owner_ty(visible_local) {
                Some(ty) => ty,
                None => return false,
            };
            let struct_sort = match Self::translate_ty(owner_ty) {
                Some(sort) => sort,
                None => return false,
            };
            let dt = match struct_sort.datatype_sort() {
                Some(dt) if dt.constructors.len() == 1 => dt,
                _ => return false,
            };
            let cons = &dt.constructors[0];
            let scopes_base = Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_SCOPES);
            let trail_terms_base =
                Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_TRAIL_TERMS);
            let trail_prev_present_base =
                Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT);
            let trail_prev_values_base =
                Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES);
            let dirty_base = Self::flattened_struct_field_base(cons, ARRAYSOLVER_FIELD_DIRTY);
            let total_leaves: usize =
                cons.fields.iter().map(|field| collect_leaf_sorts(&field.sort, 0).len()).sum();
            let mut values =
                match self.flattened_array_solver_state_var_fields(visible_local, total_leaves) {
                    Some(values) => values,
                    None => return false,
                };

            let old_len = match values[scopes_base + vec_layout::IDX_LEN].clone() {
                Some(expr) => expr,
                None => return false,
            };
            let old_data = match values[scopes_base + vec_layout::IDX_DATA].clone() {
                Some(expr) if expr.sort().is_array() => expr,
                _ => return false,
            };
            let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
            let new_len = Expr::ite(is_empty.clone(), old_len.clone(), old_len.bvsub(one));
            let marker = old_data.select(new_len.clone());
            let sidecar_scopes_len = new_len.clone();
            let trail_terms_len = match values[trail_terms_base + vec_layout::IDX_LEN].clone() {
                Some(expr) => expr,
                None => return false,
            };
            let trail_prev_present_len =
                match values[trail_prev_present_base + vec_layout::IDX_LEN].clone() {
                    Some(expr) => expr,
                    None => return false,
                };
            let trail_prev_values_len =
                match values[trail_prev_values_base + vec_layout::IDX_LEN].clone() {
                    Some(expr) => expr,
                    None => return false,
                };

            values[scopes_base + vec_layout::IDX_LEN] = Some(new_len);

            for base in [trail_terms_base, trail_prev_present_base, trail_prev_values_base] {
                let current_len = match values[base + vec_layout::IDX_LEN].clone() {
                    Some(expr) => expr,
                    None => return false,
                };
                values[base + vec_layout::IDX_LEN] =
                    Some(Expr::ite(is_empty.clone(), current_len, marker.clone()));
            }

            let current_dirty = match values[dirty_base].clone() {
                Some(expr) => expr,
                None => return false,
            };
            values[dirty_base] =
                Some(Expr::ite(is_empty.clone(), current_dirty, Expr::bool_const(true)));
            self.constrain_array_solver_field_sidecars(
                receiver_local,
                ARRAYSOLVER_FIELD_SCOPES,
                sidecar_scopes_len,
                None,
                constraints,
            );
            self.constrain_array_solver_field_sidecars(
                receiver_local,
                ARRAYSOLVER_FIELD_TRAIL_TERMS,
                Expr::ite(is_empty.clone(), trail_terms_len, marker.clone()),
                None,
                constraints,
            );
            self.constrain_array_solver_field_sidecars(
                receiver_local,
                ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT,
                Expr::ite(is_empty.clone(), trail_prev_present_len, marker.clone()),
                None,
                constraints,
            );
            self.constrain_array_solver_field_sidecars(
                receiver_local,
                ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES,
                Expr::ite(is_empty, trail_prev_values_len, marker),
                None,
                constraints,
            );
            self.constrain_array_solver_projected_vec_field(
                receiver_local,
                ARRAYSOLVER_FIELD_SCOPES,
                &values,
                scopes_base,
                constraints,
            );
            self.constrain_array_solver_projected_vec_field(
                receiver_local,
                ARRAYSOLVER_FIELD_TRAIL_TERMS,
                &values,
                trail_terms_base,
                constraints,
            );
            self.constrain_array_solver_projected_vec_field(
                receiver_local,
                ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT,
                &values,
                trail_prev_present_base,
                constraints,
            );
            self.constrain_array_solver_projected_vec_field(
                receiver_local,
                ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES,
                &values,
                trail_prev_values_base,
                constraints,
            );
            if !self.constrain_flattened_fields_for_call(visible_local, &values, constraints) {
                return false;
            }
            return self.constrain_array_solver_alias_output_from_flattened(
                receiver_local,
                visible_local,
                &values,
                modified_locals,
                constraints,
            );
        }

        let struct_in = match self.try_resolve_local_expr(receiver_local, modified_locals) {
            Some(expr) => expr,
            None => return false,
        };
        let scopes_proj = Self::array_solver_field_projection(ARRAYSOLVER_FIELD_SCOPES);
        let trail_terms_proj = Self::array_solver_field_projection(ARRAYSOLVER_FIELD_TRAIL_TERMS);
        let trail_prev_present_proj =
            Self::array_solver_field_projection(ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT);
        let trail_prev_values_proj =
            Self::array_solver_field_projection(ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES);
        let dirty_proj = Self::array_solver_field_projection(ARRAYSOLVER_FIELD_DIRTY);

        let scopes_expr = match Self::apply_field_selections(struct_in.clone(), &scopes_proj) {
            Some(expr) => expr,
            None => return false,
        };
        let ChcVecFields { vec_sort, ptr, len, cap, data } =
            match ChcVecFields::extract(scopes_expr) {
                Some(fields) => fields,
                None => return false,
            };
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let new_len = Expr::ite(is_empty.clone(), len.clone(), len.bvsub(one));
        let marker = data.clone().select(new_len.clone());
        let sidecar_scopes_len = new_len.clone();
        let trail_terms_current =
            match Self::apply_field_selections(struct_in.clone(), &trail_terms_proj) {
                Some(expr) => expr,
                None => return false,
            };
        let trail_prev_present_current =
            match Self::apply_field_selections(struct_in.clone(), &trail_prev_present_proj) {
                Some(expr) => expr,
                None => return false,
            };
        let trail_prev_values_current =
            match Self::apply_field_selections(struct_in.clone(), &trail_prev_values_proj) {
                Some(expr) => expr,
                None => return false,
            };
        let trail_terms_len = match ChcVecFields::extract(trail_terms_current) {
            Some(fields) => fields.len,
            None => return false,
        };
        let trail_prev_present_len = match ChcVecFields::extract(trail_prev_present_current) {
            Some(fields) => fields.len,
            None => return false,
        };
        let trail_prev_values_len = match ChcVecFields::extract(trail_prev_values_current) {
            Some(fields) => fields.len,
            None => return false,
        };
        let new_scopes = match Self::rebuild_vec_expr(vec_sort, ptr, new_len, cap, data) {
            Some(expr) => expr,
            None => return false,
        };
        let mut new_struct =
            match Self::apply_projection_update(&struct_in, &scopes_proj, new_scopes) {
                Some(expr) => expr,
                None => return false,
            };

        for field_proj in [&trail_terms_proj, &trail_prev_present_proj, &trail_prev_values_proj] {
            let current_vec = match Self::apply_field_selections(struct_in.clone(), field_proj) {
                Some(expr) => expr,
                None => return false,
            };
            let restored_vec = match Self::rebuild_vec_with_len(current_vec.clone(), marker.clone())
            {
                Some(expr) => Expr::ite(is_empty.clone(), current_vec, expr),
                None => return false,
            };
            new_struct = match Self::apply_projection_update(&new_struct, field_proj, restored_vec)
            {
                Some(expr) => expr,
                None => return false,
            };
        }

        let current_dirty = match Self::apply_field_selections(struct_in, &dirty_proj) {
            Some(expr) => expr,
            None => return false,
        };
        let new_dirty = Expr::ite(is_empty.clone(), current_dirty, Expr::bool_const(true));
        new_struct = match Self::apply_projection_update(&new_struct, &dirty_proj, new_dirty) {
            Some(expr) => expr,
            None => return false,
        };
        self.constrain_array_solver_field_sidecars(
            receiver_local,
            ARRAYSOLVER_FIELD_SCOPES,
            sidecar_scopes_len,
            None,
            constraints,
        );
        self.constrain_array_solver_field_sidecars(
            receiver_local,
            ARRAYSOLVER_FIELD_TRAIL_TERMS,
            Expr::ite(is_empty.clone(), trail_terms_len, marker.clone()),
            None,
            constraints,
        );
        self.constrain_array_solver_field_sidecars(
            receiver_local,
            ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT,
            Expr::ite(is_empty.clone(), trail_prev_present_len, marker.clone()),
            None,
            constraints,
        );
        self.constrain_array_solver_field_sidecars(
            receiver_local,
            ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES,
            Expr::ite(is_empty, trail_prev_values_len, marker),
            None,
            constraints,
        );
        self.constrain_array_solver_receiver_output_expr(receiver_local, new_struct, constraints)
    }
}
