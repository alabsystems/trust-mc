// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Struct-level map store method dispatch.

use std::sync::Arc;

use ay_bindings::Expr;

use super::scan::MapStorePattern;
use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::chc::call::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::call::codegen_call_coerce::CallCoerce;
use crate::codegen_ay::chc::codegen_ctx::types::EmbeddedMapAuxState;
use crate::codegen_ay::chc::codegen_decl_flatten;
use crate::codegen_ay::chc::codegen_rules::CodegenRules;
use crate::codegen_ay::chc::codegen_types::CodegenTypes;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(super) fn emit_map_store_method(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: &usize,
        struct_local: usize,
        inner_ty: &rustc_public::ty::Ty,
        pattern: &MapStorePattern,
        callee_name: &str,
    ) -> bool {
        let data_expr = match self.resolve_map_data_from_struct(
            struct_local,
            pattern.map_field_idx,
            inner_ty,
            dcx.modified_locals,
        ) {
            Some(e) => e,
            None => return false,
        };
        let key_expr = match self.resolve_callee_arg_for_map(dcx, pattern.key_local) {
            Some(e) => e,
            None => return false,
        };
        let value_expr = match self.resolve_callee_arg_for_map(dcx, pattern.value_local) {
            Some(e) => e,
            None => return false,
        };
        let present_expr =
            match self.resolve_map_present_from_struct(struct_local, dcx.modified_locals) {
                Some(e) => e,
                None => {
                    tracing::debug!(
                        struct_local,
                        callee = %callee_name,
                        "struct_map_accessor: store present array unavailable, falling through"
                    );
                    return false;
                }
            };

        let value_expr =
            ChcCtx::coerce_store_value(data_expr.sort(), value_expr, false, &self.diagnostics);
        let new_data = data_expr.store(key_expr.clone(), value_expr);

        let dest_local: usize = dcx.destination.local;
        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();

        if !self.emit_store_struct_state(
            dest_local,
            struct_local,
            pattern.map_field_idx,
            inner_ty,
            new_data,
            dcx.modified_locals,
            &mut extra_constraints,
        ) {
            return false;
        }

        self.emit_store_aux_state(
            dest_local,
            struct_local,
            pattern.map_field_idx,
            key_expr,
            present_expr,
            &mut extra_constraints,
            &mut extra_dests,
        );

        let new_output_args = self.build_output_args(dcx.modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );

        tracing::debug!(
            callee = %callee_name,
            struct_local,
            dest_local,
            map_field = pattern.map_field_idx,
            "CHC: struct BTreeMap store method dispatched (#3348)"
        );
        true
    }

    fn emit_store_struct_state(
        &mut self,
        dest_local: usize,
        struct_local: usize,
        map_field_idx: usize,
        inner_ty: &rustc_public::ty::Ty,
        new_data: Expr,
        modified_locals: &std::collections::HashSet<usize>,
        constraints: &mut Vec<Expr>,
    ) -> bool {
        let struct_sort = match Self::translate_ty(*inner_ty) {
            Some(s) => s,
            None => return false,
        };
        let Some(dt) = struct_sort.datatype_sort() else { return false };
        let Some(cons) = dt.constructors.first() else { return false };
        let Some(dest_idx) = self.try_state_idx_for_local(dest_local) else { return false };
        let Some((dest_out_name, dest_out_sort)) =
            self.state_var_mgr.output_state_vars.get(dest_idx).cloned()
        else {
            return false;
        };

        if dest_out_sort.datatype_name().is_some() {
            let mut field_exprs = Vec::with_capacity(cons.fields.len());
            for field_idx in 0..cons.fields.len() {
                if field_idx == map_field_idx {
                    field_exprs.push(new_data.clone());
                } else {
                    let Some(field_expr) = self.resolve_struct_field_expr(
                        struct_local,
                        field_idx,
                        inner_ty,
                        modified_locals,
                    ) else {
                        return false;
                    };
                    field_exprs.push(field_expr);
                }
            }
            let struct_expr =
                Expr::datatype_constructor(&dt.name, &cons.name, field_exprs, struct_sort.clone());
            let dest_var = Expr::var(&*dest_out_name, dest_out_sort);
            constraints.push(dest_var.eq(struct_expr));
            self.mark_state_var_modified(dest_idx);
            return true;
        }

        let mut flat_offset = 0;
        for (field_idx, field) in cons.fields.iter().enumerate() {
            let leaf_sorts = codegen_decl_flatten::collect_leaf_sorts(&field.sort, 0);
            for leaf_offset in 0..leaf_sorts.len() {
                let out_idx = dest_idx + flat_offset + leaf_offset;
                let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(out_idx).cloned()
                else {
                    return false;
                };
                let value = if field_idx == map_field_idx {
                    if leaf_offset != 0 {
                        return false;
                    }
                    new_data.clone()
                } else {
                    let Some(expr) = self.flattened_local_field_expr(
                        struct_local,
                        flat_offset + leaf_offset,
                        modified_locals,
                    ) else {
                        return false;
                    };
                    expr
                };
                let dest_var = Expr::var(&*out_name, out_sort.clone());
                if !self.push_coerced_eq_constraint(
                    constraints,
                    &dest_var,
                    value,
                    &out_sort,
                    dest_local,
                    "struct_map_store_method",
                ) {
                    return false;
                }
                self.mark_state_var_modified(out_idx);
            }
            flat_offset += leaf_sorts.len();
        }
        true
    }

    fn emit_store_aux_state(
        &mut self,
        dest_local: usize,
        struct_local: usize,
        map_field_idx: usize,
        key_expr: Expr,
        present_expr: Expr,
        constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        let present_sort = present_expr.sort().clone();
        let dest_present_var = self.ensure_store_dest_present_var(
            dest_local,
            struct_local,
            map_field_idx,
            &present_sort,
        );
        let pkey = self.coerce_key_for_present(&key_expr, &present_expr);
        let was_present = present_expr.clone().select(pkey.clone());
        let new_present = present_expr.store(pkey, Expr::bool_const(true));
        self.collection_present_set(
            &dest_present_var,
            new_present,
            &mut CallAccumulator::new(constraints, extra_dests),
        );

        if let Some(dest_len_var) = self.ensure_store_dest_len_var(dest_local, struct_local) {
            if let Some(src_len_var) = self.collections.len_state.get_len_var(struct_local).cloned()
            {
                let old_len = self.collection_current_len(&src_len_var);
                let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                let inc_len = old_len.clone().bvadd(one);
                let new_len = Expr::ite(was_present, old_len, inc_len);
                self.collection_len_set(
                    &dest_len_var,
                    new_len,
                    &mut CallAccumulator::new(constraints, extra_dests),
                );
            }
        }

        self.collections.register_embedded_map_aux(
            dest_local,
            map_field_idx,
            EmbeddedMapAuxState {
                len_var: self.collections.len_state.get_len_var(dest_local).cloned(),
                present_var: self.collections.len_state.get_present_var(dest_local).cloned(),
            },
        );
    }

    fn ensure_store_dest_present_var(
        &mut self,
        dest_local: usize,
        struct_local: usize,
        map_field_idx: usize,
        present_sort: &ay_bindings::Sort,
    ) -> Arc<str> {
        if let Some(state) = self.collections.get_embedded_map_aux(dest_local, map_field_idx)
            && let Some(present_var) = state.present_var.clone()
        {
            return present_var;
        }

        let src_present = self.collections.len_state.get_present_var(struct_local).cloned();
        let existing = self.collections.len_state.get_present_var(dest_local).cloned();
        let needs_fresh = existing.as_ref().is_none_or(|dst| Some(dst) == src_present.as_ref());
        let present_var = if needs_fresh {
            Arc::from(format!("hashmap_{}_present_{}", self.fn_name, dest_local))
        } else {
            existing.expect("checked existing present var")
        };

        self.collections.len_state.present_var_names.insert(dest_local, present_var.clone());
        let out_name = crate::codegen_ay::names::out_name(&present_var);
        self.push_late_collection_aux_var(present_var.clone(), &out_name, present_sort.clone());
        present_var
    }

    fn ensure_store_dest_len_var(
        &mut self,
        dest_local: usize,
        struct_local: usize,
    ) -> Option<Arc<str>> {
        let src_len = self.collections.len_state.get_len_var(struct_local).cloned();
        src_len.as_ref()?;

        let existing = self.collections.len_state.get_len_var(dest_local).cloned();
        let needs_fresh = existing.as_ref().is_none_or(|dst| Some(dst) == src_len.as_ref());
        let len_var = if needs_fresh {
            Arc::from(format!("hashmap_{}_len_{}", self.fn_name, dest_local))
        } else {
            existing.expect("checked existing len var")
        };

        self.collections.len_state.len_var_names.insert(dest_local, len_var.clone());
        let out_name = crate::codegen_ay::names::out_name(&len_var);
        self.push_late_collection_aux_var(len_var.clone(), &out_name, ptr_sort());
        Some(len_var)
    }
}
