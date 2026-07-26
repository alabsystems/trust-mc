// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Struct-level BTreeMap/HashMap accessor dispatch for `get().copied().unwrap_or()`.
//!
//! Part of #3348.

#[path = "codegen_call_struct_map_accessor_scan.rs"]
mod scan;
#[path = "codegen_call_struct_map_store.rs"]
mod store;

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, Operand};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use self::scan::{DefaultSource, MapAccessPattern, scan_map_get_pattern, scan_map_store_pattern};
use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::call::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::call::codegen_call_coerce::CallCoerce;
use crate::codegen_ay::chc::codegen_decl_flatten;
use crate::codegen_ay::chc::codegen_rules::CodegenRules;
use crate::codegen_ay::chc::codegen_stmt_projection::FieldProjection;
use crate::codegen_ay::chc::codegen_types::CodegenTypes;
use crate::codegen_ay::types::{bool_sort, int_sort};

/// Extension trait for BTreeMap accessor method dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchStructMapAccessor {
    fn try_dispatch_call_struct_map_accessor(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchStructMapAccessor for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_struct_map_accessor(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };
        let Some((callee_name, inner_ty, callee_body, struct_local, adt_name)) =
            self.resolve_struct_map_candidate(dcx)
        else {
            return false;
        };
        if self.destination_returns_self(dcx.destination.local, &adt_name) {
            let Some(pattern) = scan_map_store_pattern(&callee_body) else {
                debug!(
                    callee = %callee_name,
                    "struct_map_accessor: return-self method had no map store pattern"
                );
                return false;
            };
            debug!(
                callee = %callee_name,
                map_field = pattern.map_field_idx,
                key_local = pattern.key_local,
                value_local = pattern.value_local,
                "struct_map_accessor: store pattern found"
            );
            return self.emit_map_store_method(
                dcx,
                target,
                struct_local,
                &inner_ty,
                &pattern,
                &callee_name,
            );
        }

        let Some(pattern) = scan_map_get_pattern(&callee_body) else {
            debug!(callee = %callee_name, "struct_map_accessor: no map get pattern found in body");
            return false;
        };
        debug!(
            callee = %callee_name,
            map_field = pattern.map_field_idx,
            key_local = pattern.key_local,
            "struct_map_accessor: get pattern found"
        );
        self.emit_map_get_accessor(dcx, target, struct_local, &inner_ty, &pattern, &callee_name)
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn resolve_struct_map_candidate(
        &self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<(String, rustc_public::ty::Ty, Body, usize, String)> {
        let func_ty = dcx.func.ty(self.body.locals()).ok()?;
        let (fn_def, fn_substs) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
            _ => return None,
        };
        let callee_name = fn_def.trimmed_name();
        debug!(callee = %callee_name, "struct_map_accessor: checking callee");
        if matches!(callee_name.as_str(), "clone" | "Clone::clone" | "clone_from") {
            return None;
        }

        let arg0 = dcx.args.first()?;
        let arg0_ty = arg0.ty(self.body.locals()).ok()?;
        let inner_ty = match arg0_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
            _ => return None,
        };
        let (adt_def, adt_args) = match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) if !Self::type_is_hashmap(&inner_ty) => {
                (def, args)
            }
            _ => return None,
        };
        let fields = adt_def.variants().first()?.fields();
        if !fields.iter().any(|field| Self::type_is_hashmap(&field.ty_with_args(&adt_args))) {
            return None;
        }

        let struct_local = self.resolve_struct_local(arg0)?;

        debug!(callee = %callee_name, "struct_map_accessor: struct has map field, scanning body");
        let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
        let callee_body = instance.body()?;
        Some((callee_name, inner_ty, callee_body, struct_local, adt_def.trimmed_name()))
    }

    fn destination_returns_self(&self, dest_local: usize, adt_name: &str) -> bool {
        matches!(
            self.body.locals()[dest_local].ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == adt_name
        )
    }

    fn resolve_struct_local(&self, arg0: &Operand) -> Option<usize> {
        let ref_local = match arg0 {
            Operand::Copy(place) | Operand::Move(place) => place.local,
            _ => return None,
        };
        Some(self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local))
    }

    fn emit_map_get_accessor(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: &usize,
        struct_local: usize,
        inner_ty: &rustc_public::ty::Ty,
        pattern: &MapAccessPattern,
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
        let default_expr = match &pattern.default_source {
            DefaultSource::StructField(field_idx) => self.resolve_struct_field_expr(
                struct_local,
                *field_idx,
                inner_ty,
                dcx.modified_locals,
            ),
            DefaultSource::Parameter(param_local) => {
                self.resolve_callee_arg_for_map(dcx, *param_local)
            }
        };
        let default_expr = match default_expr {
            Some(e) => e,
            None => return false,
        };
        let present_expr = self.resolve_map_present_from_struct(struct_local, dcx.modified_locals);
        // Part of #3348 Direction 5: When `present` is missing, fall through to let
        // a sound over-approximation or explicit blocked path handle it. Raw
        // `data.select(key)` returns `hashmap_default` (a symbolic constant from
        // HashMap::new) instead of the user's fallback field, producing wrong results.
        let Some(present) = present_expr else {
            debug!(
                struct_local,
                callee = %callee_name,
                "struct_map_accessor: present array unavailable, falling through (#3348)"
            );
            return false;
        };
        let pkey = self.coerce_key_for_present(&key_expr, &present);
        let is_present = present.select(pkey);
        let value = data_expr.select(key_expr);
        let result = Expr::ite(is_present, value, default_expr);
        let dest_local: usize = dcx.destination.local;
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return false;
        };
        let eq = self.make_coerced_eq_constraint(
            &dest_var,
            result,
            dest_var.sort(),
            dest_local,
            "struct_map_accessor_get",
        );
        let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            eq,
        );

        debug!(
            callee = %callee_name,
            struct_local,
            map_field = pattern.map_field_idx,
            "CHC: struct BTreeMap accessor get dispatched (#3348)"
        );
        true
    }

    fn resolve_map_data_from_struct(
        &self,
        struct_local: usize,
        map_field_idx: usize,
        inner_ty: &rustc_public::ty::Ty,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let struct_sort = Self::translate_ty(*inner_ty)?;
        let dt = struct_sort.datatype_sort()?;
        let cons = dt.constructors.first()?;
        if map_field_idx >= cons.fields.len() {
            return None;
        }

        let state_idx = self.try_state_idx_for_local(struct_local)?;

        let (var_name, var_sort) = if modified_locals.contains(&struct_local) {
            self.state_var_mgr.output_state_vars.get(state_idx)?.clone()
        } else {
            self.state_var_mgr.state_vars.get(state_idx)?.clone()
        };
        if var_sort.datatype_name().is_some() {
            let struct_var = Expr::var(&*var_name, var_sort);
            let field_expr = Self::apply_field_selections(
                struct_var,
                &[FieldProjection { field_idx: map_field_idx, cons_idx: None, field_ty: None }],
            )?;
            if field_expr.sort().is_array() {
                return Some(field_expr);
            }
            return None;
        }
        let mut flat_offset = 0;
        for f in &cons.fields[..map_field_idx] {
            flat_offset += codegen_decl_flatten::collect_leaf_sorts(&f.sort, 0).len();
        }
        self.flattened_local_field_expr(struct_local, flat_offset, modified_locals)
    }

    fn resolve_struct_field_expr(
        &self,
        struct_local: usize,
        field_idx: usize,
        inner_ty: &rustc_public::ty::Ty,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let struct_sort = Self::translate_ty(*inner_ty)?;
        let dt = struct_sort.datatype_sort()?;
        let cons = dt.constructors.first()?;
        if field_idx >= cons.fields.len() {
            return None;
        }

        let state_idx = self.try_state_idx_for_local(struct_local)?;

        let (var_name, var_sort) = if modified_locals.contains(&struct_local) {
            self.state_var_mgr.output_state_vars.get(state_idx)?.clone()
        } else {
            self.state_var_mgr.state_vars.get(state_idx)?.clone()
        };
        if var_sort.datatype_name().is_some() {
            let struct_var = Expr::var(&*var_name, var_sort);
            return Self::apply_field_selections(
                struct_var,
                &[FieldProjection { field_idx, cons_idx: None, field_ty: None }],
            );
        }
        let mut flat_offset = 0;
        for f in &cons.fields[..field_idx] {
            flat_offset += codegen_decl_flatten::collect_leaf_sorts(&f.sort, 0).len();
        }
        self.flattened_local_field_expr(struct_local, flat_offset, modified_locals)
    }

    fn resolve_callee_arg_for_map(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        callee_local: usize,
    ) -> Option<Expr> {
        let caller_arg_idx = callee_local.checked_sub(1)?;
        let arg = dcx.args.get(caller_arg_idx)?;
        self.translate_operand_with_modified(arg, dcx.modified_locals)
    }

    fn resolve_map_present_from_struct(
        &self,
        struct_local: usize,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let present_var_name = self.collections.len_state.get_present_var(struct_local)?;
        let present_sort = self
            .state_var_index_by_name(present_var_name)
            .and_then(|idx| self.state_var_mgr.state_vars.get(idx))
            .map(|(_, s)| s.clone())
            .unwrap_or_else(|| ay_bindings::Sort::array(int_sort(), bool_sort()));
        if self.collections.len_state.modified_present_vars.contains(present_var_name) {
            let out_name = format!("{}_out", present_var_name);
            Some(Expr::var(out_name, present_sort))
        } else if modified_locals.contains(&struct_local) {
            if let Some(idx) = self.state_var_index_by_name(present_var_name) {
                if let Some((out_name, _)) = self.state_var_mgr.output_state_vars.get(idx) {
                    return Some(Expr::var(&**out_name, present_sort));
                }
            }
            Some(Expr::var(&**present_var_name, present_sort))
        } else {
            Some(Expr::var(&**present_var_name, present_sort))
        }
    }

    fn coerce_key_for_present(&self, key: &Expr, present: &Expr) -> Expr {
        let present_sort = present.sort();
        if let Some(arr) = present_sort.array_sort() {
            let target_sort = &arr.index_sort;
            if *key.sort() != *target_sort {
                if target_sort.is_int() {
                    return key.clone().bv2int();
                }
            }
        }
        key.clone()
    }
}
