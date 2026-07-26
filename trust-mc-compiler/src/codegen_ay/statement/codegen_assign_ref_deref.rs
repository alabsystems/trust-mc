// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Reference deref assignment and indexed write propagation.
//!
//! Extracted from `codegen_assign_ref.rs` — Part of #4206.

use super::{IntoOption, StatementCodegen};
use ay_bindings::Expr;
use rustc_public::mir::{Mutability, Place, ProjectionElem, Rvalue};
use rustc_public::ty::{RigidTy, TyKind};
use std::sync::Arc;
use tracing::{debug, trace};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Handle reference deref assignment: `*ref = value` for mutable references (#484).
    ///
    /// When LHS is `*r` where `r: &mut T`, assign to the pointee tracked in `ref_pointees`.
    /// Returns `true` if handled.
    pub(super) fn try_codegen_assign_ref_deref(&mut self, lhs: &Place, rhs: &Rvalue) -> bool {
        let Some(ProjectionElem::Deref) = lhs.projection.first() else {
            return false;
        };
        // Part of #2267: construct Place directly instead of clone + clear.
        let ref_place = Place { local: lhs.local, projection: vec![] };
        let Some(ref_ty) = ref_place.ty(self.body.locals()).into_option() else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Mut)) = ref_ty.kind() else {
            return false;
        };
        // Only handle whole-struct assignment (no further projections after Deref)
        if lhs.projection.len() != 1 {
            return false;
        }

        let ref_base =
            crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), ref_place.local);

        let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()).cloned() else {
            return false;
        };
        debug!(
            "codegen_assign: reference deref whole struct, ref={}, pointee={}",
            ref_base, pointee_base
        );
        let Some(rhs_expr) = self.codegen_rvalue(rhs) else {
            return false;
        };

        // Create new SSA version of the pointee
        let pointee_ssa = self.ssa_name_from_base(&pointee_base, true);
        let pointee_var = self.ctx.declare_var(&pointee_ssa, rhs_expr.sort().clone());

        // Assert SSA definition with ite semantics (#2081)
        self.assert_ssa_def(pointee_var.clone(), rhs_expr, &pointee_base);

        // Update environment
        self.env_update(Arc::clone(&pointee_base), pointee_var.clone());
        debug!("codegen_assign: reference deref assigned {} = rhs", pointee_ssa);

        // #1210: Propagate writes to array elements back to the array.
        // Part of #2267: .to_owned() is required here because try_propagate takes
        // &mut self while fn_name borrows from self.ctx.
        let fn_name = self.ctx.current_fn_name().to_owned();
        self.try_propagate_indexed_ref_write_to_array(&fn_name, &pointee_base, pointee_var.clone());

        // Part of #3041: Propagate writes to enum variant payloads back to the parent enum.
        self.try_propagate_deref_write_to_parent_datatype(&pointee_base, &pointee_var, lhs);

        true
    }

    /// Propagate indexed reference writes back to the parent array.
    ///
    /// When pointee is an indexed element (e.g., `fn::local_1_idx_by_3`),
    /// update the array itself using store operation so subsequent reads
    /// via `arr[i]` see the updated value (#1210).
    fn try_propagate_indexed_ref_write_to_array(
        &mut self,
        fn_name: &str,
        pointee_base: &str,
        pointee_var: Expr,
    ) {
        let Some(idx_pos) = pointee_base.find("_idx_by_") else {
            // Part of #3392: fallback for stub-created pointees that don't use
            // the `_idx_by_` naming convention (e.g., `slice_index_pointee_N`).
            self.try_propagate_stub_indexed_ref_write(pointee_base, pointee_var);
            return;
        };
        let array_base = &pointee_base[..idx_pos];
        let Some(idx_local_str) = pointee_base[idx_pos + 8..].split('_').next() else {
            return;
        };
        let Ok(idx_local) = idx_local_str.parse::<usize>() else {
            return;
        };

        let Some(arr_expr) = self.env_lookup(array_base).cloned() else {
            return;
        };
        if !arr_expr.sort().is_array() {
            return;
        }

        let idx_base = crate::codegen_ay::names::local_name(fn_name, idx_local);
        let Some(idx_expr) = self.env_lookup(&idx_base).cloned() else {
            return;
        };

        // Part of #2894: Vec/String coercion via shared helper (was inline #1341).
        let store_val = if let Some(coerced) =
            crate::codegen_ay::store_coercion::coerce_vec_string_store_value(
                arr_expr.sort(),
                &pointee_var,
            ) {
            trace!("codegen_assign: coerced value for Vec/String indexed ref write");
            coerced
        } else {
            pointee_var
        };

        // Part of #2970: BMC sort coercion beyond Vec/String (BV width, Bool↔BV, etc.).
        // Part of #3034: derive signedness from array element MIR type.
        // Part of #2267: eliminate format! allocation — use chained strip_prefix.
        let signed = {
            array_base
                .strip_prefix(fn_name)
                .and_then(|s| s.strip_prefix("::local_"))
                .and_then(|idx_str| idx_str.parse::<usize>().ok())
                .and_then(|local_idx| {
                    let local_ty = self.body.locals()[local_idx].ty;
                    match local_ty.kind() {
                        TyKind::RigidTy(RigidTy::Array(elem_ty, _))
                        | TyKind::RigidTy(RigidTy::Slice(elem_ty)) => {
                            crate::codegen_ay::shared::ty_signedness_shallow(elem_ty)
                        }
                        _ => crate::codegen_ay::shared::ty_signedness_shallow(local_ty),
                    }
                })
                .unwrap_or(false)
        };
        let store_val = if let Some(coerced) =
            crate::codegen_ay::store_coercion::coerce_store_value_bmc(
                arr_expr.sort(),
                &store_val,
                signed,
            ) {
            debug!("codegen_assign: BMC-coerced value for indexed ref write (Part of #2970)");
            coerced
        } else {
            store_val
        };

        // Part of #2970: Last-resort fresh symbolic if sorts still mismatch.
        let store_val = if let Some(arr) = arr_expr.sort().array_sort() {
            if *store_val.sort() != arr.element_sort {
                let sym_name = crate::codegen_ay::store_coercion::bmc_store_fallback_name();
                debug!(
                    array_base = %array_base,
                    store_sort = ?store_val.sort(),
                    elem_sort = ?arr.element_sort,
                    "codegen_assign: fresh symbolic for indexed ref write sort mismatch (Part of #2970)"
                );
                self.ctx.declare_var(&sym_name, arr.element_sort.clone())
            } else {
                store_val
            }
        } else {
            store_val
        };

        let new_arr = arr_expr.store(idx_expr, store_val);
        let new_arr_ssa = self.ssa_name_from_base(array_base, true);
        let new_arr_var = self.ctx.declare_var(&new_arr_ssa, new_arr.sort().clone());
        self.assert_ssa_def(new_arr_var.clone(), new_arr, array_base);
        self.env_update(array_base, new_arr_var);
        debug!("codegen_assign: propagated indexed ref write to array {}", new_arr_ssa);
    }

    /// Fallback propagation for stub-created indexed references. Part of #3392.
    ///
    /// When `try_propagate_indexed_ref_write_to_array` can't find `_idx_by_` in
    /// the pointee name, check `stub_indexed_refs` for a mapping from the stub
    /// path. Handles both bare arrays and Vec/datatype `fld_data` containers.
    fn try_propagate_stub_indexed_ref_write(&mut self, pointee_base: &str, pointee_var: Expr) {
        let Some((container_base, idx_expr)) = self.stub_indexed_refs.get(pointee_base).cloned()
        else {
            return;
        };
        let Some(container_expr) = self.env_lookup(&container_base).cloned() else {
            return;
        };

        if container_expr.sort().is_array() {
            // Case 1: bare array — store directly.
            let store_val = self.coerce_store_value_for_array(&container_expr, pointee_var);
            let new_arr = container_expr.store(idx_expr, store_val);
            let new_arr_ssa = self.ssa_name_from_base(&container_base, true);
            let new_arr_var = self.ctx.declare_var(&new_arr_ssa, new_arr.sort().clone());
            self.assert_ssa_def(new_arr_var.clone(), new_arr, &container_base);
            self.env_update(std::sync::Arc::clone(&container_base), new_arr_var);
            debug!(
                "codegen_assign: propagated stub indexed ref write to bare array {} (Part of #3392)",
                new_arr_ssa
            );
        } else if let Some(dt) = container_expr.sort().datatype_sort() {
            // Case 2: Vec/datatype with a backing array field. Vec/Slice use
            // "fld_data"; ArrayVec/inline buffers use "fld_buf" (the fld_-prefixed
            // Rust field name). Part of the PROVED-green ArrayVec store modelling.
            let dt_name = &*dt.name;
            let Some(cons) = dt.constructors.first() else {
                return;
            };
            let data_field_idx =
                cons.fields.iter().position(|f| matches!(&*f.name, "fld_data" | "fld_buf"));
            let Some(data_field_idx) = data_field_idx else {
                return;
            };
            let data_field_name = &*cons.fields[data_field_idx].name;
            let data_sort = cons.fields[data_field_idx].sort.clone();
            if !data_sort.is_array() {
                return;
            }
            let data_expr =
                container_expr.clone().field_select(dt_name, data_field_name, data_sort);
            let store_val = self.coerce_store_value_for_array(&data_expr, pointee_var);
            let new_data = data_expr.store(idx_expr, store_val);

            // Reconstruct the datatype with updated fld_data.
            let cons_name = &*cons.name;
            let mut args = Vec::with_capacity(cons.fields.len());
            for (idx, field) in cons.fields.iter().enumerate() {
                if idx == data_field_idx {
                    args.push(new_data.clone());
                } else {
                    args.push(container_expr.clone().field_select(
                        dt_name,
                        &*field.name,
                        field.sort.clone(),
                    ));
                }
            }
            let new_container =
                Expr::datatype_constructor(dt_name, cons_name, args, container_expr.sort().clone());
            let new_ssa = self.ssa_name_from_base(&container_base, true);
            let new_var = self.ctx.declare_var(&new_ssa, new_container.sort().clone());
            self.assert_ssa_def(new_var.clone(), new_container, &container_base);
            self.env_update(std::sync::Arc::clone(&container_base), new_var);
            debug!(
                "codegen_assign: propagated stub indexed ref write to datatype {} {} (Part of #3392)",
                data_field_name, new_ssa
            );
        }
    }

    /// Coerce a store value for array element sort compatibility. Part of #3392.
    fn coerce_store_value_for_array(&mut self, arr_expr: &Expr, val: Expr) -> Expr {
        // Try Vec/String coercion first.
        if let Some(coerced) =
            crate::codegen_ay::store_coercion::coerce_vec_string_store_value(arr_expr.sort(), &val)
        {
            return coerced;
        }
        // BMC sort coercion (BV width, Bool↔BV, etc.).
        let coerced = crate::codegen_ay::store_coercion::coerce_store_value_bmc(
            arr_expr.sort(),
            &val,
            false, // default unsigned for stub path
        );
        let val = coerced.unwrap_or(val);
        // Last-resort fresh symbolic for sort mismatch.
        if let Some(arr) = arr_expr.sort().array_sort() {
            if *val.sort() != arr.element_sort {
                let sym_name = crate::codegen_ay::store_coercion::bmc_store_fallback_name();
                return self.ctx.declare_var(&sym_name, arr.element_sort.clone());
            }
        }
        val
    }
}
