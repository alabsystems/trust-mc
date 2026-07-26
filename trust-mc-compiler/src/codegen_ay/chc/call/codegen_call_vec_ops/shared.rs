// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared Vec helper API consumed by other Vec/iterator call modules.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

use crate::codegen_ay::names;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension};

use super::super::ChcCtx;

pub(in crate::codegen_ay::chc) struct ProjectedVecState {
    pub(in crate::codegen_ay::chc) ptr: Expr,
    pub(in crate::codegen_ay::chc) len: Expr,
    pub(in crate::codegen_ay::chc) cap: Expr,
    pub(in crate::codegen_ay::chc) data: Expr,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn constrain_projected_vec_fields_for_call(
        &mut self,
        local_idx: usize,
        fields: ProjectedVecState,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) -> bool {
        self.invalidate_vec_adapter_source_data(local_idx);
        let emitted = self.constrain_flattened_fields_for_call(
            local_idx,
            &[Some(fields.ptr), Some(fields.len), Some(fields.cap), Some(fields.data)],
            extra_constraints,
        );
        if emitted {
            extra_dests.push(local_idx);
        }
        emitted
    }

    pub(in crate::codegen_ay::chc) fn invalidate_vec_adapter_source_data(
        &mut self,
        local_idx: usize,
    ) {
        self.collections.adapter_source_data.remove(&local_idx);
    }

    pub(in crate::codegen_ay::chc) fn vec_elem_size_bytes_from_ty(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<u64> {
        let ty = self.resolve_body_ty(ty);
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                self.vec_elem_size_bytes_from_ty(self.resolve_body_ty(inner))
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Vec" => {
                let elem_ty = match args.0.first() {
                    Some(GenericArgKind::Type(elem_ty)) => self.resolve_body_ty(*elem_ty),
                    _ => return None,
                };
                self.get_type_size(elem_ty).map(|size| size as u64)
            }
            _ => None,
        }
    }

    /// Vec growth from `cap == 0` must stop reusing the constructor's dangling
    /// provenance pointer. Once the Vec becomes non-empty, later pointer checks
    /// should see a heap-backed object with live metadata.
    pub(in crate::codegen_ay::chc) fn allocate_vec_backing_on_zero_cap_growth(
        &mut self,
        old_ptr: Expr,
        old_cap: &Expr,
        new_cap: &Expr,
        vec_ty: Option<rustc_public::ty::Ty>,
        extra_constraints: &mut Vec<Expr>,
    ) -> Expr {
        if !self.extra_pointer_checks || self.int_lift {
            return old_ptr;
        }

        let elem_size_bytes =
            vec_ty.and_then(|ty| self.vec_elem_size_bytes_from_ty(ty)).unwrap_or(1);
        if elem_size_bytes == 0 {
            return old_ptr;
        }

        let Some(obj_id) = self.heap_state.next_heap_alloc_id() else {
            return old_ptr;
        };

        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let cap_nonzero = new_cap.clone().bvugt(zero.clone());
        let cap_was_zero = old_cap.clone().eq(zero);
        let obj_id_expr = Expr::bitvec_const(obj_id as i128, 32);
        let fresh_ptr = obj_id_expr.clone().concat(Expr::bitvec_const(0, 32));
        let ptr_invalid = self
            .split_pointer(&old_ptr)
            .map(|(old_obj_id, _)| {
                super::super::codegen_expr_heap::obj_valid_in().select(old_obj_id).not()
            })
            .unwrap_or_else(|| Expr::bool_const(false));
        let needs_backing = cap_nonzero.and(cap_was_zero.or(ptr_invalid));

        let cap_32 = self
            .coerce_to_heap_bv32(new_cap.clone())
            .unwrap_or_else(|| Expr::bitvec_const(0u64, 32));
        let size_expr = if elem_size_bytes > 1 {
            cap_32.bvmul(Expr::bitvec_const(elem_size_bytes as i128, 32))
        } else {
            cap_32
        };
        self.record_known_heap_alloc_size_expr(obj_id, &size_expr);

        let obj_valid_in = super::super::codegen_expr_heap::obj_valid_in();
        let obj_size_in = super::super::codegen_expr_heap::obj_size_in();
        extra_constraints.push(super::super::codegen_expr_heap::obj_valid_out().eq(Expr::ite(
            needs_backing.clone(),
            obj_valid_in.clone().store(obj_id_expr.clone(), Expr::bool_const(true)),
            obj_valid_in,
        )));
        extra_constraints.push(super::super::codegen_expr_heap::obj_size_out().eq(Expr::ite(
            needs_backing.clone(),
            obj_size_in.clone().store(obj_id_expr, size_expr),
            obj_size_in,
        )));
        self.mark_heap_metadata_modified();

        Expr::ite(needs_backing, fresh_ptr, old_ptr)
    }

    pub(in crate::codegen_ay::chc) fn extract_projected_vec_fields(
        &self,
        coll_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<(Expr, Expr, Expr, Expr)> {
        let ptr =
            self.flattened_local_field_expr(coll_local, vec_layout::IDX_PTR, modified_locals)?;
        let len =
            self.flattened_local_field_expr(coll_local, vec_layout::IDX_LEN, modified_locals)?;
        let cap =
            self.flattened_local_field_expr(coll_local, vec_layout::IDX_CAP, modified_locals)?;
        let data =
            self.flattened_local_field_expr(coll_local, vec_layout::IDX_DATA, modified_locals)?;
        Some((ptr, len, cap, data))
    }

    pub(in crate::codegen_ay::chc) fn build_vec_datatype_eq(
        dt_name: &str,
        new_fields: Vec<Expr>,
        out_name: &str,
        out_sort: &Sort,
    ) -> Expr {
        let ctor_name = names::cons_name(dt_name);
        let new_vec = Expr::datatype_constructor(dt_name, ctor_name, new_fields, out_sort.clone());
        let dest_var = Expr::var(out_name, out_sort.clone());
        dest_var.eq(new_vec)
    }

    pub(in crate::codegen_ay::chc) fn emit_cap_ge_len(
        cap: Expr,
        len: Expr,
        extra_constraints: &mut Vec<Expr>,
    ) {
        extra_constraints.push(cap.bvuge(len));
    }
}

/// Coerce an element expression to match the expected element sort of an Array
/// sort. Handles Bool↔BV and BV width mismatches that arise when
/// `translate_operand` produces a different sort than `translate_ty` used
/// during state variable declaration (Part of #3496 Bug D).
pub(crate) fn coerce_array_element(elem: Expr, data_sort: &Sort) -> Expr {
    use crate::codegen_ay::types::coerce_bitvec_width_safe;

    let expected_elem_sort = match data_sort.array_sort() {
        Some(arr) => arr.element_sort.clone(),
        None => return elem,
    };
    let elem_sort = elem.sort().clone();
    if elem_sort == expected_elem_sort {
        return elem;
    }
    // Bool → BV: ite(elem, 1, 0)
    if elem_sort.is_bool() && expected_elem_sort.is_bitvec() {
        let bits = expected_elem_sort.bitvec_width().unwrap_or(8);
        return Expr::ite(elem, Expr::bitvec_const(1u64, bits), Expr::bitvec_const(0u64, bits));
    }
    // BV → Bool: elem != 0
    if elem_sort.is_bitvec() && expected_elem_sort.is_bool() {
        let w = elem_sort.bitvec_width().unwrap_or(8);
        return elem.ne(Expr::bitvec_const(0u64, w));
    }
    // BV → BV width mismatch
    if elem_sort.is_bitvec() && expected_elem_sort.is_bitvec() {
        if let Some(target_width) = expected_elem_sort.bitvec_width() {
            return coerce_bitvec_width_safe(elem, target_width, SignExtension::ZeroExtend);
        }
    }
    // Datatype → BV: flatten struct/enum to bitvec (Part of dterm#6841).
    // When flatten_dt_array_element flattens a Datatype sort (e.g., Run_u8 → BV40)
    // at Vec declaration, store sites must coerce element expressions to match.
    if elem_sort.is_datatype() && expected_elem_sort.is_bitvec() {
        if let Some(target_width) = expected_elem_sort.bitvec_width() {
            if let Some(flattened) =
                trust_mc_codegen_types::types::flatten_datatype_to_bitvec(&elem, target_width)
            {
                return flattened;
            }
        }
    }
    // BV → Datatype: unflatten bitvec back to struct/enum (reverse of above).
    if elem_sort.is_bitvec() && expected_elem_sort.is_datatype() {
        if let Some(unflattened) =
            trust_mc_codegen_types::types::unflatten_bitvec_to_datatype(&elem, &expected_elem_sort)
        {
            return unflattened;
        }
    }
    // Part of #4212: Defense-in-depth — if no coercion matched but sorts still
    // differ, substitute a fresh unconstrained symbolic of the correct sort.
    // Without this, the ay-bindings .store() panics on sort mismatch because
    // its internal coerce only handles Vec/String DT, not general BV width gaps.
    // This is sound over-approximation (same pattern as coerce_store_value).
    if elem_sort != expected_elem_sort {
        tracing::warn!(
            expected_sort = ?expected_elem_sort,
            actual_sort = ?elem_sort,
            "CHC: coerce_array_element fallback — substituted fresh symbolic (Part of #4212)"
        );
        return crate::codegen_ay::chc::declare_pending_var(
            crate::codegen_ay::chc::chc_fresh_name("__arr_elem_coerce"),
            expected_elem_sort,
        );
    }
    elem
}
