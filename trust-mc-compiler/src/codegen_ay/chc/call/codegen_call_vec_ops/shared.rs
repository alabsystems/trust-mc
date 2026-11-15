// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared Vec helper API consumed by other Vec/iterator call modules.

use crate::codegen_ay::chc::codegen_ctx::{Havoc, sound_havoc};
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

    /// The size in bytes of the element of the Vec `ty` names, from the
    /// element's own layout (`shared::vec_capacity::vec_elem_layout_size`):
    /// the size every capacity rule reads. Not [`Self::vec_elem_size_bytes_from_ty`],
    /// the heap model's size, which strips `RefCell`, `Mutex` and the other
    /// heap-transparent wrappers first.
    pub(in crate::codegen_ay::chc) fn vec_capacity_elem_size(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<u64> {
        crate::codegen_ay::shared::vec_capacity::vec_elem_layout_size(self.resolve_body_ty(ty))
    }

    /// The capacity a reservation for `required` elements in all leaves a
    /// Vec of type `vec_ty` (a `Vec`, `RawVec` or `String`, or a reference
    /// to one) whose capacity was `old_cap`: `RawVec`'s amortized or exact
    /// growth (`shared::vec_capacity`). A zero-sized element keeps
    /// `max(cap, required)`. When the element's size is unknown the grown
    /// capacity is a fresh value of at least `required`, an identified sound
    /// havoc, so a counterexample that reads it is not certified.
    pub(in crate::codegen_ay::chc) fn vec_reserved_cap(
        &mut self,
        vec_ty: Option<rustc_public::ty::Ty>,
        old_cap: &Expr,
        required: &Expr,
        growth: crate::codegen_ay::shared::vec_capacity::VecGrowth,
        constraints: &mut Vec<Expr>,
    ) -> Expr {
        use crate::codegen_ay::shared::vec_capacity::reserved_capacity;
        let elem_size = vec_ty.and_then(|ty| self.vec_capacity_elem_size(ty));
        match elem_size {
            Some(size) => reserved_capacity(old_cap, required, size, growth).unwrap_or_else(|| {
                Expr::ite(
                    old_cap.clone().bvult(required.clone()),
                    required.clone(),
                    old_cap.clone(),
                )
            }),
            None => self.vec_fresh_grown_cap(old_cap, required, constraints),
        }
    }

    /// A grown capacity the model does not compute: `old_cap` when it covers
    /// `required`, else a fresh value of at least `required`, an identified
    /// sound havoc (`vec_grown_capacity_unmodelled`).
    pub(in crate::codegen_ay::chc) fn vec_fresh_grown_cap(
        &mut self,
        old_cap: &Expr,
        required: &Expr,
        constraints: &mut Vec<Expr>,
    ) -> Expr {
        use crate::codegen_ay::chc::codegen_ctx::{Havoc, sound_havoc};
        let name = super::super::codegen_ctx::globals::chc_fresh_name("vec_grown_cap");
        let fresh = Havoc::mint(
            self,
            sound_havoc::VEC_GROWN_CAPACITY_UNMODELLED,
            name,
            Sort::bitvec(POINTER_WIDTH),
        );
        constraints.push(fresh.clone().bvuge(required.clone()));
        Expr::ite(old_cap.clone().bvult(required.clone()), fresh, old_cap.clone())
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

    /// A Vec local's (ptr, len, cap, data) fields as the call reads them: the
    /// projected scalar fields, else the datatype state var's.
    pub(in crate::codegen_ay::chc) fn read_vec_fields(
        &self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<(Expr, Expr, Expr, Expr)> {
        if self.collections.projection_locals.get(&local).copied()
            == Some(super::super::codegen_ctx::types::CollectionProjectionKind::Vec)
        {
            return self.extract_projected_vec_fields(local, modified_locals);
        }
        let (_, fields) = self.vec_datatype_state(local, modified_locals)?;
        let super::super::codegen_call_vec::ChcVecFields { ptr, len, cap, data, .. } = fields;
        Some((ptr, len, cap, data))
    }

    /// The datatype state var a Vec local lives in, with its fields as the
    /// call reads them.
    fn vec_datatype_state(
        &self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<(usize, super::super::codegen_call_vec::ChcVecFields)> {
        let idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&local).copied())?;
        let (name, sort) = if modified_locals.contains(&local) {
            self.state_var_mgr.output_state_vars.get(idx)
        } else {
            self.state_var_mgr.state_vars.get(idx)
        }
        .cloned()?;
        sort.datatype_name()?;
        let fields =
            super::super::codegen_call_vec::ChcVecFields::extract(Expr::var(&*name, sort))?;
        Some((idx, fields))
    }

    /// Write a Vec local's fields for a call: `f` maps its current
    /// (ptr, len, cap, data) to the new ones, in whichever representation the
    /// local has (the projected scalar fields or the datatype state var).
    /// `false` when neither could be read or written; nothing is written then.
    pub(in crate::codegen_ay::chc) fn write_vec_fields(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
        f: impl FnOnce(Expr, Expr, Expr, Expr) -> (Expr, Expr, Expr, Expr),
        acc: &mut super::super::call_accumulator::CallAccumulator<'_>,
    ) -> bool {
        if self.collections.projection_locals.get(&local).copied()
            == Some(super::super::codegen_ctx::types::CollectionProjectionKind::Vec)
        {
            let Some((ptr, len, cap, data)) =
                self.extract_projected_vec_fields(local, modified_locals)
            else {
                return false;
            };
            let (ptr, len, cap, data) = f(ptr, len, cap, data);
            return self.constrain_projected_vec_fields_for_call(
                local,
                ProjectedVecState { ptr, len, cap, data },
                acc.constraints,
                acc.dests,
            );
        }
        let Some((idx, fields)) = self.vec_datatype_state(local, modified_locals) else {
            return false;
        };
        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(idx).cloned()
        else {
            return false;
        };
        let super::super::codegen_call_vec::ChcVecFields { vec_sort, ptr, len, cap, data } = fields;
        let Some(dt_name) = vec_sort.datatype_name() else { return false };
        let (ptr, len, cap, data) = f(ptr, len, cap, data);
        acc.constraints.push(Self::build_vec_datatype_eq(
            dt_name,
            vec![ptr, len, cap, data],
            &out_name,
            &out_sort,
        ));
        self.mark_state_var_modified(idx);
        true
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
pub(in crate::codegen_ay::chc) fn coerce_array_element(
    ctx: &mut super::super::ChcCtx<'_, '_>,
    elem: Expr,
    data_sort: &Sort,
) -> Expr {
    let expected_elem_sort = match data_sort.array_sort() {
        Some(arr) => arr.element_sort.clone(),
        None => return elem,
    };
    let coerced = coerce_array_element_exact(elem, data_sort);
    // Part of #4212: Defense-in-depth — if no coercion matched but sorts still
    // differ, substitute a fresh value of the correct sort (the ay-bindings
    // `.store()` panics on a sort mismatch). The value is one the coercion does
    // not compute: a booked havoc (Rule E).
    if *coerced.sort() != expected_elem_sort {
        tracing::warn!(
            expected_sort = ?expected_elem_sort,
            actual_sort = ?coerced.sort(),
            "CHC: coerce_array_element fallback — substituted fresh symbolic (Part of #4212)"
        );
        return Havoc::mint(
            ctx,
            sound_havoc::UNTRACKED_SORT_MISMATCH_VALUE,
            crate::codegen_ay::chc::chc_fresh_name("__arr_elem_coerce"),
            expected_elem_sort,
        );
    }
    coerced
}

/// The exact coercions of [`coerce_array_element`] (Bool↔BV, BV widths,
/// datatype↔bitvector flattening), with no fallback: an element no coercion
/// fits is returned unchanged, so a caller with its own fallback (the BMC
/// lane's booked `bmc_store_fallback`) decides.
pub(crate) fn coerce_array_element_exact(elem: Expr, data_sort: &Sort) -> Expr {
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
    elem
}
