// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Static variable initialization helpers for CHC encoding.
//!
//! Handles reading initial values from allocations, including the
//! flattened Datatype array element case where field ordering must
//! be corrected (MSB-first concat vs LE byte reading).
//!
//! Split from codegen_decl_static.rs per file size limit.
//! Part of #3496 Phase 5.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::alloc::{AllocId, GlobalAlloc};
use std::sync::Arc;
use tracing::debug;

use super::ChcCtx;
use super::codegen_types::CodegenTypes;
use super::codegen_types_adt_sort::CodegenTypesAdtSort;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn canonical_static_seed_alloc(
        &self,
        target_alloc_id: AllocId,
    ) -> Option<(AllocId, rustc_public::ty::Allocation)> {
        use rustc_public::CrateDef;
        use rustc_public::ty::{RigidTy, TyKind};

        let mut current_alloc_id = target_alloc_id;
        for _ in 0..8 {
            match GlobalAlloc::from(current_alloc_id) {
                GlobalAlloc::Static(target_def) => {
                    let target_def_id =
                        rustc_public::rustc_internal::internal(self.tcx, target_def.def_id());
                    // A foreign (`extern "C"`) static has no initializer body;
                    // `eval_initializer()` would span_bug/panic (uncatchable by
                    // `.ok()`). Stop following the ref chain (nondet referent).
                    if self.tcx.is_foreign_item(target_def_id) {
                        return None;
                    }
                    let target_alloc = target_def.eval_initializer().ok()?;
                    let should_follow_nested_ref = !self.tcx.is_mutable_static(target_def_id)
                        && matches!(
                            target_def.ty().kind(),
                            TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
                        )
                        && !target_alloc.provenance.ptrs.is_empty();
                    if should_follow_nested_ref {
                        let next_alloc_id = target_alloc.provenance.ptrs[0].1.0;
                        if next_alloc_id == current_alloc_id {
                            return Some((current_alloc_id, target_alloc));
                        }
                        current_alloc_id = next_alloc_id;
                        continue;
                    }
                    return Some((current_alloc_id, target_alloc));
                }
                GlobalAlloc::Memory(alloc) => return Some((current_alloc_id, alloc)),
                _ => return None,
            }
        }

        None
    }

    pub(in crate::codegen_ay::chc) fn push_static_memory_init_entry(
        &mut self,
        rust_ty: rustc_public::ty::Ty,
        value_expr: Expr,
        addr_expr: Expr,
    ) {
        // Part of #3661: resolve generic params for consistent type keys.
        let type_key: Arc<str> = Arc::from(&*self.type_key_for_body_ty(rust_ty));
        let elem_sort = self.elem_sort_for_memory_array(rust_ty);
        let stored_value = if value_expr.sort() == &elem_sort {
            Some(value_expr)
        } else if value_expr.sort().is_datatype() {
            let bv_width = elem_sort.bitvec_width();
            let flat = bv_width
                .and_then(|w| crate::codegen_ay::types::flatten_datatype_to_bitvec(&value_expr, w));
            if flat.is_some() {
                self.declare_datatype_sort_if_needed(value_expr.sort());
            } // #4066
            flat
        } else {
            None
        };

        if let Some(stored_value) = stored_value {
            self.ref_resolution.static_memory_inits.push((
                type_key,
                elem_sort,
                stored_value,
                addr_expr,
            ));
        }
    }

    pub(in crate::codegen_ay::chc) fn static_addr_with_offset(
        addr_expr: Expr,
        offset: u64,
    ) -> Expr {
        if offset == 0 {
            addr_expr
        } else {
            addr_expr
                .bvadd(Expr::bitvec_const(offset as i128, crate::codegen_ay::types::POINTER_WIDTH))
        }
    }

    pub(in crate::codegen_ay::chc) fn register_static_memory_init_entries(
        &mut self,
        rust_ty: rustc_public::ty::Ty,
        value_expr: Expr,
        addr_expr: Expr,
    ) {
        use rustc_public::ty::{RigidTy, TyKind};

        // P2-S1: in a contract CHECK harness, interior-mutable (UnsafeCell-
        // covered) static memory must stay unconstrained — the contract has
        // to hold for arbitrary interior state. The ENTIRE memory region of
        // an interior-mut static is havocked (no per-field precision on the
        // raw-memory path): deref translation can collapse a field
        // projection through `UnsafeCell::get` to the static's BASE address,
        // so a pinned Freeze-field byte could be read back as the CELL's
        // value — a fail-open (observed on static_interior_mut.rs, where the
        // `mut_field.get()` read resolved to the offset-0 byte). Field
        // precision lives only on the state-var pin
        // (`collect_contract_partial_static_pins`), whose datatype accessors
        // are projection-exact. The fail direction here is always MORE havoc.
        if self.contract_static_havoc && self.ty_has_interior_mut(rust_ty) {
            return; // full havoc of this memory region
        }
        self.push_static_memory_init_entry(rust_ty, value_expr.clone(), addr_expr.clone());

        // Part of #4196: Decompose array-typed statics into per-element memory inits.
        // For `[T; N]`, the whole-array value sort is `Array(BV64, elem_sort)` but
        // the typed memory array's element sort is per-element (e.g., BV32 for char).
        // Without decomposition, `push_static_memory_init_entry` silently drops the
        // whole-array value due to sort mismatch, leaving memory unconstrained.
        if let TyKind::RigidTy(RigidTy::Array(elem_ty, len_const)) = rust_ty.kind() {
            if let Ok(array_len) = len_const.eval_target_usize() {
                if let Some(elem_size) = self.get_type_size(elem_ty) {
                    if elem_size > 0 && value_expr.sort().is_array() {
                        let idx_width = value_expr
                            .sort()
                            .array_sort()
                            .and_then(|a| a.index_sort.bitvec_width())
                            .unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);
                        for i in 0..array_len {
                            let idx = Expr::bitvec_const(i as u128, idx_width);
                            let elem_expr = value_expr.clone().select(idx);
                            let elem_addr = Self::static_addr_with_offset(
                                addr_expr.clone(),
                                i * elem_size as u64,
                            );
                            self.register_static_memory_init_entries(elem_ty, elem_expr, elem_addr);
                        }
                        debug!(
                            array_len,
                            elem_size,
                            "register_static_memory_init: decomposed array into per-element inits (#4196)"
                        );
                    }
                }
            }
            return;
        }

        let TyKind::RigidTy(RigidTy::Adt(def, args)) = rust_ty.kind() else {
            return;
        };
        if def.variants().len() != 1 {
            return;
        }

        let Some(dt) = value_expr.sort().datatype_sort() else {
            return;
        };
        let Some(ctor) = dt.constructors.first() else {
            return;
        };
        let variant = &def.variants()[0];

        for (field_idx, field_def) in variant.fields().iter().enumerate() {
            let Some(offset) = self.get_field_offset(rust_ty, field_idx) else {
                continue;
            };
            let Some(field) = ctor.fields.get(field_idx) else {
                continue;
            };
            let field_ty =
                <ChcCtx as CodegenTypesAdtSort>::resolve_generic_ty(field_def.ty(), &args)
                    .unwrap_or_else(|| field_def.ty());
            let field_expr =
                value_expr.clone().field_select(&dt.name, &field.name, field.sort.clone());
            let field_addr = Self::static_addr_with_offset(addr_expr.clone(), offset);
            self.register_static_memory_init_entries(field_ty, field_expr, field_addr);
        }
    }

    // sort_default_expr moved to codegen_decl_static_alloc.rs (Part of #4196).

    /// Compute initial value for a static, handling flattened Datatype array elements.
    /// Detects BV-flattened arrays and reads fields individually to fix byte ordering.
    /// Part of #3496 Phase 5.
    pub(in crate::codegen_ay::chc) fn static_init_from_alloc(
        &mut self,
        alloc: &rustc_public::ty::Allocation,
        sort: &Sort,
        rust_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        use rustc_public::ty::{RigidTy, TyKind};

        // Check if this is an Array whose element sort was flattened from a Datatype.
        if let Some(arr) = sort.array_sort() {
            if let Some(bv_width) = arr.element_sort.bitvec_width() {
                // Get the Rust element type.
                let elem_ty = match rust_ty.kind() {
                    TyKind::RigidTy(RigidTy::Array(et, _))
                    | TyKind::RigidTy(RigidTy::Slice(et)) => Some(et),
                    _ => None,
                };

                if let Some(elem_ty) = elem_ty {
                    // Get the unflattened element sort.
                    if let Some(dt_sort) = Self::translate_ty(elem_ty) {
                        if dt_sort.is_datatype() {
                            debug!(
                                ?bv_width,
                                "static_init: detected flattened DT array, reading with unflatten"
                            );
                            return Self::read_array_with_flatten(
                                &alloc.bytes,
                                0,
                                sort,
                                &dt_sort,
                                bv_width,
                            );
                        }
                    }
                }
            }

            if let TyKind::RigidTy(RigidTy::Array(elem_ty, len)) = rust_ty.kind()
                && matches!(elem_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)))
            {
                let array_len = len.eval_target_usize().ok()? as usize;
                return self.read_array_with_pointer_elements_from_allocation(
                    alloc, 0, sort, elem_ty, array_len,
                );
            }
        }

        // Fall back to standard reading for non-array or non-flattened statics.
        Self::scalar_from_alloc(alloc, sort)
    }

    pub(in crate::codegen_ay::chc) fn static_seed_metadata_for_value(
        &mut self,
        value_ty: rustc_public::ty::Ty,
        value_expr: Expr,
        backing_alloc: Option<&rustc_public::ty::Allocation>,
    ) -> Option<(Expr, Option<Expr>)> {
        use rustc_public::ty::{RigidTy, TyKind};

        if !value_expr.sort().is_array() {
            return None;
        }

        match value_ty.kind() {
            TyKind::RigidTy(RigidTy::Array(..)) => Some((value_expr, None)),
            TyKind::RigidTy(RigidTy::Slice(elem_ty)) => {
                let elem_bytes = self.get_type_size(elem_ty)?;
                if elem_bytes == 0 {
                    return None;
                }
                let len = backing_alloc?.bytes.len() / elem_bytes;
                let len_expr =
                    Expr::bitvec_const(len as u128, crate::codegen_ay::types::POINTER_WIDTH);
                Some((value_expr, Some(len_expr)))
            }
            TyKind::RigidTy(RigidTy::Str) => {
                let len_expr = Expr::bitvec_const(
                    backing_alloc?.bytes.len() as u128,
                    crate::codegen_ay::types::POINTER_WIDTH,
                );
                Some((value_expr, Some(len_expr)))
            }
            _ => None,
        }
    }

    pub(in crate::codegen_ay::chc) fn resolve_pointer_static_seed_metadata(
        &mut self,
        target_alloc_id: AllocId,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<(Expr, Option<Expr>)> {
        let (_resolved_alloc_id, target_alloc_data) =
            self.canonical_static_seed_alloc(target_alloc_id)?;

        let pointee_sort = Self::translate_ty(pointee_ty)?;
        let referent_value =
            self.static_init_from_alloc(&target_alloc_data, &pointee_sort, pointee_ty)?;
        self.static_seed_metadata_for_value(pointee_ty, referent_value, Some(&target_alloc_data))
    }

    /// Read an array from allocation bytes, reading elements as Datatypes then
    /// flattening to BV for correct field ordering.
    ///
    /// The CHC concat convention puts field 0 at HIGH bits (`concat(fld_0, fld_1)`),
    /// but LE byte reading puts field 0 at LOW bits. This function reads each
    /// element as a Datatype (which reads fields individually at correct offsets)
    /// and then flattens to the target BV width using `flatten_datatype_to_bitvec`.
    ///
    /// Part of #3496 Phase 5: correct byte ordering for packed struct array elements.
    fn read_array_with_flatten(
        bytes: &[Option<u8>],
        offset: usize,
        array_sort: &Sort,
        dt_elem_sort: &Sort,
        bv_width: u32,
    ) -> Option<Expr> {
        use trust_mc_codegen_types::types::flatten_datatype_to_bitvec;

        let arr = array_sort.array_sort()?;
        let dt_byte_width = Self::sort_byte_width(dt_elem_sort)?;
        if dt_byte_width == 0 {
            return None;
        }

        let remaining = bytes.len().saturating_sub(offset);
        let array_len = remaining / dt_byte_width;
        if array_len == 0 {
            return None;
        }

        let default_elem = Self::sort_default_expr(&arr.element_sort)?;
        let mut result = Expr::const_array(arr.index_sort.clone(), default_elem);
        let idx_width =
            arr.index_sort.bitvec_width().unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);

        for i in 0..array_len {
            let elem_offset = offset + i * dt_byte_width;
            // Read as Datatype (correct field ordering via recursive decomposition).
            let dt_expr = Self::read_composite_from_bytes(bytes, elem_offset, dt_elem_sort)?;
            // Flatten Datatype to BV using MSB-first concat convention.
            let bv_expr = flatten_datatype_to_bitvec(&dt_expr, bv_width)?;
            let idx = Expr::bitvec_const(i as u128, idx_width);
            result = result.store(idx, bv_expr);
        }
        Some(result)
    }

    // read_array_with_pointer_elements_from_allocation, read_pointer_like_from_allocation,
    // seed_static_str_backing_memory, alloc_dst_pointer_fallback, resolve_static_target_init_expr,
    // resolve_pointer_static_init moved to codegen_decl_static_alloc.rs (Part of #4196).
}
