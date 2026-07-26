// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Sequence-type (Array, Slice, Str) extraction from constant reference allocations.
//!
//! Extracted from codegen_decl_ref_const_extract.rs per #4147 (large-file decomposition).

use std::sync::Arc;

use ay_bindings::{Expr, Sort};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::types::{
    POINTER_WIDTH, bool_sort, int_ty_to_bitvec_width, ptr_sort, uint_ty_to_bitvec_width,
};

use crate::kani_middle::abi::LayoutOf;

use super::codegen_types::CodegenTypes;
use super::{ChcCtx, chc_fresh_name, declare_pending_var, push_pending_datatype_sort};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Extract a constant array (`[T; N]`) from a target allocation.
    ///
    /// Part of #2173: Handle constant array references for raw_eq.
    /// Reads element bytes from the allocation and builds an SMT array
    /// via nested store operations, matching translate_array_aggregate.
    pub(super) fn extract_array_from_const_ref(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        elem_ty: rustc_public::ty::Ty,
        const_len: &rustc_public::ty::TyConst,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let array_len = const_len.eval_target_usize().ok()? as usize;
        if array_len == 0 {
            let elem_sort = Self::translate_ty(elem_ty)?;
            let name = chc_fresh_name("__const_arr_empty");
            let arr_sort = Sort::array(ptr_sort(), elem_sort);
            // Part of #2317: declare the fresh symbolic array variable.
            return Some(declare_pending_var(name, arr_sort));
        }
        let (elem_sort, elem_byte_width) = match elem_ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => (bool_sort(), 1usize),
            TyKind::RigidTy(RigidTy::Uint(ut)) => {
                let bits = uint_ty_to_bitvec_width(ut);
                (Sort::bitvec(bits), (bits / 8) as usize)
            }
            TyKind::RigidTy(RigidTy::Int(it)) => {
                let bits = int_ty_to_bitvec_width(it);
                (Sort::bitvec(bits), (bits / 8) as usize)
            }
            // Part of #3607 D2: Char element type — Unicode scalar (u32, 4 bytes).
            TyKind::RigidTy(RigidTy::Char) => (Sort::bitvec(32), 4usize),
            // Part of #1739: Tuple/struct element types — read as Datatype,
            // flatten to BV. Same approach as static_init_from_alloc but for
            // const promoted references.
            _ => {
                return Self::extract_dt_array_from_const_ref(
                    target_alloc,
                    inner_ty,
                    elem_ty,
                    array_len,
                    memory_inits,
                    promoted_obj_id,
                );
            }
        };
        if target_alloc.bytes.len() < array_len * elem_byte_width {
            return None;
        }
        let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let name = chc_fresh_name("__const_arr");
        // Part of #2317: declare the fresh symbolic array variable.
        let mut result = declare_pending_var(name, array_sort);
        // Part of #2986: Get element type key for per-element memory_inits.
        // Part of #2267: Convert Cow to Arc<str> once; per-element clones
        // are O(1) refcount bumps instead of O(n) heap allocations.
        let elem_type_key: Arc<str> = Arc::from(&*Self::type_key_for_ty(elem_ty));
        for i in 0..array_len {
            let offset = i * elem_byte_width;
            // Part of #3527: Propagate None for uninitialized bytes.
            let elem_expr = if elem_sort.is_bool() {
                let byte_val: u8 = target_alloc.bytes.get(offset).copied()??;
                Expr::bool_const(byte_val != 0)
            } else {
                let bits = elem_sort.bitvec_width()?;
                let mut value: u128 = 0;
                for b in 0..elem_byte_width {
                    let byte_val: u8 = target_alloc.bytes.get(offset + b).copied()??;
                    value |= (byte_val as u128) << (b * 8);
                }
                Expr::bitvec_const(value, bits)
            };
            // Part of #2986: Emit per-element memory constraint so
            // try_raw_eq_array reads correct values from promoted constants.
            memory_inits.push((
                elem_type_key.clone(),
                elem_sort.clone(),
                elem_expr.clone(),
                promoted_obj_id,
                offset as u64,
            ));
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            result = result.store(idx, elem_expr);
        }
        // Part of #3497: Also seed the whole array value into the array-level
        // typed memory so that fat pointer dereferences through the 2D slice
        // memory see constrained values.
        let array_type_key: Arc<str> = Arc::from(&*Self::type_key_for_ty(inner_ty));
        let array_value_sort = Sort::array(ptr_sort(), elem_sort);
        memory_inits.push((
            array_type_key,
            array_value_sort,
            result.clone(),
            promoted_obj_id,
            0u64,
        ));
        Some(result)
    }

    /// Extract a Datatype-element array from a constant allocation.
    ///
    /// Handles the `_ =>` fallthrough in the array element type dispatch:
    /// tuple/struct element types are read as Datatype and flattened to BV.
    fn extract_dt_array_from_const_ref(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        elem_ty: rustc_public::ty::Ty,
        array_len: usize,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        use crate::codegen_ay::types::flatten_dt_array_element;
        use trust_mc_codegen_types::types::flatten_datatype_to_bitvec;

        let dt_sort = Self::translate_ty(elem_ty)?;
        if !dt_sort.is_datatype() {
            return None;
        }
        let dt = dt_sort.datatype_sort()?;
        if dt.constructors.len() != 1 {
            return None;
        }
        let ctor = dt.constructors.first()?;
        // Part of #3527: Use rustc's LayoutOf for element size instead
        // of manual C-like computation.
        let elem_layout = LayoutOf::new(elem_ty);
        let elem_byte_width = elem_layout.size_of()?;
        if elem_byte_width == 0 {
            return None;
        }
        let flattened_sort = flatten_dt_array_element(dt_sort.clone());
        let bv_width = flattened_sort.bitvec_width()?;
        // Physical BV width matches elem_sort_for_memory_array (byte-size * 8).
        // When padding exists (e.g. (u8, u32) -> 8 bytes -> BV64 vs BV40 flattened),
        // memory_inits must use the physical width so the entry rule's sort guard
        // does not silently drop them.
        let physical_bv_width = (elem_byte_width as u32).checked_mul(8)?;
        let physical_sort = Sort::bitvec(physical_bv_width);

        if target_alloc.bytes.len() < array_len * elem_byte_width {
            return None;
        }
        let array_sort = Sort::array(ptr_sort(), flattened_sort.clone());
        let name = chc_fresh_name("__const_arr");
        let mut result = declare_pending_var(name, array_sort);
        let elem_type_key: Arc<str> = Arc::from(&*Self::type_key_for_ty(elem_ty));
        for i in 0..array_len {
            let base = i * elem_byte_width;
            // Part of #3527: Read DT fields using rustc field offsets.
            let mut field_exprs = Vec::with_capacity(ctor.fields.len());
            for (field_idx, field) in ctor.fields.iter().enumerate() {
                let fld_offset = base + elem_layout.field_offset(field_idx)?;
                let field_expr = if field.sort.is_bool() {
                    let byte_val: u8 = target_alloc.bytes.get(fld_offset).copied()??;
                    Expr::bool_const(byte_val != 0)
                } else {
                    let bits = field.sort.bitvec_width()?;
                    let fw = (bits as usize / 8).max(1);
                    let mut value: u128 = 0;
                    for b in 0..fw {
                        let byte_val: u8 = target_alloc.bytes.get(fld_offset + b).copied()??;
                        value |= (byte_val as u128) << (b * 8);
                    }
                    Expr::bitvec_const(value, bits)
                };
                field_exprs.push(field_expr);
            }
            let dt_expr =
                Expr::datatype_constructor(&dt.name, &ctor.name, field_exprs, dt_sort.clone());
            let elem_expr = flatten_datatype_to_bitvec(&dt_expr, bv_width)?;
            // Part of #4066: The flattened BV embeds DT constructor/accessor
            // sub-expressions. Push the DT sort for late declaration so the
            // entry rule can reference them without undeclared sort errors.
            if matches!(dt_expr.sort().inner(), ay_bindings::SortInner::Datatype(_)) {
                push_pending_datatype_sort(dt_expr.sort().clone());
            }
            // Produce physical-width BV for memory_inits when padding exists,
            // so it matches the registered mem_<type> array sort (BV64 for (u8,u32)).
            let mem_expr = if physical_bv_width > bv_width {
                flatten_datatype_to_bitvec(&dt_expr, physical_bv_width)?
            } else {
                elem_expr.clone()
            };
            memory_inits.push((
                elem_type_key.clone(),
                physical_sort.clone(),
                mem_expr,
                promoted_obj_id,
                base as u64,
            ));
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            result = result.store(idx, elem_expr);
        }
        let array_type_key: Arc<str> = Arc::from(&*Self::type_key_for_ty(inner_ty));
        let array_value_sort = Sort::array(ptr_sort(), flattened_sort);
        memory_inits.push((
            array_type_key,
            array_value_sort,
            result.clone(),
            promoted_obj_id,
            0u64,
        ));
        Some(result)
    }

    /// Extract a constant slice (`[T]`) from a target allocation.
    ///
    /// Part of #3495: Handle constant slice references (`const &[u8]`).
    pub(super) fn extract_slice_from_const_ref(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        elem_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let (elem_sort, elem_byte_width) = match elem_ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => (bool_sort(), 1usize),
            TyKind::RigidTy(RigidTy::Uint(ut)) => {
                let bits = uint_ty_to_bitvec_width(ut);
                (Sort::bitvec(bits), (bits / 8) as usize)
            }
            TyKind::RigidTy(RigidTy::Int(it)) => {
                let bits = int_ty_to_bitvec_width(it);
                (Sort::bitvec(bits), (bits / 8) as usize)
            }
            _ => return None, // external enum: TyKind
        };
        if elem_byte_width == 0 {
            return None;
        }
        let array_len = target_alloc.bytes.len() / elem_byte_width;
        if array_len == 0 {
            return None;
        }
        let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let name = chc_fresh_name("__const_slice");
        let mut result = declare_pending_var(name, array_sort);
        let elem_type_key: Arc<str> = Arc::from(&*Self::type_key_for_ty(elem_ty));
        for i in 0..array_len {
            let offset = i * elem_byte_width;
            let elem_expr = if elem_sort.is_bool() {
                let byte_val: u8 = target_alloc.bytes.get(offset).copied()??;
                Expr::bool_const(byte_val != 0)
            } else {
                let bits = elem_sort.bitvec_width()?;
                let mut value: u128 = 0;
                for b in 0..elem_byte_width {
                    let byte_val: u8 = target_alloc.bytes.get(offset + b).copied()??;
                    value |= (byte_val as u128) << (b * 8);
                }
                Expr::bitvec_const(value, bits)
            };
            memory_inits.push((
                elem_type_key.clone(),
                elem_sort.clone(),
                elem_expr.clone(),
                promoted_obj_id,
                offset as u64,
            ));
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            result = result.store(idx, elem_expr);
        }
        let array_type_key: Arc<str> = Arc::from(&*Self::type_key_for_ty(inner_ty));
        let array_value_sort = Sort::array(ptr_sort(), elem_sort);
        memory_inits.push((
            array_type_key,
            array_value_sort,
            result.clone(),
            promoted_obj_id,
            0u64,
        ));
        Some(result)
    }

    /// Extract a constant `str` from a target allocation.
    ///
    /// Part of #3617: Handle promoted `&str` constant references.
    /// `&str` is a fat pointer to a UTF-8 byte sequence.
    ///
    /// Optimization: strings longer than 64 bytes are elided — the array variable
    /// is returned without per-byte memory_inits constraints. This eliminates
    /// hundreds of entry-rule conjuncts from panic message strings (e.g., 267-byte
    /// "unsafe precondition(s) violated: ..." from NonZeroU128) that are dead code
    /// for verification. The string length metadata (subslice_len) is recorded
    /// separately and remains correct. String content becomes unconstrained, which
    /// is sound because CHC proofs do not verify panic message content.
    pub(super) fn extract_str_from_const_ref(
        target_alloc: &rustc_public::ty::Allocation,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let elem_byte_width = 1usize;
        let elem_sort = Sort::bitvec(8);
        let array_len = target_alloc.bytes.len();
        if array_len == 0 {
            return None;
        }
        let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let name = chc_fresh_name("__const_str");
        // Elide per-byte encoding for long strings (panic messages, error descriptions).
        // The pointer and length metadata are still correct; only content is unconstrained.
        const MAX_CONST_STR_INIT_BYTES: usize = 64;
        if array_len > MAX_CONST_STR_INIT_BYTES {
            debug!(
                len = array_len,
                "CHC: eliding per-byte memory_inits for long const str (>{MAX_CONST_STR_INIT_BYTES} bytes)"
            );
            return Some(declare_pending_var(name, array_sort));
        }
        let mut result = declare_pending_var(name, array_sort);
        let elem_type_key: Arc<str> = Arc::from("u8");
        for i in 0..array_len {
            let byte_val: u8 = target_alloc.bytes.get(i).copied()??;
            let elem_expr = Expr::bitvec_const(byte_val as u128, 8);
            memory_inits.push((
                elem_type_key.clone(),
                elem_sort.clone(),
                elem_expr.clone(),
                promoted_obj_id,
                (i * elem_byte_width) as u64,
            ));
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            result = result.store(idx, elem_expr);
        }
        // Do not seed a typed `slice_u8` memory init with the whole byte array.
        // `slice_u8` is modeled as byte-addressed memory (`Array<BV64, BV8>`), so an
        // array-valued init here produces `select(mem_slice_u8, addr) = store(...)`
        // sort mismatches in the entry rule.
        Some(result)
    }
}
