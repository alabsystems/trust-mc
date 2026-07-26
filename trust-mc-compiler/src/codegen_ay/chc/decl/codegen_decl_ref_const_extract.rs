// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Type-dispatch extraction logic for constant reference scalar values.
//!
//! Contains `extract_scalar_from_const_ref` (the main type-dispatch function),
//! `extract_nested_str_from_const_ref`, and `extract_nested_ref_from_const_ref`.
//!
//! Complex arms (Array/Slice/Str, ADT) are delegated to
//! `codegen_decl_ref_const_extract_seq` and `codegen_decl_ref_const_extract_adt`.
//!
//! Extracted from codegen_decl_ref_const_values.rs per #4147 (large-file decomposition).

use std::sync::Arc;

use ay_bindings::{Expr, Sort};
use rustc_public::ty::{RigidTy, TyKind};

use crate::codegen_ay::types::{
    POINTER_WIDTH, bool_sort, int_ty_to_bitvec_width, ptr_sort, uint_ty_to_bitvec_width,
};

use crate::kani_middle::abi::LayoutOf;

use super::codegen_decl_flatten::byte_size_to_bv_width;
use super::codegen_types::CodegenTypes;
use super::{ChcCtx, chc_fresh_name, declare_pending_var, push_pending_datatype_sort};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Extracts a scalar AY expression from a constant reference.
    ///
    /// Part of #1919: For `const &0u8`, the allocation contains a pointer with
    /// provenance. We follow it to the target allocation and read the scalar value,
    /// returning it as a AY expression with the correct sort.
    ///
    /// Part of #2958: Also populates `memory_inits` with byte-level memory
    /// array initialization data for the promoted constant at address 0x1000.
    pub(super) fn extract_scalar_from_const_ref(
        kind: rustc_public::ty::ConstantKind,
        inner_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let target_alloc = Self::resolve_const_target_alloc(&kind)?;

        match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => {
                Self::extract_bool_scalar(&target_alloc, inner_ty, memory_inits, promoted_obj_id)
            }
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => Self::extract_uint_scalar(
                &target_alloc,
                inner_ty,
                uint_ty,
                memory_inits,
                promoted_obj_id,
            ),
            TyKind::RigidTy(RigidTy::Int(int_ty)) => Self::extract_int_scalar(
                &target_alloc,
                inner_ty,
                int_ty,
                memory_inits,
                promoted_obj_id,
            ),
            TyKind::RigidTy(RigidTy::Char) => {
                Self::extract_char_scalar(&target_alloc, inner_ty, memory_inits, promoted_obj_id)
            }
            TyKind::RigidTy(RigidTy::Array(elem_ty, const_len)) => {
                Self::extract_array_from_const_ref(
                    &target_alloc,
                    inner_ty,
                    elem_ty,
                    &const_len,
                    memory_inits,
                    promoted_obj_id,
                )
            }
            TyKind::RigidTy(RigidTy::Slice(elem_ty)) => Self::extract_slice_from_const_ref(
                &target_alloc,
                inner_ty,
                elem_ty,
                memory_inits,
                promoted_obj_id,
            ),
            TyKind::RigidTy(RigidTy::Str) => {
                Self::extract_str_from_const_ref(&target_alloc, memory_inits, promoted_obj_id)
            }
            TyKind::RigidTy(RigidTy::Tuple(_)) => Self::extract_tuple_from_const_ref(
                &target_alloc,
                inner_ty,
                memory_inits,
                promoted_obj_id,
            ),
            TyKind::RigidTy(RigidTy::Adt(def, args)) => Self::extract_adt_from_const_ref(
                &target_alloc,
                inner_ty,
                def,
                &args,
                memory_inits,
                promoted_obj_id,
            ),
            _ => None, // external enum: TyKind
        }
    }

    /// Extract a Bool scalar from a const allocation.
    fn extract_bool_scalar(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let expr = Expr::bool_const(target_alloc.read_bool().ok()?);
        let type_key = Self::type_key_for_ty(inner_ty);
        memory_inits.push((
            Arc::from(&*type_key),
            bool_sort(),
            expr.clone(),
            promoted_obj_id,
            0u64,
        ));
        Some(expr)
    }

    /// Extract a Uint scalar from a const allocation.
    fn extract_uint_scalar(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        uint_ty: rustc_public::ty::UintTy,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let width = uint_ty_to_bitvec_width(uint_ty);
        let value = target_alloc.read_uint().ok()?;
        let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
        let expr = Expr::bitvec_const(masked, width);
        let type_key = Self::type_key_for_ty(inner_ty);
        memory_inits.push((
            Arc::from(&*type_key),
            Sort::bitvec(width),
            expr.clone(),
            promoted_obj_id,
            0u64,
        ));
        Some(expr)
    }

    /// Extract an Int scalar from a const allocation.
    fn extract_int_scalar(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        int_ty: rustc_public::ty::IntTy,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let width = int_ty_to_bitvec_width(int_ty);
        let value = target_alloc.read_int().ok()?;
        let masked =
            if width >= 128 { value as u128 } else { (value as u128) & ((1u128 << width) - 1) };
        let expr = Expr::bitvec_const(masked, width);
        let type_key = Self::type_key_for_ty(inner_ty);
        memory_inits.push((
            Arc::from(&*type_key),
            Sort::bitvec(width),
            expr.clone(),
            promoted_obj_id,
            0u64,
        ));
        Some(expr)
    }

    /// Extract a Char scalar (u32) from a const allocation.
    fn extract_char_scalar(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let value = target_alloc.read_uint().ok()?;
        let expr = Expr::bitvec_const(value & 0xFFFFFFFF, 32);
        let type_key = Self::type_key_for_ty(inner_ty);
        memory_inits.push((
            Arc::from(&*type_key),
            Sort::bitvec(32),
            expr.clone(),
            promoted_obj_id,
            0u64,
        ));
        Some(expr)
    }

    /// Extract a promoted tuple constant from a target allocation.
    ///
    /// Part of #3786: `assert!(t == (0, true))` passes the RHS as a promoted
    /// `&(u8, bool)`. Without decoding the tuple allocation into a datatype
    /// expression, fn_inline sees only a raw pointer and cannot project
    /// `(*other).0/.1` precisely, causing false CTREX.
    fn extract_tuple_from_const_ref(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        let sort = Self::translate_ty(inner_ty)?;
        let expr = Self::read_composite_from_allocation(target_alloc, 0, &sort)?;

        // Seed flattened tuple value for statement-level field-ref lowering.
        Self::seed_flattened_memory_init(
            target_alloc.bytes.len(),
            &expr,
            inner_ty,
            memory_inits,
            promoted_obj_id,
            0u64,
        );

        let TyKind::RigidTy(RigidTy::Tuple(field_tys)) = inner_ty.kind() else {
            return Some(expr);
        };
        Self::seed_tuple_field_memory_inits(
            target_alloc,
            inner_ty,
            &field_tys,
            memory_inits,
            promoted_obj_id,
        );
        Some(expr)
    }

    /// Seed per-field memory_inits for a tuple's fields.
    fn seed_tuple_field_memory_inits(
        target_alloc: &rustc_public::ty::Allocation,
        inner_ty: rustc_public::ty::Ty,
        field_tys: &[rustc_public::ty::Ty],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) {
        let tuple_layout = LayoutOf::new(inner_ty);
        for (field_idx, field_ty) in field_tys.iter().enumerate() {
            let Some(field_sort) = Self::translate_ty(*field_ty) else { return };
            let Some(field_offset) = tuple_layout.field_offset(field_idx) else { return };
            let Some(field_expr) =
                Self::read_composite_from_allocation(target_alloc, field_offset, &field_sort)
            else {
                return;
            };
            let (mem_sort, mem_expr) =
                match Self::flatten_field_for_memory_init(&field_expr, &field_sort, *field_ty) {
                    Some(pair) => pair,
                    None => continue,
                };
            let field_type_key = Self::type_key_for_ty(*field_ty);
            memory_inits.push((
                Arc::from(&*field_type_key),
                mem_sort,
                mem_expr,
                promoted_obj_id,
                field_offset as u64,
            ));
        }
    }

    /// Flatten a datatype field expr to BV for memory init, or pass through scalars.
    ///
    /// Returns None if the field is a datatype that can't be flattened (skip it).
    pub(super) fn flatten_field_for_memory_init(
        field_expr: &Expr,
        field_sort: &Sort,
        field_ty: rustc_public::ty::Ty,
    ) -> Option<(Sort, Expr)> {
        if field_sort.is_datatype() {
            let fw = LayoutOf::new(field_ty).size_of()?;
            if fw == 0 || fw > 16 {
                return None;
            }
            let flat = crate::codegen_ay::types::flatten_datatype_to_bitvec(
                field_expr,
                byte_size_to_bv_width(fw),
            )?;
            Some((Sort::bitvec(byte_size_to_bv_width(fw)), flat))
        } else {
            Some((field_sort.clone(), field_expr.clone()))
        }
    }

    /// Seed a flattened BV memory init for a composite value, if small enough.
    pub(super) fn seed_flattened_memory_init(
        byte_width: usize,
        expr: &Expr,
        ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
        offset: u64,
    ) {
        if byte_width > 0
            && byte_width <= 16
            && let Some(flat_expr) = crate::codegen_ay::types::flatten_datatype_to_bitvec(
                expr,
                byte_size_to_bv_width(byte_width),
            )
        {
            // The flattened BV expression embeds DT constructor/accessor
            // sub-expressions (e.g. fld_value(MemoryInitializationState_mk(...))).
            // Push the original DT sort for late declaration so the entry rule
            // can reference these sub-expressions without hitting an undeclared
            // sort error.
            if matches!(expr.sort().inner(), ay_bindings::SortInner::Datatype(_)) {
                push_pending_datatype_sort(expr.sort().clone());
            }
            let type_key = Self::type_key_for_ty(ty);
            memory_inits.push((
                Arc::from(&*type_key),
                Sort::bitvec(byte_size_to_bv_width(byte_width)),
                flat_expr,
                promoted_obj_id,
                offset,
            ));
        }
    }

    /// Extract string bytes from a nested `&&str` promoted constant.
    ///
    /// Part of #3607: `PartialEq<&str>` often receives a local initialized from
    /// a promoted `&&str` constant. This follows two levels of provenance to reach
    /// the backing UTF-8 bytes.
    pub(super) fn extract_nested_str_from_const_ref(
        kind: rustc_public::ty::ConstantKind,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<(Expr, usize)> {
        use rustc_public::mir::alloc::GlobalAlloc;

        let outer_alloc = Self::unwrap_const_alloc(&kind)?;
        let inner_alloc_id = outer_alloc.provenance.ptrs.first()?.1.0;
        let GlobalAlloc::Memory(inner_alloc) = GlobalAlloc::from(inner_alloc_id) else {
            return None;
        };
        let bytes_alloc_id = inner_alloc.provenance.ptrs.first()?.1.0;
        let GlobalAlloc::Memory(bytes_alloc) = GlobalAlloc::from(bytes_alloc_id) else {
            return None;
        };

        let ptr_bytes = (POINTER_WIDTH / 8) as usize;
        if inner_alloc.bytes.len() < ptr_bytes * 2 {
            return None;
        }
        let mut len_arr = [0u8; 8];
        for (i, opt_byte) in inner_alloc.bytes[ptr_bytes..ptr_bytes * 2].iter().enumerate() {
            len_arr[i] = (*opt_byte)?;
        }
        let len = u64::from_le_bytes(len_arr) as usize;
        if len == 0 || bytes_alloc.bytes.len() < len {
            return None;
        }

        let elem_sort = Sort::bitvec(8);
        let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let name = chc_fresh_name("__const_str");
        let mut result = declare_pending_var(name, array_sort);
        let elem_type_key: Arc<str> = Arc::from("u8");
        for i in 0..len {
            let byte_val: u8 = bytes_alloc.bytes.get(i).copied()??;
            let elem_expr = Expr::bitvec_const(byte_val as u128, 8);
            memory_inits.push((
                elem_type_key.clone(),
                elem_sort.clone(),
                elem_expr.clone(),
                promoted_obj_id,
                i as u64,
            ));
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            result = result.store(idx, elem_expr);
        }
        Some((result, len))
    }

    /// Peel through one reference level in a promoted constant to extract the
    /// inner referent's scalar/array value.
    ///
    /// Part of #3632: `assert_eq!` wraps the RHS array literal in `&&[u8; N]`.
    pub(super) fn extract_nested_ref_from_const_ref(
        kind: rustc_public::ty::ConstantKind,
        nested_inner_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        promoted_obj_id: u32,
    ) -> Option<Expr> {
        use rustc_public::mir::alloc::GlobalAlloc;
        use rustc_public::ty::ConstantKind;

        let outer_alloc = Self::unwrap_const_alloc(&kind)?;
        let inner_alloc_id = outer_alloc.provenance.ptrs.first()?.1.0;
        let GlobalAlloc::Memory(inner_alloc) = GlobalAlloc::from(inner_alloc_id) else {
            return None;
        };
        let synthetic_kind = ConstantKind::Allocated(inner_alloc);
        Self::extract_scalar_from_const_ref(
            synthetic_kind,
            nested_inner_ty,
            memory_inits,
            promoted_obj_id,
        )
    }

    /// Unwrap a ConstantKind to its raw Allocation (without provenance resolution).
    fn unwrap_const_alloc(
        kind: &rustc_public::ty::ConstantKind,
    ) -> Option<rustc_public::ty::Allocation> {
        use rustc_public::ty::{ConstantKind, TyConstKind};
        match kind {
            ConstantKind::Allocated(alloc) => Some(alloc.clone()),
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_value_ty, alloc) => Some(alloc.clone()),
                _ => None,
            },
            _ => None,
        }
    }
}
