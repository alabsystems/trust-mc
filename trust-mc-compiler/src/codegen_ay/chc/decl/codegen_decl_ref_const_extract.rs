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

use crate::codegen_ay::chc::codegen_ctx::ExactVar;
use std::sync::Arc;

use ay_bindings::{Expr, Sort};
use rustc_public::ty::{RigidTy, TyKind};

use crate::codegen_ay::types::{
    POINTER_WIDTH, bool_sort, int_ty_to_bitvec_width, ptr_sort, uint_ty_to_bitvec_width,
};

use crate::kani_middle::abi::LayoutOf;

use super::codegen_decl_flatten::byte_size_to_bv_width;
use super::codegen_types::CodegenTypes;
use super::global_objects::InitSite;
use super::{ChcCtx, chc_fresh_name, push_pending_datatype_sort};
use crate::codegen_ay::shared::const_pointer::{self, ConstRead};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Decodes a pointee WINDOW (`const_pointer::fixed_pointee`) as a value of
    /// `inner_ty`, pushing its typed-memory seeds at `site` (the window's own
    /// object and offset).
    ///
    /// Part of #1919 / #2958. The window starts at the pointer's offset in its
    /// target and is exactly the pointee's extent, so every reader below
    /// decodes from the window's byte 0 — which is the pointee's first byte,
    /// not the target's. Decoding the whole target from its byte 0 read the
    /// WRONG element: for `E = &[1u32, 2, 3][1]`, `*E == 1` PROVED.
    pub(in crate::codegen_ay::chc) fn decode_window(
        &self,
        window: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let target_alloc = window;
        match inner_ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => {
                Self::extract_bool_scalar(target_alloc, inner_ty, memory_inits, site)
            }
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => {
                Self::extract_uint_scalar(target_alloc, inner_ty, uint_ty, memory_inits, site)
            }
            TyKind::RigidTy(RigidTy::Int(int_ty)) => {
                Self::extract_int_scalar(target_alloc, inner_ty, int_ty, memory_inits, site)
            }
            TyKind::RigidTy(RigidTy::Char) => {
                Self::extract_char_scalar(target_alloc, inner_ty, memory_inits, site)
            }
            TyKind::RigidTy(RigidTy::Float(float_ty)) => {
                Self::extract_float_scalar(target_alloc, inner_ty, float_ty, memory_inits, site)
            }
            TyKind::RigidTy(RigidTy::Array(elem_ty, const_len)) => self
                .extract_array_from_const_ref(
                    target_alloc,
                    inner_ty,
                    elem_ty,
                    &const_len,
                    memory_inits,
                    site,
                ),
            TyKind::RigidTy(RigidTy::Slice(elem_ty)) => self.extract_slice_from_const_ref(
                target_alloc,
                inner_ty,
                elem_ty,
                memory_inits,
                site,
            ),
            TyKind::RigidTy(RigidTy::Str) => {
                self.extract_str_from_const_ref(target_alloc, memory_inits, site)
            }
            TyKind::RigidTy(RigidTy::Tuple(_)) => {
                self.extract_tuple_from_const_ref(target_alloc, inner_ty, memory_inits, site)
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => self.extract_adt_from_const_ref(
                target_alloc,
                inner_ty,
                def,
                &args,
                memory_inits,
                site,
            ),
            // A pointer stored in the window (`&&T`, an array of references):
            // its value is the pointer — the relocation at the window's byte 0,
            // placed at its own target's object plus its offset — never the
            // relocation's offset bytes, and never the allocation's FIRST
            // relocation.
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => self
                .extract_pointer_from_const_ref(
                    target_alloc,
                    inner_ty,
                    pointee,
                    memory_inits,
                    site,
                ),
            // A function pointer stored in the window (`&SF` for a `fn`
            // static): the identity of the function its relocation names, the
            // value a reification of that instance mints. A slot that holds no
            // function relocation declines.
            TyKind::RigidTy(RigidTy::FnPtr(_)) => {
                self.extract_fn_ptr_from_const_ref(target_alloc, inner_ty, memory_inits, site)
            }
            _ => None, // external enum: TyKind
        }
    }

    /// The function pointer stored at the window's byte 0: its function's
    /// identity (`const_ptr_address`), seeded at the fn-pointer type's key.
    fn extract_fn_ptr_from_const_ref(
        &self,
        window: &dyn ConstRead,
        fn_ptr_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let ptr = window.stored_pointer(0)?;
        if !matches!(ptr.kind(), const_pointer::ConstTarget::Function(_)) {
            return None;
        }
        let expr = self.const_ptr_address(&ptr)?.into_expr();
        let type_key = Self::type_key_for_ty(fn_ptr_ty);
        memory_inits.push((
            Arc::from(&*type_key),
            ptr_sort(),
            expr.clone(),
            site.obj_id,
            site.at(0),
        ));
        Some(expr)
    }

    /// The pointer value stored at the window's byte 0 (thin: its address;
    /// fat: `concat(len, address)`), seeded at the pointer type's key.
    fn extract_pointer_from_const_ref(
        &self,
        window: &dyn ConstRead,
        ptr_ty: rustc_public::ty::Ty,
        pointee: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let r = const_pointer::const_ref(window, 0, pointee)?;
        let addr = self.const_ptr_address(&r.ptr)?.into_expr();
        if let Some(key) = r.ptr.key() {
            self.note_object_read_deferred(key, pointee);
        }
        let expr = if Self::ref_pointee_is_fat_bv128(pointee) {
            Expr::bitvec_const(u128::from(r.metadata?), POINTER_WIDTH).concat(addr)
        } else {
            if !matches!(pointee.layout().ok().map(|l| l.shape().is_sized()), Some(true)) {
                return None;
            }
            addr
        };
        let sort = expr.sort().clone();
        let type_key = Self::type_key_for_ty(ptr_ty);
        memory_inits.push((Arc::from(&*type_key), sort, expr.clone(), site.obj_id, site.at(0)));
        Some(expr)
    }

    /// Extract a Bool scalar from a const allocation.
    fn extract_bool_scalar(
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let expr = Expr::bool_const(target_alloc.read_bool_at(0)?);
        let type_key = Self::type_key_for_ty(inner_ty);
        memory_inits.push((
            Arc::from(&*type_key),
            bool_sort(),
            expr.clone(),
            site.obj_id,
            site.at(0),
        ));
        Some(expr)
    }

    /// Extract a Uint scalar from a const allocation.
    fn extract_uint_scalar(
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        uint_ty: rustc_public::ty::UintTy,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let width = uint_ty_to_bitvec_width(uint_ty);
        let value = target_alloc.read_uint_at(0, target_alloc.len())?;
        let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
        let expr = Expr::bitvec_const(masked, width);
        let type_key = Self::type_key_for_ty(inner_ty);
        memory_inits.push((
            Arc::from(&*type_key),
            Sort::bitvec(width),
            expr.clone(),
            site.obj_id,
            site.at(0),
        ));
        Some(expr)
    }

    /// Extract an Int scalar from a const allocation.
    fn extract_int_scalar(
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        int_ty: rustc_public::ty::IntTy,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let width = int_ty_to_bitvec_width(int_ty);
        let value = target_alloc.read_int_at(0, target_alloc.len())?;
        let masked =
            if width >= 128 { value as u128 } else { (value as u128) & ((1u128 << width) - 1) };
        let expr = Expr::bitvec_const(masked, width);
        let type_key = Self::type_key_for_ty(inner_ty);
        memory_inits.push((
            Arc::from(&*type_key),
            Sort::bitvec(width),
            expr.clone(),
            site.obj_id,
            site.at(0),
        ));
        Some(expr)
    }

    /// Extract a float scalar from a const allocation as its IEEE-754 bit
    /// pattern (the CHC lane's float sort is the bitvector of the float's
    /// width, `translate_ty`).
    ///
    /// A promoted `&-0.0f32` used to fall through to `None`: its object id and
    /// address were still registered, so a deref read a FREE memory cell and a
    /// FREE `obj_size` for it, with nothing recorded — a false memory-safety
    /// counterexample certified Genuine (T1 review, 2026-09-24,
    /// `read_f32(&-0.0f32)`).
    fn extract_float_scalar(
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        float_ty: rustc_public::ty::FloatTy,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let width = crate::codegen_ay::types::float_ty_to_bitvec_width(float_ty);
        if target_alloc.len() * 8 != width as usize {
            return None;
        }
        let value = target_alloc.read_uint_at(0, target_alloc.len())?;
        let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
        let expr = Expr::bitvec_const(masked, width);
        let type_key = Self::type_key_for_ty(inner_ty);
        memory_inits.push((
            Arc::from(&*type_key),
            Sort::bitvec(width),
            expr.clone(),
            site.obj_id,
            site.at(0),
        ));
        Some(expr)
    }

    /// Extract a Char scalar (u32) from a const allocation.
    fn extract_char_scalar(
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let value = target_alloc.read_uint_at(0, 4)?;
        // An invalid `char` is not a char: its cell stays free.
        char::from_u32(u32::try_from(value).ok()?)?;
        let expr = Expr::bitvec_const(value & 0xFFFFFFFF, 32);
        let type_key = Self::type_key_for_ty(inner_ty);
        memory_inits.push((
            Arc::from(&*type_key),
            Sort::bitvec(32),
            expr.clone(),
            site.obj_id,
            site.at(0),
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
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let sort = Self::translate_ty(inner_ty)?;
        // Layout-aware: a tuple's ABI order is not its declaration order
        // (`(u8, u64)` puts the u64 first), so read each element at
        // `field_offset(i)` rather than at a declaration-order cursor.
        if self.const_safe_value_supported(inner_ty, 0) {
            return self.decode_const_safe_window(target_alloc, inner_ty, memory_inits, site);
        }
        let expr = self.read_adt_composite_from_allocation(target_alloc, 0, inner_ty, &sort)?;

        // Seed flattened tuple value for statement-level field-ref lowering.
        Self::seed_flattened_memory_init(
            target_alloc.len(),
            &expr,
            inner_ty,
            memory_inits,
            site,
            0u64,
        );

        let TyKind::RigidTy(RigidTy::Tuple(field_tys)) = inner_ty.kind() else {
            return Some(expr);
        };
        self.seed_tuple_field_memory_inits(target_alloc, inner_ty, &field_tys, memory_inits, site);
        Some(expr)
    }

    /// Seed per-field memory_inits for a tuple's fields.
    fn seed_tuple_field_memory_inits(
        &self,
        target_alloc: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        field_tys: &[rustc_public::ty::Ty],
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) {
        let tuple_layout = LayoutOf::new(inner_ty);
        for (field_idx, field_ty) in field_tys.iter().enumerate() {
            let Some(field_sort) = Self::translate_ty(*field_ty) else { return };
            let Some(field_offset) = tuple_layout.field_offset(field_idx) else { return };
            let Some(field_expr) =
                self.read_composite_from_allocation(target_alloc, field_offset, &field_sort)
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
                site.obj_id,
                site.at(field_offset as u64),
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
        site: InitSite,
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
                site.obj_id,
                site.at(offset),
            ));
        }
    }

    /// The `&str` stored at the window's byte 0 (`SS: &&str`): the string's
    /// bytes as a byte array, its length, and the inner pointer's address.
    ///
    /// Part of #3607 (`PartialEq<&str>` receives a local initialized from a
    /// promoted `&&str`). The inner pointer is the relocation AT the window's
    /// byte 0 — for `SS = &["ab", "cd"][1]` that is the pointer to `"cd"`,
    /// while the allocation's FIRST relocation points to `"ab"` — and the
    /// string's bytes are the window it names in its own target. Its seeds
    /// live at the string's own object (`note_object_read` + D2), never at the
    /// outer constant's.
    pub(super) fn extract_nested_str_from_const_ref(
        &self,
        window: &dyn ConstRead,
    ) -> Option<NestedStr> {
        let str_ty = rustc_public::ty::Ty::from_rigid_kind(RigidTy::Str);
        let (r, bytes_window) = const_pointer::fixed_pointee(self.tcx, window, 0, str_ty)?;
        let len = usize::try_from(r.metadata?).ok()?;
        if len == 0 || bytes_window.len() != len {
            return None;
        }
        let elem_sort = Sort::bitvec(8);
        let array_sort = Sort::array(ptr_sort(), elem_sort);
        let name = chc_fresh_name("__const_str");
        let mut result = ExactVar::unobserved(name, array_sort);
        for (i, byte) in bytes_window.read_data_bytes(0, len)?.into_iter().enumerate() {
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            result = result.store(idx, Expr::bitvec_const(u128::from(byte), 8));
        }
        let target = r.ptr.key()?;
        let inner = self.global_object(&target).map(|o| (o.obj_id, r.ptr.offset()));
        Some(NestedStr { bytes: result, len, inner, target, str_ty })
    }
}

/// A `&str` read through an outer constant pointer (`&&str`).
pub(super) struct NestedStr {
    /// The string's bytes, as the byte-array value fact.
    pub(super) bytes: Expr,
    /// Its length (the inner fat pointer's metadata word).
    pub(super) len: usize,
    /// The inner pointer: the string's object and its offset in it.
    pub(super) inner: Option<(u32, u64)>,
    /// The string's target, to note its read type for D2 seeding.
    pub(super) target: crate::codegen_ay::shared::const_pointer::TargetKey,
    /// `str`.
    pub(super) str_ty: rustc_public::ty::Ty,
}
