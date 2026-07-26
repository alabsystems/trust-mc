// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Type size, alignment, and array query helpers.
//!
//! Extracted from `memory_impl_layout.rs` — Part of #4206.

use crate::kani_middle::abi::LayoutOf;
use rustc_public::rustc_internal;
use rustc_public::ty::{FloatTy, IntTy, RigidTy, TyKind, UintTy};
use tracing::{debug, warn};

use super::ChcCtx;
use super::memory_impl_layout::{ty_has_unresolved_non_region_params, unwrap_heap_transparent_ty};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Gets the size in bytes of a type.
    pub(in crate::codegen_ay::chc) fn get_type_size(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<usize> {
        let ty = unwrap_heap_transparent_ty(self.resolve_body_ty(ty));
        // Part of #3942: Bail out only for unresolved type/const params
        // (e.g., `MaybeUninit<[u8; BYTES/#0]>` from PointerGenerator<const BYTES>).
        // Lifetime-only params should still use rustc layout because they do not
        // change size, alignment, or field offsets.
        if ty_has_unresolved_non_region_params(ty) {
            return None;
        }
        if ty.layout().is_ok() {
            let layout = LayoutOf::new(ty);
            if let Some(size) = layout.size_of() {
                return Some(size);
            }
            if let Some((Some(size), _)) = self.resolve_trait_tail_layout(ty, &layout) {
                return Some(size);
            }
        }
        // Part of #3975: use shared dyn-tail normalization.
        let concrete_ty = self.normalize_unique_dyn_tail_ty(ty);
        if concrete_ty != ty && concrete_ty.layout().is_ok() {
            let concrete_layout = LayoutOf::new(concrete_ty);
            if let Some(size) = concrete_layout.size_of() {
                debug!(?ty, ?concrete_ty, size, "resolved dyn-tail size (#3975)");
                return Some(size);
            }
        }
        if let Some((size, _)) = self.resolve_repr_simd_layout(ty) {
            return Some(size);
        }
        if let Some(elem_ty) = self.unsized_slice_tail_elem_ty(ty) {
            return self.get_type_size(elem_ty);
        }

        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => Some(1),
            TyKind::RigidTy(RigidTy::Char) => Some(4),
            TyKind::RigidTy(RigidTy::Int(int_ty)) => match int_ty {
                IntTy::I8 => Some(1),
                IntTy::I16 => Some(2),
                IntTy::I32 => Some(4),
                IntTy::I64 => Some(8),
                IntTy::I128 => Some(16),
                IntTy::Isize => Some(8),
            },
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => match uint_ty {
                UintTy::U8 => Some(1),
                UintTy::U16 => Some(2),
                UintTy::U32 => Some(4),
                UintTy::U64 => Some(8),
                UintTy::U128 => Some(16),
                UintTy::Usize => Some(8),
            },
            TyKind::RigidTy(RigidTy::Float(float_ty)) => match float_ty {
                FloatTy::F16 => Some(2),
                FloatTy::F32 => Some(4),
                FloatTy::F64 => Some(8),
                FloatTy::F128 => Some(16),
            },
            TyKind::RigidTy(RigidTy::Ref(_, _, _)) | TyKind::RigidTy(RigidTy::RawPtr(_, _)) => {
                Some(8) // 64-bit pointers
            }
            // Zero-sized types: FnDef, Never — Part of #3083
            // FnDef is always ZST (function items have no runtime representation).
            // Never (!) is ZST (uninhabited type).
            // Note: Closure is NOT included — closures can capture variables
            // and have non-zero size. Closure size requires ty.layout().
            TyKind::RigidTy(RigidTy::FnDef(_, _)) => Some(0),
            TyKind::RigidTy(RigidTy::Never) => Some(0),
            // Array: N * element_size when both are known — Part of #3083
            TyKind::RigidTy(RigidTy::Array(elem_ty, const_len)) => {
                let len = const_len.eval_target_usize().ok()? as usize;
                let elem_size = self.get_type_size(elem_ty)?;
                Some(len * elem_size)
            }
            // Part of #3655: str is [u8] under the hood — element size is 1.
            // The actual size_of_val for str is len (the fat-pointer metadata),
            // but element-level layout (size=1, align=1) is what callers need
            // for heap access checks and memory array sort computation.
            TyKind::RigidTy(RigidTy::Str) => Some(1),
            // Slice: element size is the size of the element type.
            // Same rationale as Str — slices are unsized but element size is known.
            TyKind::RigidTy(RigidTy::Slice(elem_ty)) => self.get_type_size(elem_ty),
            // Tuple: sum element sizes (approximate — ignores alignment padding).
            // Only used when ty.layout() fails, which should be rare for tuples.
            // Part of #3083.
            TyKind::RigidTy(RigidTy::Tuple(elems)) if elems.is_empty() => Some(0),
            _ => {
                // external enum: TyKind
                // Unknown type: return None instead of guessing 8 bytes.
                // Heuristic size was unsound — a 1-byte struct field behind
                // a complex type would get wrong memory offsets, and types
                // larger than 8 bytes would get truncated reads/writes.
                // Callers already handle None with their own fallback logic.
                warn!(?ty, "No layout available for type size (unknown type)");
                // Not counted here: callers already increment their own counters
                // (record_sound_fallback, heap_check_unknown_layout) when get_type_size
                // returns None. Adding a counter here would double-count.
                None
            }
        }
    }

    /// Gets the alignment in bytes of a type.
    pub(in crate::codegen_ay::chc) fn get_type_align(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<u64> {
        let ty = unwrap_heap_transparent_ty(self.resolve_body_ty(ty));
        // Part of #3942: Bail out only for unresolved type/const params.
        if ty_has_unresolved_non_region_params(ty) {
            return None;
        }
        if ty.layout().is_ok() {
            let layout = LayoutOf::new(ty);
            if let Some(align) = layout.align_of() {
                return Some(align as u64);
            }
            if let Some((_, Some(align))) = self.resolve_trait_tail_layout(ty, &layout) {
                return Some(align);
            }
        }
        // Part of #3975: use shared dyn-tail normalization.
        let concrete_ty = self.normalize_unique_dyn_tail_ty(ty);
        if concrete_ty != ty && concrete_ty.layout().is_ok() {
            let concrete_layout = LayoutOf::new(concrete_ty);
            if let Some(align) = concrete_layout.align_of() {
                debug!(?ty, ?concrete_ty, align, "resolved dyn-tail alignment (#3975)");
                return Some(align as u64);
            }
        }
        if let Some((_, align)) = self.resolve_repr_simd_layout(ty) {
            return Some(align);
        }
        if let Some(elem_ty) = self.unsized_slice_tail_elem_ty(ty) {
            return self.get_type_align(elem_ty);
        }

        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => Some(1),
            TyKind::RigidTy(RigidTy::Char) => Some(4),
            TyKind::RigidTy(RigidTy::Int(int_ty)) => match int_ty {
                IntTy::I8 => Some(1),
                IntTy::I16 => Some(2),
                IntTy::I32 => Some(4),
                IntTy::I64 => Some(8),
                IntTy::I128 => Some(16),
                IntTy::Isize => Some(8),
            },
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => match uint_ty {
                UintTy::U8 => Some(1),
                UintTy::U16 => Some(2),
                UintTy::U32 => Some(4),
                UintTy::U64 => Some(8),
                UintTy::U128 => Some(16),
                UintTy::Usize => Some(8),
            },
            TyKind::RigidTy(RigidTy::Float(float_ty)) => match float_ty {
                FloatTy::F16 => Some(2),
                FloatTy::F32 => Some(4),
                FloatTy::F64 => Some(8),
                FloatTy::F128 => Some(16),
            },
            TyKind::RigidTy(RigidTy::Ref(_, _, _)) | TyKind::RigidTy(RigidTy::RawPtr(_, _)) => {
                Some(8)
            }
            // ZST alignment: 1 byte — Part of #3083
            TyKind::RigidTy(RigidTy::FnDef(_, _)) | TyKind::RigidTy(RigidTy::Never) => Some(1),
            // Array: alignment is element alignment — Part of #3083
            TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => self.get_type_align(elem_ty),
            // Part of #3655: str has alignment 1 (same as u8).
            TyKind::RigidTy(RigidTy::Str) => Some(1),
            // Slice: alignment is element alignment.
            TyKind::RigidTy(RigidTy::Slice(elem_ty)) => self.get_type_align(elem_ty),
            // Unit tuple: alignment 1 — Part of #3083
            TyKind::RigidTy(RigidTy::Tuple(elems)) if elems.is_empty() => Some(1),
            _ => {
                // external enum: TyKind
                // Unknown type: return None instead of guessing 8-byte alignment.
                // Matches the fail-closed pattern for get_type_size and
                // get_field_offset (#2315). Callers handle None.
                warn!(?ty, "No layout available for type alignment (unknown type)");
                // Not counted here: callers already increment their own counters
                // (record_sound_fallback, heap_check_unknown_layout) when get_type_align
                // returns None. Adding a counter here would double-count.
                None
            }
        }
    }

    /// Gets the element type of an array, slice, or repr-SIMD wrapper type.
    /// Part of #4086: handles `[T; N]`, `[T]`, and `Simd<T, N>` (wraps `[T; N]`).
    pub(in crate::codegen_ay::chc) fn get_array_element_ty(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<rustc_public::ty::Ty> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => Some(elem_ty),
            TyKind::RigidTy(RigidTy::Slice(elem_ty)) => Some(elem_ty),
            TyKind::RigidTy(RigidTy::Adt(adt_def, args))
                if rustc_internal::internal(self.tcx, ty).is_simd() =>
            {
                let variants = adt_def.variants();
                if variants.len() != 1 || variants[0].fields().len() != 1 {
                    return None;
                }
                let field_ty = variants[0].fields()[0].ty_with_args(&args);
                match field_ty.kind() {
                    TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => Some(elem_ty),
                    _ => None,
                }
            }
            _ => None, // external enum: TyKind
        }
    }

    /// Gets the compile-time length of an array or repr-SIMD wrapper type.
    /// Part of #1888, #3792: handles `[T; N]` and `Simd<T, N>` (wraps `[T; N]`).
    pub(in crate::codegen_ay::chc) fn get_array_length(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<usize> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(_, const_len)) => {
                const_len.eval_target_usize().ok().map(|len| len as usize)
            }
            TyKind::RigidTy(RigidTy::Adt(adt_def, args))
                if rustc_internal::internal(self.tcx, ty).is_simd() =>
            {
                let variants = adt_def.variants();
                if variants.len() != 1 || variants[0].fields().len() != 1 {
                    return None;
                }
                let field_ty = variants[0].fields()[0].ty_with_args(&args);
                match field_ty.kind() {
                    TyKind::RigidTy(RigidTy::Array(_, cl)) => {
                        cl.eval_target_usize().ok().map(|l| l as usize)
                    }
                    _ => None,
                }
            }
            _ => None, // external enum: TyKind
        }
    }
}
