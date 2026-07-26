// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `PointerCoercion::Unsize` helpers for CHC rvalue translation.
//!
//! Contains:
//! - `is_array_to_slice_unsize`
//! - `is_custom_dst_unsize`
//! - `try_translate_dyn_trait_coercion`

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

use super::super::ChcCtx;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort};

/// Peel reference/pointer wrappers to the effective slice/array payload.
///
/// This includes repr-SIMD single-field wrappers whose payload is a fixed
/// array. Their array-to-slice coercions preserve the same lane backing as
/// ordinary `[T; N] -> [T]` unsizing.
fn peel_array_like_inner(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    ty: rustc_public::ty::Ty,
) -> rustc_public::ty::Ty {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            peel_array_like_inner(tcx, inner)
        }
        TyKind::RigidTy(RigidTy::Adt(adt_def, args))
            if rustc_internal::internal(tcx, ty).is_simd() =>
        {
            let variants = adt_def.variants();
            if variants.len() == 1 && variants[0].fields().len() == 1 {
                let field_ty = variants[0].fields()[0].ty_with_args(&args);
                peel_array_like_inner(tcx, field_ty)
            } else {
                ty
            }
        }
        TyKind::RigidTy(RigidTy::Adt(_, args)) => args
            .0
            .iter()
            .find_map(|arg| match arg {
                GenericArgKind::Type(t) => Some(*t),
                _ => None,
            })
            .map(|inner| peel_array_like_inner(tcx, inner))
            .unwrap_or(ty),
        _ => ty,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Check if an Unsize coercion converts an array type to a slice type.
    ///
    /// Covers all wrapping patterns:
    /// - `Box<[T; N]>` → `Box<[T]>` (ADT wrapper, Part of #3095)
    /// - `&[T; N]` → `&[T]` (shared reference unsizing)
    /// - `&mut [T; N]` → `&mut [T]` (mutable reference unsizing)
    /// - `*const [T; N]` → `*const [T]` (raw pointer unsizing)
    /// - `*mut [T; N]` → `*mut [T]` (raw pointer unsizing)
    ///
    /// These patterns are safe to skip fallback recording because:
    /// 1. Array data is preserved in type-indexed memory (not in fat pointer metadata)
    /// 2. The compile-time array length N is available from the source type
    /// 3. Downstream stubs recover the length via type info or MIR tracing
    ///
    /// Part of #3099: prevents false demotion for 17+ harnesses that use
    /// array-to-slice coercions in safe patterns (`.len()`, bounds checks, etc.).
    pub(super) fn is_array_to_slice_unsize(
        &self,
        operand: &Operand,
        target_ty: &rustc_public::ty::Ty,
    ) -> bool {
        let Ok(src_ty) = operand.ty(self.body.locals()) else {
            return false;
        };

        let src_inner = peel_array_like_inner(self.tcx, src_ty);
        let tgt_inner = peel_array_like_inner(self.tcx, *target_ty);

        // Source inner must be Array or Slice, target inner must be Slice or Str.
        // Part of #3655: str is layout-identical to [u8], so Unsize coercions
        // targeting str (e.g. Box<[u8]> → Box<str>) are safe in the memory model.
        let src_ok = matches!(
            src_inner.kind(),
            TyKind::RigidTy(RigidTy::Array(_, _)) | TyKind::RigidTy(RigidTy::Slice(_))
        );
        let tgt_ok = matches!(
            tgt_inner.kind(),
            TyKind::RigidTy(RigidTy::Slice(_)) | TyKind::RigidTy(RigidTy::Str)
        );
        src_ok && tgt_ok
    }

    /// Check if the Unsize target is a custom DST — an ADT with a slice tail
    /// (e.g., `MyStr { header: u8, data: str }`).
    ///
    /// Part of #4163: custom-DST Unsize casts preserve metadata through
    /// `try_propagate_dst_metadata` (D1), so they should not be classified
    /// as `unsize_metadata_lost`.
    pub(super) fn is_custom_dst_unsize(&self, target_ty: &rustc_public::ty::Ty) -> bool {
        use crate::kani_middle::abi::LayoutOf;

        let pointee = match target_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
            | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            _ => return false,
        };
        if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Adt(..))) {
            return false;
        }
        LayoutOf::new(pointee).has_slice_tail()
    }

    /// Attempt to translate an Unsize coercion to a `dyn Trait` as a Dyn_Trait
    /// datatype value with vtable discriminant.
    ///
    /// Returns `Some(expr)` if the target is `dyn Trait` and vtable ID resolution
    /// succeeds. Returns `None` to fall through to the generic BV cast.
    ///
    /// Part of #3159: connects Unsize coercion to multi-impl dispatch by
    /// assigning a concrete vtable ID that matches the enumeration order in
    /// `find_concrete_virtual_impls`.
    pub(super) fn try_translate_dyn_trait_coercion(
        &mut self,
        operand: &Operand,
        target_ty: &rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use crate::codegen_ay::chc::dyn_coercion;

        // Check if target type contains a dyn Trait (unwrap through &, *, Box).
        // Also handles ADTs with a dyn Trait tail (e.g., Pair<u8, dyn Debug>).
        // Part of #3445: struct-with-dyn-tail Unsize coercion.
        // Part of #3918: peel transport wrappers only; keep dyn-tail ADTs intact.
        let target_inner = dyn_coercion::peel_pointer_like_wrapper_ty(*target_ty);
        let dyn_tail = dyn_coercion::find_dyn_trait_tail_ty(self, target_inner)?;
        let TyKind::RigidTy(RigidTy::Dynamic(..)) = dyn_tail.kind() else {
            return None;
        };

        // Get the source concrete type (peel transport wrappers only).
        let src_ty = operand.ty(self.body.locals()).ok()?;
        let src_inner = dyn_coercion::peel_pointer_like_wrapper_ty(src_ty);

        // For struct-with-dyn-tail unsizing (e.g., Pair<i32, u8> → Pair<i32, dyn Debug>),
        // extract the concrete tail field type for vtable ID resolution. The vtable is for
        // the tail type (u8) implementing the trait (Debug), not the whole struct.
        // Part of #3589: use shared extract_concrete_tail_for_dyn + merged candidates.
        let concrete_for_vtable =
            dyn_coercion::extract_concrete_tail_for_dyn(src_inner, target_inner);
        let vtable_src =
            rustc_internal::stable(rustc_internal::internal(self.tcx, concrete_for_vtable));
        let vtable_id = dyn_coercion::resolve_dyn_target_vtable_id(self, target_inner, vtable_src)?;

        // Part of #3159: Record concrete type's size/align for vtable intrinsic constraining.
        // When vtable_size/vtable_align is called later, we build an ITE chain
        // mapping vtable discriminant values to their concrete type metadata.
        {
            use crate::kani_middle::abi::LayoutOf;
            let layout = LayoutOf::new(vtable_src);
            if let (Some(size), Some(align)) = (layout.size_of(), layout.align_of()) {
                self.vtable_type_metadata.entry(vtable_id).or_insert((size as u64, align as u64));
            }
        }

        // Part of #4225: Alias heap memory from concrete type key to unsized type key.
        {
            let src_pointee_key = Self::type_key_for_ty(src_inner);
            let tgt_pointee_key = Self::type_key_for_ty(target_inner);
            if src_pointee_key != tgt_pointee_key {
                let src_elem_sort = self.elem_sort_for_memory_array(src_inner);
                let tgt_elem_sort = self.elem_sort_for_memory_array(target_inner);
                let alias_src_expr = self.translate_operand_with_modified(operand, modified_locals);
                if let Some(alias_src) = alias_src_expr {
                    let alias_ptr =
                        dyn_coercion::extract_pointer_expr(&alias_src).unwrap_or_else(|| {
                            coerce_bitvec_width_safe(
                                alias_src,
                                POINTER_WIDTH,
                                SignExtension::ZeroExtend,
                            )
                        });
                    let alias_ptr = coerce_bitvec_width_safe(
                        alias_ptr,
                        POINTER_WIDTH,
                        SignExtension::ZeroExtend,
                    );
                    if let Some(loaded_val) = self.load_from_type_array(
                        alias_ptr.clone(),
                        &src_pointee_key,
                        src_elem_sort.clone(),
                        None,
                    ) {
                        // UnsizedCoercion FP fix: never let the alias store
                        // silently narrow a whole-struct value into a narrower
                        // target element sort. Previously a BV16 flattened
                        // struct (e.g. Outer<Inner> = concat(outer_id,
                        // inner_id), field 0 at MSB) was re-stored into the
                        // dyn-tail u8 view; coerce_store_value truncated it to
                        // the LOW byte (the LAST field) and the wrong byte-0
                        // store clobbered the correct per-field mirror stores
                        // via store forwarding — fabricating a Genuine CTREX
                        // on safe programs (and a false Safe on their duals).
                        if *loaded_val.sort() == tgt_elem_sort {
                            // Sort-equality gate: the direct alias store is
                            // lossless — keep the original #4225 path.
                            self.store_to_type_array(
                                alias_ptr,
                                loaded_val,
                                &tgt_pointee_key,
                                tgt_elem_sort,
                                false,
                            );
                            debug!(
                                src_key = %src_pointee_key,
                                tgt_key = %tgt_pointee_key,
                                "CHC: Unsize dyn coercion — aliased heap memory from concrete to unsized type key"
                            );
                        } else if tgt_elem_sort.bitvec_width() == Some(8)
                            && matches!(
                                src_inner.kind(),
                                TyKind::RigidTy(RigidTy::Adt(..))
                                    | TyKind::RigidTy(RigidTy::Tuple(_))
                            )
                        {
                            // Sized ADT/tuple → dyn-tail byte view: scatter
                            // the loaded whole-struct value per field via
                            // try_decompose_struct_store (field 0 at MSB ↔
                            // lowest byte address, real layout offsets from
                            // get_field_offset), writing each leaf scalar to
                            // mem_u8[ptr+offset] — the exact cells the
                            // virtual-inline field map reads.
                            let mut extra = Vec::new();
                            let prev_suppress = self.suppress_heap_store_checks;
                            self.suppress_heap_store_checks = true;
                            let decomposed = self.try_decompose_struct_store(
                                &alias_ptr,
                                &loaded_val,
                                src_inner,
                                &mut extra,
                            );
                            self.suppress_heap_store_checks = prev_suppress;
                            if decomposed {
                                self.heap_state.pending_updates.extend(extra);
                                debug!(
                                    src_key = %src_pointee_key,
                                    tgt_key = %tgt_pointee_key,
                                    "CHC: Unsize dyn coercion — per-field scatter of concrete struct into dyn-tail byte view"
                                );
                            } else {
                                // Decompose declined (unknown offsets/params/
                                // width mismatch): skip the alias store
                                // entirely. Unconstrained target-key cells are
                                // a sound over-approximation — they can
                                // fabricate a spurious CTREX but can never
                                // discharge an assert into a false Safe.
                                self.record_sound_fallback_reason("unsize_alias_width_mismatch");
                                debug!(
                                    src_key = %src_pointee_key,
                                    tgt_key = %tgt_pointee_key,
                                    "CHC: Unsize dyn coercion — struct decompose declined, skipping alias store (sound over-approximation)"
                                );
                            }
                        } else {
                            // Any other sort mismatch: skip the alias store
                            // (sound over-approximation) rather than emit a
                            // silently narrowing/widening store.
                            self.record_sound_fallback_reason("unsize_alias_width_mismatch");
                            debug!(
                                src_key = %src_pointee_key,
                                tgt_key = %tgt_pointee_key,
                                loaded_sort = ?loaded_val.sort(),
                                tgt_sort = ?tgt_elem_sort,
                                "CHC: Unsize dyn coercion — alias sort mismatch, skipping alias store (sound over-approximation)"
                            );
                        }
                    }
                }
            }
        }

        // Translate the source operand (the data pointer).
        let src_expr = self.translate_operand_with_modified(operand, modified_locals)?;
        let ptr_expr = dyn_coercion::extract_pointer_expr(&src_expr).unwrap_or_else(|| {
            coerce_bitvec_width_safe(src_expr.clone(), POINTER_WIDTH, SignExtension::ZeroExtend)
        });
        let ptr_expr = coerce_bitvec_width_safe(ptr_expr, POINTER_WIDTH, SignExtension::ZeroExtend);

        // Construct Dyn_Trait{fld_ptr: ptr_expr, fld_vtable: vtable_id}.
        let dyn_name = crate::codegen_ay::names::dyn_sort_name("Trait");
        let dyn_sort = crate::codegen_ay::names::struct_sort(
            dyn_name.clone(),
            [("fld_ptr", ptr_sort()), ("fld_vtable", ptr_sort())],
        );
        // Part of #2267: pre-allocate instead of format!().
        let ctor_name = {
            let mut s = String::with_capacity(dyn_name.len() + 3);
            s.push_str(&dyn_name);
            s.push_str("_mk");
            s
        };
        let vtable_expr = Expr::bitvec_const(vtable_id as u128, POINTER_WIDTH);

        // Part of #3159: Ensure the Dyn_Trait datatype is declared in the SMT2
        // output. Without this, the solver sees Dyn_Trait_mk as an unknown
        // constant and fails. All other datatype constructor codegen paths
        // call this (e.g., codegen_stmt_aggregate_adt.rs:320).
        self.declare_datatype_sort_if_needed(&dyn_sort);

        debug!(
            ?src_ty,
            ?target_ty,
            vtable_id,
            "CHC: Unsize coercion to dyn Trait with vtable ID (#3159)"
        );

        Some(Expr::datatype_constructor(
            &dyn_name,
            &ctor_name,
            vec![ptr_expr, vtable_expr],
            dyn_sort,
        ))
    }
}
