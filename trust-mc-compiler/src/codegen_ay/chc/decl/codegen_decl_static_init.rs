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

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};

use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::shared::const_pointer::ConstRead;
use std::sync::Arc;
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Records "the initializer datum `value` lives at address `addr`" for the
    /// entry rule's typed-memory mirror.
    ///
    /// The two operands used to be adjacent bare `Expr`s — one an address, one a
    /// value, with nothing but argument order keeping them apart. That is the
    /// canonical shape of the slot-misalignment defect class (see
    /// `docs/addr-vs-value-conversion-queue.md` wave 13); taking [`Val`] and
    /// [`Loc`] makes the swap a compile error.
    pub(in crate::codegen_ay::chc) fn push_static_memory_init_entry(
        &mut self,
        rust_ty: rustc_public::ty::Ty,
        value: Val,
        addr: Loc,
    ) {
        let value_expr = value.into_expr();
        let addr_expr = addr.into_expr();
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

    /// Address arithmetic: a byte offset into the object `addr` names. Address
    /// in, address out — the offset is a value and cannot be swapped for the
    /// base.
    pub(in crate::codegen_ay::chc) fn static_addr_with_offset(addr: Loc, offset: u64) -> Loc {
        if offset == 0 {
            addr
        } else {
            Loc::of_address(
                addr.into_expr().bvadd(Expr::bitvec_const(
                    offset as i128,
                    crate::codegen_ay::types::POINTER_WIDTH,
                )),
            )
        }
    }

    /// Mirrors a static's initializer into typed memory, decomposing arrays and
    /// structs into per-element / per-field `(value, address)` pairs.
    ///
    /// `mutable`: the memory can be written after entry (a `static mut`, the
    /// referent of a mutable nested static). An immutable static's
    /// `MaybeUninit` / `ManuallyDrop` value is decomposed as its content
    /// ([`Self::static_image_wrapper_content`]); a mutable one's is not.
    pub(in crate::codegen_ay::chc) fn register_static_memory_init_entries(
        &mut self,
        rust_ty: rustc_public::ty::Ty,
        value: Val,
        addr: Loc,
        mutable: bool,
    ) {
        use rustc_public::ty::{RigidTy, TyKind};

        let value_expr = value.as_expr().clone();

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
        self.push_static_memory_init_entry(rust_ty, value.clone(), addr.clone());

        // Part of #4196: Decompose array-typed statics into per-element memory inits.
        // For `[T; N]`, the whole-array value sort is `Array(BV64, elem_sort)` but
        // the typed memory array's element sort is per-element (e.g., BV32 for char).
        // Without decomposition, `push_static_memory_init_entry` silently drops the
        // whole-array value due to sort mismatch, leaving memory unconstrained.
        // The declared type may carry unevaluated constants
        // (`[(u64, u64); SIZE1]`): decompose it as a body sees it.
        let rust_ty = self.normalize_static_ty(rust_ty);
        // An immutable static's wrapper holds its content under the content's
        // decomposition (the whole-value entry above already has the content's
        // key: the typed memory keys `MaybeUninit<T>` like `T`).
        let rust_ty = match self.static_image_wrapper_content(rust_ty) {
            Some(content) if !mutable => content,
            _ => rust_ty,
        };
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
                            // Selecting out of an initializer array yields the
                            // element DATUM; the address moves by the element
                            // stride. The two can no longer be transposed.
                            let elem_value = Val::of_value(value_expr.clone().select(idx));
                            let elem_addr =
                                Self::static_addr_with_offset(addr.clone(), i * elem_size as u64);
                            self.register_static_memory_init_entries(
                                elem_ty, elem_value, elem_addr, mutable,
                            );
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

        // A struct or tuple, whether its value is the datatype or the flattened
        // bitvector of an array element: each field at its ABI offset
        // (`static_image_fields`, the decomposition `write_static_image`
        // writes and the untyped-view net 2 reads as seeded).
        let Some(fields) = self.static_image_fields(rust_ty, &value_expr) else {
            return;
        };
        for (field_ty, field_value, offset) in fields {
            let field_addr = Self::static_addr_with_offset(addr.clone(), offset);
            self.register_static_memory_init_entries(
                field_ty,
                Val::of_value(field_value),
                field_addr,
                mutable,
            );
        }
    }

    // sort_default_expr moved to codegen_decl_static_alloc.rs (Part of #4196).

    /// Compute initial value for a static, handling flattened Datatype array elements.
    /// Detects BV-flattened arrays and reads fields individually to fix byte ordering.
    /// Part of #3496 Phase 5.
    ///
    /// This is a producer of [`Val`]: whatever the initializer image decodes to
    /// is the static's *datum*, including the case where that datum happens to
    /// be a pointer the static holds. It is never the address of the static
    /// itself — that is minted separately (the object table
    /// `RefResolution::global_objects`, chc/decl/global_objects.rs), and
    /// confusing the two is what that table vs `static_initial_values` keeps
    /// apart.
    pub(in crate::codegen_ay::chc) fn static_init_from_alloc(
        &mut self,
        bytes: &dyn ConstRead,
        sort: &Sort,
        rust_ty: rustc_public::ty::Ty,
    ) -> Option<Val> {
        use rustc_public::ty::{RigidTy, TyKind};

        // A fn-pointer static holds a relocation to a function, whose bytes
        // are all zero: the value is the function's identity (the same term
        // a reification of it produces). Read as bytes, `static SF: fn(..) =
        // f` started at 0, so `SF == f as fn(..)` failed, certified Genuine
        // (`walker_fn_ptr_completeness_dual.rs::safe_static_eq_reified`).
        if matches!(rust_ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(..)))
            && sort.bitvec_width() == Some(crate::codegen_ay::types::POINTER_WIDTH)
            && let Some(ptr) = bytes.stored_pointer(0)
            && let Some(identity) = Self::fn_ptr_identity_of_const_ptr(&ptr)
        {
            return Some(Val::of_value(identity.into_expr()));
        }

        if let TyKind::RigidTy(RigidTy::Array(elem_ty, len)) = rust_ty.kind()
            && sort.is_array()
            && matches!(elem_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)))
        {
            let array_len = len.eval_target_usize().ok()? as usize;
            return self
                .read_array_with_pointer_elements_from_allocation(
                    bytes, 0, sort, elem_ty, array_len,
                )
                .map(Val::of_value);
        }

        // Arrays, slices, structs and tuples by their real layout: fields at
        // their ABI offsets, elements at their stride, a datatype element
        // flattened as `translate_ty` flattens it. The sequential readers
        // decoded every static whose fields rustc reorders wrongly
        // (`codegen_decl_static_layout.rs`). Every leaf is read under the slot
        // clause (`shared::const_pointer`), so an initializer that holds
        // pointers goes through here too, scalar or not: a pointer field is
        // its relocation's address (D8), never its offset bytes — `static HS:
        // Holder = Holder { r: &ARR[1] }` decoded `HS.r` as object 0 + 4.
        if bytes.has_relocations() || sort.is_array() || sort.is_datatype() {
            debug!(?rust_ty, "static_init: reading the initializer by its layout");
            return self.read_static_value_by_layout(bytes, 0, rust_ty, sort, 0).map(Val::of_value);
        }

        // Scalars.
        Self::scalar_from_alloc(bytes, sort).map(Val::of_value)
    }

    /// Both halves of a referent seed are values: the referent's contents and,
    /// for an unsized referent, its element count. Neither is an address.
    pub(in crate::codegen_ay::chc) fn static_seed_metadata_for_value(
        &mut self,
        value_ty: rustc_public::ty::Ty,
        value: Val,
        backing_len: Option<usize>,
    ) -> Option<(Expr, Option<Expr>)> {
        use rustc_public::ty::{RigidTy, TyKind};

        let value_expr = value.into_expr();
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
                let len = backing_len? / elem_bytes;
                let len_expr =
                    Expr::bitvec_const(len as u128, crate::codegen_ay::types::POINTER_WIDTH);
                Some((value_expr, Some(len_expr)))
            }
            TyKind::RigidTy(RigidTy::Str) => {
                let len_expr = Expr::bitvec_const(
                    backing_len? as u128,
                    crate::codegen_ay::types::POINTER_WIDTH,
                );
                Some((value_expr, Some(len_expr)))
            }
            _ => None,
        }
    }

    /// The referent seed of a pointer-typed static (D9): the pointee WINDOW
    /// its own pointer names (at the pointer's offset in its target, not the
    /// target's byte 0), and — for a `[T]` / `str` pointee — the length word
    /// its own bytes carry beside the pointer (not the target's size).
    ///
    /// For `static SLS: &[u32] = ARR.split_at(1).1`, both `SLS.len() == 3`
    /// and `SLS[0] == 1` PROVED when this read the target from byte 0 and
    /// measured it.
    pub(in crate::codegen_ay::chc) fn resolve_pointer_static_seed_metadata(
        &mut self,
        static_bytes: &dyn ConstRead,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<(Expr, Option<Expr>)> {
        let (r, value) = self.fixed_window_value(static_bytes, 0, pointee_ty)?;
        if !value.sort().is_array() {
            return None;
        }
        match pointee_ty.kind() {
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Array(..)) => {
                Some((value, None))
            }
            rustc_public::ty::TyKind::RigidTy(
                rustc_public::ty::RigidTy::Slice(_) | rustc_public::ty::RigidTy::Str,
            ) => {
                let len = Expr::bitvec_const(
                    u128::from(r.metadata?),
                    crate::codegen_ay::types::POINTER_WIDTH,
                );
                Some((value, Some(len)))
            }
            _ => None,
        }
    }

    // read_array_with_pointer_elements_from_allocation, read_pointer_like_from_allocation,
    // seed_static_str_backing_memory, alloc_dst_pointer_fallback, resolve_static_target_init_expr,
    // resolve_pointer_static_init moved to codegen_decl_static_alloc.rs (Part of #4196).
}
