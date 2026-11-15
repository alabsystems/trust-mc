// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! A `static mut` lives in two places: its state variable, which `G[i]`,
//! `&G[i]` and a helper taking `&G` read, and its MEMORY IMAGE, the typed
//! memory the entry rule seeds with the initializer
//! (`register_static_memory_init_entries`) and a raw read of the static
//! selects (`*addr_of!(G).cast::<u8>().add(3)`).
//!
//! The static lanes of `handle_deref_store_via_ref_targets` updated the state
//! variable only, so after `G[3] = 99` or `G = [1, 2, 3, 99]` the raw read
//! returned the initializer: the bug rows verified SUCCESSFUL clean and their
//! safe twins were certified Genuine (review of fix/chc-lost-writes,
//! 2026-09-27; the whole-array store was pre-existing on main). The stored
//! value now also goes into the image, written exactly as the entry rule
//! seeded it: the value under its own type key (a datatype flattened to its
//! memory width), an array element by element, a struct or tuple field by field
//! (`static_image_fields`, also for an array element's flattened value). A
//! key the entry rule could not seed (a value of another sort) is not written
//! either, so the image stays exactly as constrained as it was.
//! A value the writer cannot split (more than 256 array elements, an unknown
//! layout) answers `false`, and the caller fails closed.
//!
//! The same holds for every static, not only a `static mut` array: an
//! `AtomicU32` static's image is seeded under `AtomicU32` and under `u32`, a
//! struct static's under the struct and each field, and a pointer a call
//! returns (`A.as_ptr()`) reads the image directly. Every store that changes
//! (or havocs) a static's state variable rewrites the whole image from it
//! (`sync_static_image`), so a view the store itself did not write never
//! keeps the initializer.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::shared::ty_signedness_shallow;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::deref_elem_store::constant_index_value;

/// The cap `mirror_array_elements_to_flat_memory` expands a whole array to.
const MAX_IMAGE_ELEMENTS: usize = 256;
/// Nesting the image writer follows (arrays and struct fields).
const MAX_IMAGE_DEPTH: usize = 8;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The base address of the memory image of the static whose state variable
    /// is `static_vec_idx`: `Ok(None)` when the static has no minted address
    /// (and so no image), `Err(())` when several objects claim it.
    fn static_image_base(&self, static_vec_idx: usize) -> Result<Option<Expr>, ()> {
        let mut objs = self
            .ref_resolution
            .static_state_idx_by_obj
            .iter()
            .filter(|&(_, &idx)| idx == static_vec_idx)
            .map(|(&obj_id, _)| obj_id);
        let Some(obj_id) = objs.next() else { return Ok(None) };
        if objs.next().is_some() {
            return Err(());
        }
        Ok(Some(Expr::bitvec_const(i128::from(obj_id), 32).concat(Expr::bitvec_const(0i128, 32))))
    }

    /// Write element `index` of the `static mut` array `array_ty` whose state
    /// variable is `static_vec_idx` into the static's memory image, at
    /// `base + i * size_of::<T>()`.
    pub(in crate::codegen_ay::chc) fn store_static_array_element_image(
        &mut self,
        static_vec_idx: usize,
        array_ty: Ty,
        index: Expr,
        rhs_expr: &Expr,
    ) -> bool {
        self.note_static_state_lane_store(static_vec_idx);
        let Ok(base) = self.static_image_base(static_vec_idx) else { return false };
        let Some(base) = base else { return true };
        let array_ty = self.resolve_body_ty(array_ty);
        let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = array_ty.kind() else {
            return false;
        };
        let Some(elem_size) = self.get_type_size(elem_ty).filter(|&s| s > 0) else {
            return false;
        };
        if !index.sort().is_bitvec() {
            return false;
        }
        let index = coerce_bitvec_width_safe(index, POINTER_WIDTH, SignExtension::ZeroExtend);
        let elem_addr = match constant_index_value(&index) {
            Some(0) => base,
            Some(i) => {
                base.bvadd(Expr::bitvec_const(u128::from(i) * elem_size as u128, POINTER_WIDTH))
            }
            None => base.bvadd(index.bvmul(Expr::bitvec_const(elem_size as u128, POINTER_WIDTH))),
        };
        self.with_static_image_writer(|ctx| {
            ctx.write_array_element_image(array_ty, elem_ty, rhs_expr, &elem_addr)
        })
    }

    /// Write the WHOLE new value of the static whose state variable is
    /// `static_vec_idx` (`G = [..]`, or the value a store through a pointer
    /// into it left) into its memory image, every view the entry rule seeded.
    ///
    /// It used to write arrays only, on the claim that a raw read of any other
    /// static resolves through its state variable. A pointer returned by a
    /// call does not: `*A.as_ptr()` (an `AtomicU32` static) selects the `u32`
    /// view of the image, and `(&CT as *const Counters as *const u32).add(1)`
    /// a field's. A store that wrote the state variable and one view left the
    /// others at the initializer, so the raw read saw the value before the
    /// store (`const_pointer_live_raw_read_dual.rs`,
    /// `bug_atomic_as_ptr_after_store` PROVED).
    pub(in crate::codegen_ay::chc) fn store_static_image(
        &mut self,
        static_vec_idx: usize,
        static_ty: Ty,
        value: &Expr,
    ) -> bool {
        if self.static_image_writes.dry_run.is_none() {
            self.note_static_state_lane_store(static_vec_idx);
        }
        let static_ty = self.resolve_body_ty(static_ty);
        let Ok(base) = self.static_image_base(static_vec_idx) else { return false };
        let Some(base) = base else { return true };
        // A contract CHECK harness seeds no image for an interior-mutable
        // static or a `static mut` (`register_static_memory_init_entries`,
        // P2-S1): those cells are free, so no view of them can be stale, and
        // a field-collapsed read must not find a pinned field there. Its
        // writer keeps its old reach, arrays only.
        if self.contract_static_havoc
            && !matches!(static_ty.kind(), TyKind::RigidTy(RigidTy::Array(..)))
        {
            return true;
        }
        self.with_static_image_writer(|ctx| ctx.write_static_image(static_ty, value, &base, 0))
    }

    /// Write `value` of type `ty` at `addr` the way the entry rule seeds a
    /// value of that type: under its own key and every field or element view
    /// below it. After a store havocked its static's image, the views of the
    /// bytes the store itself wrote are exact again.
    pub(in crate::codegen_ay::chc) fn write_static_value_image(
        &mut self,
        ty: Ty,
        value: &Expr,
        addr: &Expr,
    ) -> bool {
        self.with_static_image_writer(|ctx| ctx.write_static_image(ty, value, addr, 1))
    }

    /// Keep the memory image of the static whose state variable is
    /// `static_vec_idx` equal to the decomposition of its state: after a store
    /// changed the state to `whole`, write it; after a store havocked the
    /// state (`Err`, the token of the booking the havoc made), write a fresh
    /// value of the static's sort standing on that booking (Rule E,
    /// `Havoc::booked`), so no seeded view keeps the initializer while the
    /// state is free. `false`: the image could not be written and may be stale
    /// (the caller fails closed).
    pub(in crate::codegen_ay::chc) fn sync_static_image(
        &mut self,
        static_vec_idx: usize,
        whole: Result<Expr, crate::codegen_ay::chc::codegen_ctx::Booked>,
    ) -> bool {
        match self.static_image_base(static_vec_idx) {
            Ok(Some(_)) => {}
            Ok(None) => return true,
            Err(()) => return false,
        }
        let Some(static_ty) = self.ref_resolution.static_state_ty.get(&static_vec_idx).copied()
        else {
            return false;
        };
        let value = match whole {
            Ok(whole) => whole,
            Err(booked) => {
                let Some((_, sort)) =
                    self.state_var_mgr.output_state_vars.get(static_vec_idx).cloned()
                else {
                    return false;
                };
                crate::codegen_ay::chc::codegen_ctx::Havoc::booked(
                    booked,
                    crate::codegen_ay::chc::chc_fresh_name("__static_image_havoc"),
                    sort,
                )
            }
        };
        debug!(static_vec_idx, "CHC: static memory image rewritten from the static's state");
        self.store_static_image(static_vec_idx, static_ty, &value)
    }

    /// One array element into the image: as the entry rule seeds it, and, for
    /// a scalar element, under the array's own key too (the cell an indexed
    /// read of the array through memory reconstructs), as the element store
    /// through a `Box` writes it.
    fn write_array_element_image(
        &mut self,
        array_ty: Ty,
        elem_ty: Ty,
        value: &Expr,
        elem_addr: &Expr,
    ) -> bool {
        let elem_sort = self.elem_sort_for_memory_array(elem_ty);
        let array_key = self.type_key_for_body_ty(array_ty);
        if *value.sort() == elem_sort
            && !elem_sort.is_array()
            && !elem_sort.is_datatype()
            && array_key != self.type_key_for_body_ty(elem_ty)
            && self.elem_sort_for_memory_array(array_ty) == elem_sort
        {
            let signed = ty_signedness_shallow(elem_ty).unwrap_or(false);
            self.static_image_store(
                elem_addr.clone(),
                value.clone(),
                &array_key,
                elem_sort,
                signed,
            );
        }
        self.write_static_image(elem_ty, value, elem_addr, 1)
    }

    /// One cell of the image, or, while the image's cells are listed
    /// (`StaticImageWrites::dry_run`), its key and address.
    fn static_image_store(
        &mut self,
        addr: Expr,
        value: Expr,
        key: &str,
        elem_sort: ay_bindings::Sort,
        signed: bool,
    ) {
        if let Some(listed) = self.static_image_writes.dry_run.as_mut() {
            listed.push((key.to_string(), addr));
            return;
        }
        self.store_to_type_array(addr, value, key, elem_sort, signed);
    }

    /// Write `value` of type `ty` at `addr` the way
    /// `register_static_memory_init_entries` seeds an initializer.
    fn write_static_image(&mut self, ty: Ty, value: &Expr, addr: &Expr, depth: usize) -> bool {
        if depth > MAX_IMAGE_DEPTH {
            return false;
        }
        let ty = self.resolve_body_ty(ty);

        // The value under its own type key (`push_static_memory_init_entry`).
        let key = self.type_key_for_body_ty(ty);
        let elem_sort = self.elem_sort_for_memory_array(ty);
        let stored = if *value.sort() == elem_sort {
            Some(value.clone())
        } else if value.sort().is_datatype() {
            let flat = elem_sort
                .bitvec_width()
                .and_then(|w| crate::codegen_ay::types::flatten_datatype_to_bitvec(value, w));
            if flat.is_some() {
                self.declare_datatype_sort_if_needed(value.sort());
            }
            flat
        } else {
            None
        };
        if let Some(stored) = stored {
            let signed = ty_signedness_shallow(ty).unwrap_or(false);
            self.static_image_store(addr.clone(), stored, &key, elem_sort, signed);
        }

        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => {
                if !value.sort().is_array() {
                    return true;
                }
                let Some(len) = self.get_array_length(ty) else { return false };
                let Some(elem_size) = self.get_type_size(elem_ty) else { return false };
                let Some(index_width) =
                    value.sort().array_sort().and_then(|a| a.index_sort.bitvec_width())
                else {
                    return false;
                };
                if elem_size == 0 || len == 0 {
                    return true;
                }
                if len > MAX_IMAGE_ELEMENTS {
                    return false;
                }
                (0..len).all(|i| {
                    let elem = value.clone().select(Expr::bitvec_const(i as u128, index_width));
                    let elem_addr = if i == 0 {
                        addr.clone()
                    } else {
                        addr.clone()
                            .bvadd(Expr::bitvec_const((i * elem_size) as u128, POINTER_WIDTH))
                    };
                    if depth == 0 {
                        self.write_array_element_image(ty, elem_ty, &elem, &elem_addr)
                    } else {
                        self.write_static_image(elem_ty, &elem, &elem_addr, depth + 1)
                    }
                })
            }
            // A struct or tuple (the datatype, or an array element's flattened
            // bitvector): field by field, as the entry rule seeds it
            // (`static_image_fields`).
            _ => match self.static_image_fields(ty, value) {
                Some(fields) => fields.into_iter().all(|(field_ty, field_value, offset)| {
                    let field_addr = if offset == 0 {
                        addr.clone()
                    } else {
                        addr.clone().bvadd(Expr::bitvec_const(u128::from(offset), POINTER_WIDTH))
                    };
                    self.write_static_image(field_ty, &field_value, &field_addr, depth + 1)
                }),
                None => {
                    debug!(?ty, "CHC: static memory image written under the value's own key");
                    true
                }
            },
        }
    }
}
