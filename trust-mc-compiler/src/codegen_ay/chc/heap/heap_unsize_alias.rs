// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! When the unsize-to-dyn alias store may republish an object's value.
//!
//! A region object's value lives in two views: the WHOLE view (its region
//! array and its concrete type's array, written by a store of the object's
//! own sort) and the FIELD view (the field types' arrays, written by a store
//! of a field's sort, which `try_store_to_region` sends to the type array
//! only). A direct field read, and every read through a dyn receiver (the
//! walked impl reads `self.a` as a field), reads the field view. The
//! coercion `Box<C> -> Box<dyn T>` (`try_translate_dyn_trait_coercion`)
//! republishes the whole view into the field view, which is right while the
//! whole view is current and wrong after a field store: `d.a = 255; let o:
//! Box<dyn Tv> = d;` put the constructor's `a` back over the 255, and
//! `assert!(o.get() < 255)` was proved (walker_dyn_heap_write_dual.rs,
//! bug_write_then_coerce_*).
//!
//! Stores that write both views consistently (a fresh allocation's
//! initializer: `Box::new`, the `Rc`/`Arc` models; the alias store itself)
//! run inside [`ChcCtx::with_coherent_object_stores`] and are not counted.
//! Every other region store is counted by the view it reached. The decision:
//! - only field stores: the field view is current, so the alias store
//!   republishes the FIELD view's own value (read back leaf by leaf,
//!   [`ChcCtx::load_struct_from_field_view`]), which leaves the cells the dyn
//!   view reads as they are: it then reads exactly what a direct field read
//!   reads. A payload the field view cannot rebuild (an enum field, a depth
//!   past four) takes no alias store;
//! - only whole stores, or none: republish;
//! - both: neither view can be trusted to be current at the coercion; skip
//!   and record `unsize_alias_view_stale` (FailClose).
//!
//! Encoding order is not program order across blocks: a store encoded AFTER
//! the decision, in a block that can reach the coercion's block (a
//! predecessor, or a loop through it), may run first. When such a store
//! contradicts the decision the harness records the same FailClose reason.
//! Within one block encoding order is program order, so a later store there
//! runs after the coercion and cannot.

use super::ChcCtx;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::types::POINTER_WIDTH;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

/// Not blessed: the unsize alias store's decision may rest on a view a store
/// of the object made stale.
pub(in crate::codegen_ay::chc) const UNSIZE_ALIAS_VIEW_STALE: &str = "unsize_alias_view_stale";

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Run `f` with its region stores counted as writing both views of their
    /// object consistently.
    pub(in crate::codegen_ay::chc) fn with_coherent_object_stores<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.heap_state.coherent_object_stores += 1;
        let result = f(self);
        self.heap_state.coherent_object_stores -= 1;
        result
    }

    /// Count a region store to `obj_id` by the view it reached (`field`:
    /// another sort than the region's), and fail closed when it contradicts an
    /// alias decision it may precede.
    pub(in crate::codegen_ay::chc) fn note_object_view_store(&mut self, obj_id: u32, field: bool) {
        if self.heap_state.coherent_object_stores > 0 {
            return;
        }
        if field {
            self.heap_state.field_view_store_objs.insert(obj_id);
        } else {
            self.heap_state.whole_view_store_objs.insert(obj_id);
        }
        let Some(decisions) = self.heap_state.unsize_alias_decisions.get(&obj_id) else {
            return;
        };
        let here = self.current_encode_bb;
        let contradicted = decisions.iter().any(|&(alias_bb, republished)| {
            republished == field && self.block_reaches_after_an_edge(here, alias_bb)
        });
        if contradicted {
            debug!(
                obj_id,
                block = here,
                field,
                "CHC: a store may precede the unsize alias decision it contradicts — fail closed"
            );
            self.record_sound_fallback_reason(UNSIZE_ALIAS_VIEW_STALE);
        }
    }

    /// Decide whether the unsize alias store may republish `obj_id`'s whole
    /// view into its field view, and record the decision.
    pub(in crate::codegen_ay::chc) fn unsize_alias_may_republish(&mut self, obj_id: u32) -> bool {
        let field = self.heap_state.field_view_store_objs.contains(&obj_id);
        let whole = self.heap_state.whole_view_store_objs.contains(&obj_id);
        if field && whole {
            debug!(
                obj_id,
                "CHC: unsize alias: both views of the object were written — fail closed"
            );
            self.record_sound_fallback_reason(UNSIZE_ALIAS_VIEW_STALE);
        }
        let republish = !field;
        let block = self.current_encode_bb;
        self.heap_state.unsize_alias_decisions.entry(obj_id).or_default().push((block, republish));
        republish
    }

    /// The value of the struct or tuple of type `ty` at `addr` as its FIELD
    /// view holds it: every scalar leaf read the way a field read reads it
    /// (`load_from_memory_untyped` at the leaf's offset), the value rebuilt
    /// around them. The reads add no heap checks: the coercion dereferences
    /// nothing. `None` for a multi-variant or unlaid-out level.
    pub(in crate::codegen_ay::chc) fn load_struct_from_field_view(
        &mut self,
        addr: &Expr,
        ty: Ty,
    ) -> Option<Expr> {
        let checks = self.heap_state.pending_checks.len();
        let value = self.load_struct_from_field_view_at(addr, ty, 0);
        self.heap_state.pending_checks.truncate(checks);
        value
    }

    /// The value of the struct or tuple field of type `ty` at `addr`, read the
    /// way the walked impl's field map reads it: rebuilt from its scalar leaves
    /// when the field map rebuilds that type (`field_map_rebuilds_from_leaves`),
    /// with the heap checks of the whole field's access. `None` for any other
    /// type, which the caller loads from the type's own array as before.
    ///
    /// The Deref+Field lane (`try_deref_field_offset_load`) loaded such a
    /// field from its own type-indexed array, which a store of one of its
    /// leaves never writes: `d.x.0 = 255; let t = d.x; assert!(t.0 < 255)` on
    /// a `Box<N2 { x: (u8, u8), .. }>` read the constructor's byte, and the
    /// safe twin (`== 255`) was certified a Genuine failure on main. The same
    /// held for a struct field (`d.i.p = 255; let i = d.i;`) and through a raw
    /// pointer, where the bug twin verified SUCCESSFUL clean (review
    /// follow-up of fix/chc-lost-writes, 2026-09-27).
    pub(in crate::codegen_ay::chc) fn load_aggregate_field_from_leaves(
        &mut self,
        addr: &Expr,
        ty: Ty,
    ) -> Option<Expr> {
        let ty = self.resolve_body_ty(ty);
        if !crate::codegen_ay::chc::call::inline_field_map_reconstruct::field_map_rebuilds_from_leaves(
            self, ty,
        ) {
            return None;
        }
        let checks = self.heap_access_checks(addr.clone(), ty);
        let value = self.load_struct_from_field_view(addr, ty)?;
        if !checks.is_empty() {
            self.mark_heap_metadata_read();
        }
        self.heap_state.pending_checks.extend(checks);
        debug!(?ty, "CHC: aggregate field rebuilt from its leaves");
        Some(value)
    }

    fn load_struct_from_field_view_at(
        &mut self,
        addr: &Expr,
        ty: Ty,
        depth: usize,
    ) -> Option<Expr> {
        const MAX_DEPTH: usize = 4;
        let ty = self.resolve_body_ty(ty);
        let sort = Self::translate_ty(ty)?;
        let Some(dt) = sort.datatype_sort() else {
            let leaf = self.load_from_memory_untyped(addr.clone(), ty)?;
            return (*leaf.sort() == sort).then_some(leaf);
        };
        if depth >= MAX_DEPTH {
            return None;
        }
        let [ctor] = dt.constructors.as_slice() else { return None };
        let field_tys: Vec<Ty> = match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let variants = def.variants();
                let [variant] = variants.as_slice() else { return None };
                variant
                    .fields()
                    .iter()
                    .map(|f| mono_ty::field_ty(f, &args))
                    .collect::<Option<Vec<_>>>()?
            }
            TyKind::RigidTy(RigidTy::Tuple(elems)) => elems,
            _ => return None,
        };
        if field_tys.len() != ctor.fields.len() || field_tys.is_empty() {
            return None;
        }
        let mut fields = Vec::with_capacity(field_tys.len());
        for (idx, (field_ty, field)) in field_tys.iter().zip(ctor.fields.iter()).enumerate() {
            let offset = self.get_field_offset(ty, idx)?;
            let field_addr = if offset == 0 {
                addr.clone()
            } else {
                addr.clone().bvadd(Expr::bitvec_const(offset as i64, POINTER_WIDTH))
            };
            let value = self.load_struct_from_field_view_at(&field_addr, *field_ty, depth + 1)?;
            if *value.sort() != field.sort {
                return None;
            }
            fields.push(value);
        }
        Some(Expr::datatype_constructor(&dt.name, &ctor.name, fields, sort.clone()))
    }

    /// Record `unsize_alias_view_stale` when the dyn view of `ty` would read a
    /// field the republished leaves do not reach
    /// (`payload_field_read_as_a_whole`).
    pub(in crate::codegen_ay::chc) fn fail_closed_on_field_read_as_a_whole(&mut self, ty: Ty) {
        if self.payload_field_read_as_a_whole(ty) {
            debug!(
                ?ty,
                "CHC: unsize alias: a payload field the dyn view reads whole is stale after a \
                 field store — fail closed"
            );
            self.record_sound_fallback_reason(UNSIZE_ALIAS_VIEW_STALE);
        }
    }

    /// `true` when a top-level field of the payload `ty` is an aggregate whose
    /// leaves a store can write one by one, but which the walked impl's field
    /// map loads WHOLE from the field's own type-indexed array
    /// (`build_self_field_map`), an array no leaf store writes: a struct or
    /// tuple the field map does not rebuild from its leaves
    /// (`field_map_rebuilds_from_leaves`: an enum inside it, a one-element
    /// tuple, nesting past its depth), or an array of structs or tuples. The
    /// field-view republish writes the leaves, so the dyn read of such a field
    /// would return the value from before the field store.
    ///
    /// A tuple field was such a field until the field map rebuilt tuples and
    /// nested structs from their leaves: after `d.x.0.0 = 255` on
    /// `D3 { x: ((u8, u8), u8), .. }` the walked `(self.x.0).0` read the
    /// constructor's byte, and `assert!(o.get() < 255)` verified SUCCESSFUL
    /// clean (review of fix/chc-lost-writes, 2026-09-27, `bug_depth3_box_dyn`).
    fn payload_field_read_as_a_whole(&self, ty: Ty) -> bool {
        let ty = self.resolve_body_ty(ty);
        let field_tys: Vec<Ty> = match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let Some(tys) = def
                    .variants()
                    .iter()
                    .flat_map(|v| v.fields().into_iter().map(|f| mono_ty::field_ty(&f, &args)))
                    .collect::<Option<Vec<_>>>()
                else {
                    return false;
                };
                tys
            }
            TyKind::RigidTy(RigidTy::Tuple(elems)) => elems,
            _ => return false,
        };
        field_tys.into_iter().any(|field_ty| {
            let field_ty = self.resolve_body_ty(field_ty);
            match field_ty.kind() {
                TyKind::RigidTy(RigidTy::Tuple(elems)) => {
                    !elems.is_empty()
                        && !crate::codegen_ay::chc::call::inline_field_map_reconstruct::field_map_rebuilds_from_leaves(self, field_ty)
                }
                // A struct the type translation keeps as a datatype; a struct
                // it collapses to its only field is read as that field.
                TyKind::RigidTy(RigidTy::Adt(def, _))
                    if def.kind() == rustc_public::ty::AdtKind::Struct
                        && Self::translate_ty(field_ty).is_some_and(|s| s.is_datatype()) =>
                {
                    !crate::codegen_ay::chc::call::inline_field_map_reconstruct::field_map_rebuilds_from_leaves(self, field_ty)
                }
                TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => matches!(
                    self.resolve_body_ty(elem_ty).kind(),
                    TyKind::RigidTy(RigidTy::Adt(..) | RigidTy::Tuple(_))
                ),
                _ => false,
            }
        })
    }

    /// `true` when a path of one or more edges leads from `from` to `to`.
    fn block_reaches_after_an_edge(&self, from: usize, to: usize) -> bool {
        let blocks = &self.body.blocks;
        let mut seen = vec![false; blocks.len()];
        let mut stack: Vec<usize> =
            blocks.get(from).map(|b| b.terminator.successors()).unwrap_or_default();
        while let Some(bb) = stack.pop() {
            if bb == to {
                return true;
            }
            if bb >= seen.len() || std::mem::replace(&mut seen[bb], true) {
                continue;
            }
            stack.extend(blocks[bb].terminator.successors());
        }
        false
    }
}
