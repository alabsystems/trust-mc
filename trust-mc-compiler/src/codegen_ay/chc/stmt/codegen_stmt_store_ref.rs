// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Reg-level deref store via ref_targets for CHC block statement encoding.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//!
//! Contains:
//! - `handle_deref_store_via_ref_targets`: `*ref = value` at Reg level via ref_targets (#1957)
//! - `handle_deref_store_array_via_ref_targets`: array element case for ref_target stores

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

use super::codegen_call_coerce::coerce_eq_constraint;
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_stmt_store::RefStoreReinterpretation;
use super::stmt_accumulator::StmtAccumulator;
use super::{ChcCtx, FieldProjection, UnknownProjectionPolicy, collect_field_projections};

/// Not blessed: an element store through a static array whose element could
/// not be written; the static is havocked instead.
const STATIC_ELEM_STORE_UNPLACED: &str = "static_elem_store_unplaced";

/// Extension trait for ref_target-based deref store handlers.
pub(crate) trait StmtStoreRef {
    /// Handles Deref store at Reg level via ref_targets (#1957).
    fn handle_deref_store_via_ref_targets(
        &mut self,
        lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool;
    fn store_whole_value_into_flattened_local(
        &mut self,
        target_local: usize,
        ref_local: usize,
        rhs_expr: Expr,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool;

    /// Handles array element store via ref_targets (#1957).
    fn handle_deref_store_array_via_ref_targets(
        &mut self,
        rhs_expr: Expr,
        ref_local: usize,
        ref_target: &super::RefTarget,
        index_proj: &ProjectionElem,
        field_projs: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool;

    /// Handles array element store through arg-ref pointee (#2750).
    fn handle_deref_store_array_arg_ref(
        &mut self,
        rhs_expr: Expr,
        local_idx: usize,
        pointee_vec_idx: usize,
        index_proj: &ProjectionElem,
        field_projs: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool;
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// A store into a pointer local replaces its referent, not the storage
    /// containing that pointer. Keep the updated state and storage address,
    /// but discard facts about the old pointer value and its backing bytes.
    fn clear_replaced_pointer_metadata(&mut self, local: usize) {
        let Some(decl) = self.body.locals().get(local) else { return };
        if matches!(
            self.resolve_body_ty(decl.ty).kind(),
            TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
        ) {
            self.clear_path_insensitive_ref_metadata(local);
            self.known_alloc_ids.remove(&local);
            self.known_stack_addr_exprs.remove(&local);
            self.clear_known_vtable_discriminant(local);
        }
    }

    /// Keep the typed-memory image of `target_local` in step with the state a
    /// Reg-level store through a resolved reference just gave it.
    ///
    /// This lane constrains only the local's state variable. Its image, written
    /// when the local was assigned or borrowed, kept the old value, and a read
    /// through a pointer made before the store — one joined from two borrows,
    /// which has no single points-at edge — loaded it: with
    /// `let r: *const u8 = if b { &m } else { &n }; let p = &mut m; *p = 7;`
    /// --ay-chc proved `unsafe { *r } != 7` on the path that took `&m`
    /// (tools/soundness-duals/negative/stale_memory_image_writes.rs). When the
    /// image cannot be written, the store fails closed.
    pub(in crate::codegen_ay::chc) fn refresh_ref_target_memory_image(
        &mut self,
        target_local: usize,
        new_value: &Expr,
        acc: &mut StmtAccumulator<'_>,
    ) {
        if self.track_level < crate::args::ChcTrackLevel::Mem {
            return;
        }
        let place = Place { local: target_local, projection: Vec::new() };
        let modified = acc.modified.clone();
        let Some(loc) = self.translate_ref_to_address(&place, &modified) else {
            self.record_sound_fallback_reason("deref_store_memory_image_unrefreshed");
            return;
        };
        let Some(target_ty) = self.body.locals().get(target_local).map(|decl| decl.ty) else {
            self.record_sound_fallback_reason("deref_store_memory_image_unrefreshed");
            return;
        };
        let addr = loc.into_expr();
        // NOTE: `mirror_ref_value_to_memory` writes through `heap_state`
        // (`try_store_to_region`) as well as through `constraints`, so the
        // number of constraints it pushes says NOTHING about whether the image
        // moved. An earlier version of this repair treated an unchanged
        // constraint count as "nothing written" and demoted every element store
        // in the lane.
        self.mirror_ref_value_to_memory(
            &addr,
            new_value,
            target_ty,
            target_local,
            &modified,
            acc.constraints,
        );
    }

    /// The whole new value of the static `static_vec_idx` after the scalar
    /// store `*p = rhs`, where `p` (`ptr_local`) addresses the static's base
    /// with no static place path (#428). `rhs` is the static's whole value
    /// only when the store writes `size_of` the static's bytes; a narrower
    /// store at the base of an integer static replaces its low bytes
    /// (`splice_integer_bytes`). Any other width is `None`: the caller
    /// havocs the static and records why (fail closed). The lane used to
    /// coerce `rhs` to the static's width, so a byte store zero-extended into
    /// the whole static.
    fn whole_static_scalar_store_value(
        &self,
        ptr_local: usize,
        static_vec_idx: usize,
        rhs: Expr,
        modified: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let store_ty = Self::deref_pointee_ty(self.body.locals().get(ptr_local)?.ty);
        let static_ty = self.ref_resolution.static_state_ty.get(&static_vec_idx).copied();
        let (Some(store_ty), Some(static_ty)) = (store_ty, static_ty) else {
            return Some(rhs);
        };
        let (Some(store_size), Some(static_size)) =
            (self.get_type_size(store_ty), self.get_type_size(static_ty))
        else {
            return Some(rhs);
        };
        if store_size == static_size {
            return self.same_width_static_store_value(static_vec_idx, store_ty, static_ty, rhs);
        }
        let current = self.static_state_current(static_vec_idx, modified)?;
        let spliced = crate::codegen_ay::chc::decl::static_path::splice_integer_bytes(
            static_ty, &current, 0, store_ty, &rhs,
        );
        debug!(
            ptr_local,
            static_vec_idx,
            store_size,
            static_size,
            spliced = spliced.is_some(),
            "CHC: scalar store narrower or wider than its static (#428)"
        );
        spliced
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The whole new value of a static after a store of `size_of` the
    /// static's bytes at its base, of type `store_ty`. A STRUCT or TUPLE
    /// static of several fields takes the stored bits in MEMORY order
    /// (`transmute_aggregate_memory_order`): the lane used to return the bits
    /// as the struct's whole value, and the constraint unflattened them in
    /// declaration order, MSB first, so `*(addr_of_mut!(PS) as *mut u32) =
    /// 0x0005_0006` into `#[repr(C)] struct { a: u16, b: u16 }` set `a = 5,
    /// b = 6`, and the safe `PS.a == 6 && PS.b == 5` was certified Genuine
    /// (const_pointer_live_same_width_dual.rs). A layout that lane does not
    /// model is `None`: the caller havocs the static and fails closed. Any
    /// other pair of types keeps the stored value as the static's.
    fn same_width_static_store_value(
        &self,
        static_vec_idx: usize,
        store_ty: rustc_public::ty::Ty,
        static_ty: rustc_public::ty::Ty,
        rhs: Expr,
    ) -> Option<Expr> {
        use crate::codegen_ay::chc::stmt::codegen_stmt_transmute_layout::AggregateTransmute;
        match self.transmute_aggregate_memory_order(&rhs, store_ty, static_ty) {
            AggregateTransmute::NotApplicable => Some(rhs),
            AggregateTransmute::Precise(value) => {
                let out_sort = self.state_var_mgr.output_state_vars.get(static_vec_idx)?.1.clone();
                (*value.sort() == out_sort).then_some(value)
            }
            AggregateTransmute::Unsupported(why) => {
                debug!(
                    static_vec_idx,
                    why, "CHC: same-width store into an aggregate static not encodable"
                );
                None
            }
        }
    }
}

impl<'tcx, 'body> StmtStoreRef for ChcCtx<'tcx, 'body> {
    /// Store a whole value through a reference into a flattened local.
    ///
    /// A flattened struct or tuple local has one state variable per leaf field,
    /// and the slot `try_state_idx_for_local` names is only the first of them.
    /// The whole-value store used to constrain that one slot with the whole
    /// value, so no field changed: `let r = &mut s; *r = S { a: 1, b: 2 };
    /// assert!(s.b == 0)` verified SUCCESSFUL. Every leaf slot is constrained
    /// from the value instead; a value that does not decompose into exactly the
    /// local's slots leaves the local unconstrained and fails closed.
    fn store_whole_value_into_flattened_local(
        &mut self,
        target_local: usize,
        ref_local: usize,
        rhs_expr: Expr,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let slots = self.flattened_field_count(target_local);
        let field_constraints =
            self.build_flattened_destination_field_constraints(target_local, rhs_expr.clone());
        match field_constraints {
            Some(field_constraints)
                if field_constraints.len() == slots
                    && field_constraints.iter().enumerate().all(|(i, (field, _))| *field == i) =>
            {
                for (field, constraint) in field_constraints {
                    let key = self.flattened_field_constraint_key(target_local, field);
                    acc.replace_constraint(key, constraint);
                }
                self.encode.local_expr_env.insert(target_local, rhs_expr);
                debug!(
                    target_local,
                    ref_local, slots, "CHC: emitted whole-value Deref store into flattened local"
                );
            }
            _ => {
                warn!(
                    target_local,
                    ref_local,
                    slots,
                    "CHC: whole-value store does not decompose into the flattened local"
                );
                self.record_sound_fallback_reason("deref_store_flattened_target_undecomposed");
                for field in 0..slots {
                    let key = self.flattened_field_constraint_key(target_local, field);
                    acc.replace_constraint(key, Expr::bool_const(true));
                }
                self.encode.local_expr_env.remove(&target_local);
            }
        }
        acc.modified.insert(target_local);
        true
    }

    fn handle_deref_store_via_ref_targets(
        &mut self,
        lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        if lhs.projection.is_empty() || !matches!(lhs.projection[0], ProjectionElem::Deref) {
            return false;
        }
        // FC-06: register-promoted deref stores bypass build_memory_store, so
        // the modifies frame-condition check must fire here as well.
        self.modifies_frame_ref_store_check(lhs, &acc.modified);
        // Part of #3348: Handle deref store through IndexMut-returned &mut T.
        if let Some(cmr) = self.ref_resolution.collection_mut_refs.get(&local_idx).cloned() {
            return self.handle_collection_mut_ref_store(rhs_expr, &cmr, acc);
        }

        // Part of #2496: Handle deref store through argument reference locals.
        if let Some(&pointee_vec_idx) = self.ref_resolution.ref_arg_pointee_idx.get(&local_idx) {
            let track_key = usize::MAX - pointee_vec_idx; // synthetic key (#2496)
            let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(pointee_vec_idx)
            else {
                warn!(
                    ?local_idx,
                    pointee_vec_idx,
                    "CHC: dropped arg-ref deref store — missing pointee output state var (#2496)"
                );
                self.diagnostics.store_dropped_transition.inc();
                self.mark_state_var_modified(pointee_vec_idx); // #3138
                return true;
            };
            let mut pointee_field_projs = Vec::new();
            let mut index_proj_found = None;
            let mut pending_cons_idx = None;
            for (i, proj) in lhs.projection[1..].iter().enumerate() {
                match proj {
                    ProjectionElem::Downcast(variant_idx) if index_proj_found.is_none() => {
                        pending_cons_idx =
                            Some(crate::rustc_public_bridge::IndexedVal::to_index(variant_idx));
                    }
                    ProjectionElem::Field(idx, ty) if index_proj_found.is_none() => {
                        pointee_field_projs.push(FieldProjection {
                            field_idx: *idx,
                            cons_idx: pending_cons_idx.take(),
                            field_ty: Some(*ty),
                        });
                    }
                    ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                        index_proj_found = Some((i, proj.clone()));
                        break;
                    }
                    _ => return false, // external enum: ProjectionElem
                }
            }
            // Part of #2750: Route array element stores through arg-ref pointee.
            if let Some((_idx_offset, index_proj)) = index_proj_found {
                // Part of #3816: aggregate pointee — select field, store, update.
                if !pointee_field_projs.is_empty() {
                    return self.handle_aggregate_field_array_store_arg_ref_impl(
                        rhs_expr,
                        local_idx,
                        pointee_vec_idx,
                        track_key,
                        &index_proj,
                        &pointee_field_projs,
                        acc,
                    );
                }
                let post_idx_fp = collect_field_projections(
                    &lhs.projection[1 + _idx_offset + 1..],
                    UnknownProjectionPolicy::Break,
                );
                return self.handle_deref_store_array_arg_ref(
                    rhs_expr,
                    local_idx,
                    pointee_vec_idx,
                    &index_proj,
                    &post_idx_fp,
                    acc,
                );
            }
            let out_var = Expr::var(&**out_name, out_sort.clone());
            if pointee_field_projs.is_empty() {
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, rhs_expr.clone(), out_sort, false)
                {
                    acc.replace_constraint(track_key, constraint);
                    self.encode.local_expr_env.insert(track_key, rhs_expr);
                    self.mark_state_var_modified(pointee_vec_idx);
                    debug!(
                        local_idx,
                        pointee_vec_idx, "CHC: scalar Deref store via arg-ref (#2496)"
                    );
                    return true;
                }
                warn!(
                    ?local_idx,
                    pointee_vec_idx,
                    "CHC: arg-ref scalar deref store sort mismatch — constraint dropped"
                );
                self.diagnostics.store_dropped_transition.inc();
                self.mark_state_var_modified(pointee_vec_idx); // #3138
                return true;
            }

            let root_in = if let Some(env_expr) = self.encode.local_expr_env.get(&track_key) {
                env_expr.clone()
            } else if self.encode.modified_state_indices.contains(&pointee_vec_idx) {
                Expr::var(&**out_name, out_sort.clone())
            } else if let Some((in_name, in_sort)) =
                self.state_var_mgr.state_vars.get(pointee_vec_idx)
            {
                Expr::var(&**in_name, in_sort.clone())
            } else {
                warn!(
                    ?local_idx,
                    pointee_vec_idx,
                    "CHC: dropped arg-ref field deref store — missing pointee input state var"
                );
                self.diagnostics.store_dropped_transition.inc();
                self.mark_state_var_modified(pointee_vec_idx); // #3138
                return true;
            };

            if let Some(updated) =
                ChcCtx::apply_projection_update(&root_in, &pointee_field_projs, rhs_expr)
            {
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, updated.clone(), out_sort, false)
                {
                    acc.replace_constraint(track_key, constraint);
                    self.encode.local_expr_env.insert(track_key, updated);
                    self.mark_state_var_modified(pointee_vec_idx);
                } else {
                    warn!(?local_idx, pointee_vec_idx, "CHC: arg-ref field store sort mismatch");
                    self.diagnostics.store_dropped_transition.inc();
                    self.mark_state_var_modified(pointee_vec_idx); // #3138
                }
                debug!(local_idx, pointee_vec_idx, "CHC: field Deref store via arg-ref (#2496)");
                return true;
            }
            // Part of #3144: apply_projection_update returned None — drop store.
            warn!(?local_idx, pointee_vec_idx, "CHC: arg-ref projection_update failed — dropped");
            self.diagnostics.store_dropped_transition.inc();
            self.mark_state_var_modified(pointee_vec_idx); // #3138
            return true;
        }

        // Part of #428: Handle deref store through static pointer locals.
        if let Some(&static_vec_idx) = self.ref_resolution.static_ref_to_state_idx.get(&local_idx) {
            let track_key = usize::MAX - static_vec_idx;
            let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(static_vec_idx)
            else {
                warn!(
                    ?local_idx,
                    static_vec_idx,
                    "CHC: dropped static deref store — missing output state var (#428)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark static modified-unconstrained (universally quantified)
                self.mark_state_var_modified(static_vec_idx);
                return true;
            };

            // D6: a pointer into a live static at an offset writes the PART
            // of the static its path names: the whole static's new value is
            // its current value updated along that path.
            let static_path = self.ref_resolution.static_ref_paths.get(&local_idx).cloned();
            let (out_name, out_sort) = (out_name.clone(), out_sort.clone());
            let new_whole = match &static_path {
                None => self.whole_static_scalar_store_value(
                    local_idx,
                    static_vec_idx,
                    rhs_expr.clone(),
                    &acc.modified,
                ),
                Some(path) if lhs.projection.len() == 1 => self
                    .static_state_current(static_vec_idx, &acc.modified)
                    .and_then(|current| Self::update_static_path(&current, path, rhs_expr.clone())),
                Some(_) => None,
            };
            let Some(new_whole) = new_whole else {
                // The part could not be updated: the static is havoced, and no
                // verdict rests on it (fail closed).
                debug!(local_idx, static_vec_idx, "CHC: static path store not encodable — havoc (D6)");
                let booked = self.record_sound_fallback_reason(
                    crate::codegen_ay::chc::decl::codegen_decl_static::CONST_PTR_INTO_LIVE_STATIC,
                );
                // A havoc must drop the block's EARLIER binding of the static's
                // output (an earlier `STATIC = v` in this block), or that stale
                // value survives the store it should forget — the same
                // discipline as `route_exact_static_store_stmt`.
                acc.replace_constraint(track_key, Expr::bool_const(true));
                self.encode.local_expr_env.remove(&track_key);
                self.mark_state_var_modified(static_vec_idx);
                acc.modified.insert(track_key);
                // The image follows the havocked state, or a raw read of it
                // still sees the initializer (`sync_static_image`).
                self.sync_static_image_or_fail_closed(static_vec_idx, Err(booked));
                return true;
            };
            let rhs_expr = new_whole;

            // Simple scalar store: *static_ptr = value
            if lhs.projection.len() == 1 {
                let out_var = Expr::var(&*out_name, out_sort.clone());
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, rhs_expr.clone(), &out_sort, false)
                {
                    acc.replace_constraint(track_key, constraint);
                    self.encode.local_expr_env.insert(track_key, rhs_expr.clone());
                    self.mark_state_var_modified(static_vec_idx);
                    acc.modified.insert(track_key);
                    // The store reaches the static's memory image too, which
                    // a raw read of the static selects (`store_static_image`):
                    // every view the entry rule seeded, not only an array's
                    // elements. `rhs_expr` is the WHOLE static's new value (D6
                    // updated it along the static place path when the pointer
                    // names a part), so the image is written at the static's
                    // own type; the pointee type is that type only when the
                    // pointer names the whole static.
                    let static_ty =
                        self.ref_resolution.static_state_ty.get(&static_vec_idx).copied().or_else(
                            || {
                                static_path.is_none().then(|| {
                                    Self::deref_pointee_ty(self.body.locals()[local_idx].ty)
                                })?
                            },
                        );
                    let placed = static_ty.is_some_and(|static_ty| {
                        self.store_static_image(static_vec_idx, static_ty, &rhs_expr)
                    });
                    if !placed {
                        warn!(
                            ?local_idx,
                            static_vec_idx,
                            "CHC: store through a static not placed in its memory image — fail closed"
                        );
                        let booked = self.record_sound_fallback_reason(STATIC_ELEM_STORE_UNPLACED);
                        if let Some(static_ty) = static_ty
                            && let Some(elem_ty) = self.get_array_element_ty(static_ty)
                        {
                            self.overapproximate_memory_store_target(booked, elem_ty, None);
                        }
                    }
                    debug!(
                        local_idx,
                        static_vec_idx,
                        "CHC: emitted Reg-level scalar Deref store via static ref (#428)"
                    );
                    return true;
                }
                warn!(
                    ?local_idx,
                    static_vec_idx,
                    "CHC: static scalar deref store sort mismatch — constraint dropped (#428)"
                );
                let booked = self.diagnostics.book_store_dropped();
                // Part of #3138: mark static modified-unconstrained (universally quantified)
                self.mark_state_var_modified(static_vec_idx);
                self.sync_static_image_or_fail_closed(static_vec_idx, Err(booked));
                return true;
            }

            // Element store through a static array: `G[i] = v` lowers to
            // `(*_p)[_i] = v` with `_p` the static's address. The read of
            // `G[i]` selects the static's array state variable
            // (`resolve_static_ref_root_expr`), so the store updates that
            // variable at the index. It used to fall through to the
            // projection fallback, which havocked `_p` and lost the write:
            // `G[3] = 99; assert!(G[3] == 4)` was proved from a false error
            // obligation (lost_deref_elem_store_dual.rs).
            if lhs.projection.len() == 2
                && matches!(
                    lhs.projection[1],
                    ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                )
                && let Some(arr) = out_sort.array_sort().cloned()
            {
                let out_sort = out_sort.clone();
                let out_var = Expr::var(&*out_name, out_sort.clone());
                let modified = acc.modified.clone();
                let root = self.resolve_static_ref_root_expr(local_idx, &modified);
                let index = self.resolve_index_expr(&lhs.projection[1], acc);
                let index_width = arr.index_sort.bitvec_width();
                // A struct element is held flattened in the array
                // (`flatten_dt_array_element`): store it the same way.
                let elem_value = if rhs_expr.sort().is_datatype()
                    && let Some(width) = arr.element_sort.bitvec_width()
                    && let Some(flat) =
                        crate::codegen_ay::types::flatten_datatype_to_bitvec(&rhs_expr, width)
                {
                    self.declare_datatype_sort_if_needed(rhs_expr.sort());
                    flat
                } else {
                    rhs_expr.clone()
                };
                // The state variable holds the STATIC's value: a pointer to
                // another type of the same bytes (a `MaybeUninit<[u16; 2]>`
                // static written through `as_mut_ptr() -> *mut [u16; 2]`)
                // indexes the content, which the static's reads
                // (`assume_init`, its memory image under the wrapper's key) do
                // not see. The lazy-init pattern was certified a Genuine
                // failure (review of fix/chc-lost-writes, lostwrite round 1,
                // finding 1); such a store is not placed. The pointer names the
                // static WHOLE only at the static's own type, up to regions, as
                // the static place path (D6) decides it.
                let pointee_is_static = Self::deref_pointee_ty(self.body.locals()[local_idx].ty)
                    .zip(self.ref_resolution.static_state_ty.get(&static_vec_idx).copied())
                    .is_some_and(|(pointee, static_ty)| {
                        crate::codegen_ay::chc::decl::static_path::same_ty_modulo_regions(
                            self.resolve_body_ty(pointee),
                            static_ty,
                        )
                    });
                if let (Some(root), Some(index), Some(index_width)) = (root, index, index_width)
                    && pointee_is_static
                    && *root.sort() == out_sort
                    && *elem_value.sort() == arr.element_sort
                {
                    let index =
                        coerce_bitvec_width_safe(index, index_width, SignExtension::ZeroExtend);
                    let updated = root.store(index.clone(), elem_value);
                    if let Some(constraint) =
                        coerce_eq_constraint(&out_var, updated.clone(), &out_sort, false)
                    {
                        acc.replace_constraint(track_key, constraint);
                        self.encode.local_expr_env.insert(track_key, updated);
                        self.mark_state_var_modified(static_vec_idx);
                        acc.modified.insert(track_key);
                        // The static's memory image, which a raw read of the
                        // static selects, takes the element too
                        // (`store_static_array_element_image`); when it cannot,
                        // the image is stale and no verdict may rest on it.
                        let array_ty = Self::deref_pointee_ty(self.body.locals()[local_idx].ty);
                        let placed = array_ty.is_some_and(|array_ty| {
                            self.store_static_array_element_image(
                                static_vec_idx,
                                array_ty,
                                index,
                                &rhs_expr,
                            )
                        });
                        if !placed {
                            warn!(
                                ?local_idx,
                                static_vec_idx,
                                "CHC: element store through a static array not placed in its memory image — fail closed"
                            );
                            let booked =
                                self.record_sound_fallback_reason(STATIC_ELEM_STORE_UNPLACED);
                            if let Ok(elem_ty) = lhs.ty(self.body.locals()) {
                                self.overapproximate_memory_store_target(booked, elem_ty, None);
                            }
                        }
                        debug!(
                            local_idx,
                            static_vec_idx, "CHC: element store through a static array (#428)"
                        );
                        return true;
                    }
                }
                // Not placeable: the static takes a free value, and no proof
                // or certified counterexample may rest on it.
                warn!(
                    ?local_idx,
                    static_vec_idx,
                    "CHC: element store through a static array not placeable — havoc the static"
                );
                self.diagnostics.store_dropped_transition.inc();
                self.mark_state_var_modified(static_vec_idx);
                acc.modified.insert(track_key);
                self.encode.local_expr_env.remove(&track_key);
                let booked = self.record_sound_fallback_reason(STATIC_ELEM_STORE_UNPLACED);
                self.sync_static_image_or_fail_closed(static_vec_idx, Err(booked));
                return true;
            }

            // Field store through static: *static_ptr.field = value
            // Not yet needed for COUNTER += 1 pattern but handled for completeness.
            debug!(
                ?local_idx,
                static_vec_idx,
                num_projs = lhs.projection.len(),
                "CHC: static deref store with field projections — not yet handled (#428)"
            );
            return false;
        }

        let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx).cloned() else {
            return false;
        };

        // A store through a pointer of ANOTHER type into an enum (`*(&mut f
        // as *mut F as *mut u8) = x`) writes the tag byte, which the handlers
        // below cannot express: a whole-value store decomposed the `u8` as the
        // payload of `F::A`, so an invalid tag read back as a valid variant,
        // and a tag byte written into an `Option<u8>` was read as its
        // payload. Kani's "unreachable code" and the `o.is_some()` assertion
        // failed where these verified clean (walker fail-closed repair round
        // 5, `walker_invalid_enum_dual.rs`, the three statement-path rows).
        // The target is left unconstrained and the store fails closed.
        if lhs.projection.len() == 1 && deref_store_puns_an_enum(self.body.locals(), lhs, &ref_target) {
            warn!(
                ref_local = local_idx,
                ?ref_target,
                "CHC: a store of another type through a pointer into an enum — fail closed"
            );
            self.record_sound_fallback_reason("deref_store_type_punned_into_enum");
            self.projection_sound_fallback(
                ref_target.local,
                "deref_store_type_punned_into_enum",
                acc,
            );
            return true;
        }

        // A store through a POINTER CAST to a type of the same size writes the
        // target's bytes as that type (`*(&mut w as *mut Words as *mut u128) =
        // v`): the value read back in the target's layout, or a fresh target
        // (`ChcCtx::ref_store_reinterpretation`). The u128 was decomposed into
        // the struct's slots as if it were the struct, and only the first slot
        // took it: `w.hi` kept its old value (review probe p1_ptr_cast.rs,
        // `write_through_safe` FAILED certified Genuine).
        let (ref_target, rhs_expr) = match self.ref_store_reinterpretation(
            &ref_target,
            lhs,
            &rhs_expr,
            local_idx,
            acc.modified,
        ) {
            RefStoreReinterpretation::SameType => (ref_target, rhs_expr),
            RefStoreReinterpretation::Converted(value) => (ref_target, value),
            // A wider store inside the containing local: the WHOLE local's new
            // value (`ref_store_reinterpretation` requires a store with no
            // projection past the deref).
            RefStoreReinterpretation::ConvertedLocal(value) => {
                (super::RefTarget::with_projections(ref_target.local, Vec::new()), value)
            }
            RefStoreReinterpretation::OutOfBounds => {
                self.record_block_violation(
                    Expr::bool_const(true),
                    super::codegen_stmt_store::OUT_OF_BOUNDS_MESSAGE,
                );
                return true;
            }
            RefStoreReinterpretation::Unmodeled(why) => {
                warn!(ref_local = local_idx, why, "CHC: pointer-cast store not modeled");
                // A store through a heap owner's buffer pointer does not land in
                // the owner local this havocs: havocking it is no
                // over-approximation of the store, so no proof may rest on it.
                let reason = if self.ref_target_is_foreign_heap_owner(local_idx) {
                    "store_through_heap_owner_pointer_unplaced"
                } else {
                    "transmute_layout_fallback"
                };
                self.havoc_local_fail_closed(ref_target.local, reason, acc);
                return true;
            }
        };

        let index_proj = ref_target
            .projections
            .iter()
            .find(|p| matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }));

        // Part of #3041/#3223: Collect Field projections after the first Index/ConstantIndex.
        let after_index_start = ref_target
            .projections
            .iter()
            .position(|p| {
                matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
            })
            .map(|i| i + 1)
            .unwrap_or(ref_target.projections.len());
        let mut field_projs = collect_field_projections(
            &ref_target.projections[after_index_start..],
            UnknownProjectionPolicy::Skip,
        );

        // The LHS's OWN post-deref projections are part of the store place and
        // the element handlers below never see `lhs`: passing only the
        // ref_target's post-index fields DROPPED them. `let p = &mut a[1];
        // p.x = 9;` has ref_target `a[1]` and store place `(*p).x`, so the `.x`
        // was lost and `assert!(a[1].x == 0)` verified SUCCESSFUL with
        // `[AY:PROOF_QUALIFIERS:clean]` — a false proof of the commonest way
        // there is to mutate an array of structs (adversarial review of
        // m3/soundness-fixes-2, 2026-09-14; pre-existing on main).
        // A ref_target with FIELDS BEFORE its index (`&mut g.buf[1]`) is routed
        // to the aggregate-root handler, which does not take `field_projs` at
        // all, so the LHS fields would be dropped there too.
        // A projection after the ref_target's index that is NOT a field — a
        // SECOND index (`&mut g[1][0].x`), a dereference — names a sub-place no
        // handler below encodes, and `collect_field_projections(.., Skip)`
        // above skipped it silently: the store then landed on `g[1]`'s field 0
        // and `assert!(g[1][0].x == 0)` stayed provable (fifth adversarial
        // review of m3/soundness-fixes-2, 2026-09-14, defects R3/R4, the 2-D
        // shape). Dropping a projection is a false proof; fail closed instead.
        if index_proj.is_some()
            && ref_target.projections[after_index_start..]
                .iter()
                .any(|p| !matches!(p, ProjectionElem::Field(..) | ProjectionElem::Downcast(_)))
        {
            warn!(
                ref_local = local_idx,
                ?ref_target,
                "CHC: sub-place under a referenced element is not encodable — fail closed"
            );
            self.record_sound_fallback_reason("store_nested_under_referenced_element");
            self.projection_sound_fallback(
                ref_target.local,
                "store_nested_under_referenced_element",
                acc,
            );
            return true;
        }
        let target_has_pre_index_fields = after_index_start > 1;
        if index_proj.is_some() && lhs.projection.len() > 1 {
            let tail = &lhs.projection[1..];
            if !target_has_pre_index_fields
                && tail
                    .iter()
                    .all(|p| matches!(p, ProjectionElem::Field(..) | ProjectionElem::Downcast(_)))
            {
                field_projs
                    .extend(collect_field_projections(tail, UnknownProjectionPolicy::Break));
            } else {
                // A further index or dereference after the referenced element:
                // no handler below encodes it, and dropping it is a false proof.
                warn!(
                    ?lhs,
                    "CHC: store nested under a referenced element is not encodable — fail closed"
                );
                self.record_sound_fallback_reason("store_nested_under_referenced_element");
                self.projection_sound_fallback(
                    ref_target.local,
                    "store_nested_under_referenced_element",
                    acc,
                );
                return true;
            }
        }
        let field_projs = field_projs;

        if let Some(index_proj) = index_proj {
            if let Some(&pointee_vec_idx) =
                self.ref_resolution.ref_arg_pointee_idx.get(&ref_target.local)
            {
                // Derived refs rooted in argument refs must update the pointee
                // array state var, not the pointer-typed argument slot (#3586).
                return self.handle_deref_store_array_arg_ref(
                    rhs_expr,
                    local_idx,
                    pointee_vec_idx,
                    index_proj,
                    &field_projs,
                    acc,
                );
            }
            // Part of #3816: pre-Index fields → aggregate root.
            let index_position = after_index_start.saturating_sub(1);
            let pre_idx = collect_field_projections(
                &ref_target.projections[..index_position],
                UnknownProjectionPolicy::Skip,
            );
            if !pre_idx.is_empty() {
                // The post-index fields travel with the call: they name a slot
                // INSIDE the element, and the handler applies them there.
                if let Some(r) = self.handle_lhs_index_through_ref_target_projs(
                    &rhs_expr,
                    local_idx,
                    &ref_target,
                    index_proj,
                    &field_projs,
                    acc,
                ) {
                    return r;
                }
                warn!(
                    ref_local = local_idx,
                    n = pre_idx.len(),
                    "CHC: aggregate-root ref_target array store fell through (#3816)"
                );
            }
            return self.handle_deref_store_array_via_ref_targets(
                rhs_expr,
                local_idx,
                &ref_target,
                index_proj,
                &field_projs,
                acc,
            );
        }
        // Part of #3041: Category D — route Deref+Index stores through ref_target projs.
        // The LHS's own projections AFTER its index name a slot inside the
        // element (`(*p).a[1].x = 9`): they are carried to the handler, which
        // applies them to the element. Dropping them was a false proof of the
        // same family as R3.
        if let Some(pos) = lhs.projection[1..]
            .iter()
            .position(|p| matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }))
        {
            let idx_proj = &lhs.projection[1 + pos];
            let lhs_tail = &lhs.projection[1 + pos + 1..];
            if lhs_tail
                .iter()
                .any(|p| !matches!(p, ProjectionElem::Field(..) | ProjectionElem::Downcast(_)))
            {
                warn!(
                    ?lhs,
                    "CHC: store nested under an indexed element of a referenced place is not \
                     encodable — fail closed"
                );
                self.record_sound_fallback_reason("store_nested_under_referenced_element");
                self.projection_sound_fallback(
                    ref_target.local,
                    "store_nested_under_referenced_element",
                    acc,
                );
                return true;
            }
            let lhs_tail_projs =
                collect_field_projections(lhs_tail, UnknownProjectionPolicy::Break);
            if let Some(h) = self.handle_lhs_index_through_ref_target_projs(
                &rhs_expr,
                local_idx,
                &ref_target,
                idx_proj,
                &lhs_tail_projs,
                acc,
            ) {
                return h;
            }
        }

        let target_local = ref_target.local;
        // Part of #3768: graceful fallback instead of panic
        let Some(target_vec_idx) = self.try_state_idx_for_local(target_local) else {
            warn!(
                ?target_local,
                ?local_idx,
                "CHC: deref store target not in state map — sound fallback"
            );
            self.record_sound_fallback_reason("state_idx_missing_deref_store_target");
            return false;
        };

        // Part of #3041/#3223: Track Downcast projections as cons_idx on subsequent Field.
        let mut combined_field_projs =
            collect_field_projections(&ref_target.projections, UnknownProjectionPolicy::Skip);
        combined_field_projs.extend(collect_field_projections(
            &lhs.projection[1..],
            UnknownProjectionPolicy::Break,
        ));

        // A whole-value store into a FLATTENED target (`*p = None` through
        // `p = &mut o`, `o: Option<u8>` held as `(is_some, value)` slots): the
        // stored datatype value is decomposed into the slots, as an assignment
        // to the local would be. Constraining the first slot with the whole value
        // was a sort mismatch; the store was dropped and a true `o == None` after
        // it failed (review major 1, deref_store_then_eq_safe).
        if combined_field_projs.is_empty()
            && self.flatten.flattened_tuple_locals.contains(&target_local)
            && let Some(slot_constraints) =
                self.build_flattened_destination_field_constraints(target_local, rhs_expr.clone())
        {
            for (slot, constraint) in slot_constraints {
                let key = self.flattened_field_constraint_key(target_local, slot);
                acc.replace_constraint(key, constraint);
            }
            self.encode.local_expr_env.remove(&target_local);
            acc.modified.insert(target_local);
            self.refresh_ref_target_memory_image(target_local, &rhs_expr, acc);
            self.clear_replaced_pointer_metadata(target_local);
            debug!(
                target_local,
                ref_local = local_idx,
                "CHC: emitted Reg-level flattened Deref store via ref_targets"
            );
            return true;
        }

        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(target_vec_idx)
        else {
            warn!(
                ?target_local,
                ?local_idx,
                "CHC: dropped Deref store via ref_targets — missing output state var (Part of #2236)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return true;
        };
        let out_var = Expr::var(&**out_name, out_sort.clone());

        if combined_field_projs.is_empty()
            && self.flatten.flattened_tuple_locals.contains(&target_local)
        {
            return self.store_whole_value_into_flattened_local(
                target_local,
                local_idx,
                rhs_expr,
                acc,
            );
        }

        if combined_field_projs.is_empty() {
            if let Some(constraint) =
                coerce_eq_constraint(&out_var, rhs_expr.clone(), out_sort, false)
            {
                acc.replace_constraint(target_local, constraint);
                self.encode.local_expr_env.insert(target_local, rhs_expr.clone());
                acc.modified.insert(target_local);
                self.refresh_ref_target_memory_image(target_local, &rhs_expr, acc);
                self.clear_replaced_pointer_metadata(target_local);
                debug!(
                    target_local,
                    ref_local = local_idx,
                    "CHC: emitted Reg-level scalar Deref store via ref_targets"
                );
                return true;
            }
            warn!(
                target_local,
                ref_local = local_idx,
                "CHC: ref_targets scalar deref store sort mismatch — constraint dropped"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return true;
        }

        let root_in = if acc.modified.contains(&target_local) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&target_local) {
                env_expr.clone()
            } else {
                Expr::var(&**out_name, out_sort.clone())
            }
        } else {
            self.state_var_mgr.state_vars.get(target_vec_idx).map_or_else(
                || Expr::var(&**out_name, out_sort.clone()),
                |(n, s)| Expr::var(&**n, s.clone()),
            )
        };

        if let Some(updated) =
            ChcCtx::apply_projection_update(&root_in, &combined_field_projs, rhs_expr)
        {
            if let Some(constraint) =
                coerce_eq_constraint(&out_var, updated.clone(), &out_sort, false)
            {
                acc.replace_constraint(target_local, constraint);
                self.encode.local_expr_env.insert(target_local, updated.clone());
                acc.modified.insert(target_local);
                self.refresh_ref_target_memory_image(target_local, &updated, acc);
                self.clear_replaced_pointer_metadata(target_local);
            } else {
                warn!(
                    target_local,
                    ref_local = local_idx,
                    num_field_projs = combined_field_projs.len(),
                    "CHC: deref field store sort mismatch — constraint dropped"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark target modified-unconstrained (universally quantified)
                acc.modified.insert(target_local);
            }
            debug!(
                target_local,
                ref_local = local_idx,
                num_field_projs = combined_field_projs.len(),
                "CHC: emitted Reg-level field Deref store via ref_targets"
            );
            return true;
        }
        // Part of #3148: Return false so the #2967 flattened-ref_target fallback
        // in encode_projection_assignment can handle this store.
        debug!(
            target_local,
            ref_local = local_idx,
            num_field_projs = combined_field_projs.len(),
            "CHC: apply_projection_update failed for Deref field store — deferring to fallback"
        );
        false
    }

    fn handle_deref_store_array_via_ref_targets(
        &mut self,
        rhs_expr: Expr,
        ref_local: usize,
        ref_target: &super::RefTarget,
        index_proj: &ProjectionElem,
        field_projs: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        self.handle_deref_store_array_via_ref_targets_impl(
            rhs_expr,
            ref_local,
            ref_target,
            index_proj,
            field_projs,
            acc,
        )
    }

    fn handle_deref_store_array_arg_ref(
        &mut self,
        rhs_expr: Expr,
        local_idx: usize,
        pointee_vec_idx: usize,
        index_proj: &ProjectionElem,
        field_projs: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        self.handle_deref_store_array_arg_ref_impl(
            rhs_expr,
            local_idx,
            pointee_vec_idx,
            index_proj,
            field_projs,
            acc,
        )
    }
}

// handle_collection_mut_ref_store is in codegen_stmt_store_ref_collection.rs
// (extracted per #3348, file size limit).

/// Does the whole-value store `*p = ..` (`lhs` is `*p`) write a type other
/// than the one `p` points at, into a target that is an enum (a pointer cast
/// between the borrow and the store)?
fn deref_store_puns_an_enum(
    locals: &[rustc_public::mir::LocalDecl],
    lhs: &Place,
    ref_target: &super::RefTarget,
) -> bool {
    use rustc_public::ty::{AdtKind, RigidTy, TyKind};
    // `Place::ty` indexes the locals: a place naming no local of this body
    // (a reference target recorded for another body, a synthetic one) has no
    // type to compare, and the store is not judged a pun here.
    if locals.get(lhs.local).is_none() || locals.get(ref_target.local).is_none() {
        return false;
    }
    let Ok(stored_ty) = lhs.ty(locals) else {
        return false;
    };
    let target_place = Place { local: ref_target.local, projection: ref_target.projections.clone() };
    let Ok(target_ty) = target_place.ty(locals) else {
        return false;
    };
    if stored_ty == target_ty {
        return false;
    }
    matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == AdtKind::Enum)
}
