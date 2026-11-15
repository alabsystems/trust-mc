// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Collection shadow state propagation for simple (non-projection) assignments.
//! Extracted from codegen_stmt_assign_simple.rs per #3952.
//!
//! Handles propagation of collection ghost state (present, len, cap) through
//! Move/Copy assignments, struct field projections, ADT aggregates, and
//! Ref/AddressOf rvalues.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::mir::{Operand, ProjectionElem, Rvalue};

use super::ChcCtx;
use super::stmt_accumulator::StmtAccumulator;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Propagate collection shadow state through a simple assignment.
    ///
    /// Covers Move/Copy (direct and projected), ADT Aggregate operands,
    /// and Ref/AddressOf collection references.
    pub(in crate::codegen_ay::chc) fn apply_collection_propagation(
        &mut self,
        rhs: &Rvalue,
        rhs_expr: &Expr,
        local_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        // Part of #3057: Propagate collection shadow state (present, len, cap)
        // for Move/Copy assignments.
        if let Rvalue::Use(Operand::Copy(src_place) | Operand::Move(src_place), ..) = rhs {
            if src_place.projection.is_empty() {
                let src_local: usize = src_place.local;
                self.propagate_collection_shadow_state(src_local, local_idx, acc.constraints);
            } else {
                // Part of #3284: Propagate collection ghost state through
                // struct field projections.
                let has_deref =
                    src_place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref));
                let (resolved_src_local, resolved_field_idx) = if has_deref {
                    if let Some(rt) = self.ref_resolution.ref_targets.get(&local_idx).cloned() {
                        let field_idx = rt.projections.iter().find_map(|p| {
                            if let ProjectionElem::Field(idx, _) = p { Some(*idx) } else { None }
                        });
                        (rt.local, field_idx)
                    } else {
                        let resolved_local = self
                            .ref_resolution
                            .ref_targets
                            .get(&src_place.local)
                            .map_or(src_place.local, |rt| rt.local);
                        let field_idx = src_place.projection.iter().find_map(|p| {
                            if let ProjectionElem::Field(idx, _) = p { Some(*idx) } else { None }
                        });
                        (resolved_local, field_idx)
                    }
                } else {
                    let field_idx = src_place.projection.iter().find_map(|p| {
                        if let ProjectionElem::Field(idx, _) = p { Some(*idx) } else { None }
                    });
                    (src_place.local, field_idx)
                };

                if let Some(field_idx) = resolved_field_idx {
                    self.propagate_collection_ghost_through_projection(
                        local_idx,
                        rhs_expr,
                        resolved_src_local,
                        field_idx,
                        acc.modified,
                        acc.constraints,
                    );
                }
            }
        }

        // Part of #3348: Propagate collection presence/len/cap aliases from
        // ADT Aggregate operands.
        if let Rvalue::Aggregate(rustc_public::mir::AggregateKind::Adt(_, _, _, _, _), operands) =
            rhs
        {
            self.propagate_collection_presence_from_aggregate(local_idx, operands);
        }

        // Part of #3284: For Ref/AddressOf producing a &Vec (or similar
        // collection reference) from a field inside a flattened struct,
        // propagate ghost vars using ref_targets resolution.
        if matches!(rhs, Rvalue::Ref(..) | Rvalue::AddressOf(..)) {
            if self.collections.len_state.get_len_var(local_idx).is_some() {
                if let Some(rt) = self.ref_resolution.ref_targets.get(&local_idx).cloned() {
                    let field_idx = rt.projections.iter().find_map(|p| {
                        if let ProjectionElem::Field(idx, _) = p { Some(*idx) } else { None }
                    });
                    if let Some(field_idx) = field_idx {
                        self.propagate_collection_ghost_through_projection(
                            local_idx,
                            rhs_expr,
                            rt.local,
                            field_idx,
                            acc.modified,
                            acc.constraints,
                        );
                    }
                }
            }
        }
    }

    /// A whole-value store through a reference into a collection
    /// (`*r = vec![1, 2, 3]` with `r = &mut v`): the collection's length,
    /// capacity and presence live in side state keyed by the target local,
    /// which the deref store handlers never touched, so `v.len()` read the
    /// value before the store and `assert!(v.len() == 0)` verified clean where
    /// Kani fails, while the true `v.len() == 3` was certified a Genuine
    /// failure (walker fail-closed review 6 round 3, `q1_md_writes.rs`
    /// `p1` / `p2`; `tools/soundness-duals/deref_collection_store_dual.rs`).
    ///
    /// Fails closed (`deref_store_collection_side_state_unmodelled`) where the
    /// target carries such side state, or cannot be named and is a collection.
    /// Propagating the stored local's side state was measured and rejected:
    /// the stored temporary's (`vec![..]`'s `into_vec` result) is not live
    /// across the blocks between, and the propagated length read 0.
    pub(in crate::codegen_ay::chc) fn sync_collection_side_state_through_deref(
        &mut self,
        lhs: &rustc_public::mir::Place,
        _rhs: &Rvalue,
        _acc: &mut StmtAccumulator<'_>,
    ) {
        if !lhs.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
            return;
        }
        // A store whose place goes on past the deref (`(*r).v = vec![1, 2, 3]`
        // with `r = &mut s`), or that stores a value holding a collection
        // (`*r = S { v: vec![..] }`), writes the target's memory image, while
        // the collection's length is read from the target's own state (the
        // struct-embedded path of `Vec::len`): `s.v.len() == 0` verified clean
        // where Kani fails (walker fail-closed repair round 4, finding 7's
        // class, `r3_vec_through_ref.rs` `d5`, `r5_vec_field_store.rs` `f4`,
        // `r6_bmc_field_stale.rs` `s4`).
        let stored_holds_collection = lhs
            .ty(self.body.locals())
            .is_ok_and(|ty| crate::codegen_ay::chc::stmt::ty_holds_collection(ty, 0));
        if lhs.projection.len() != 1 || !matches!(lhs.projection[0], ProjectionElem::Deref) {
            if stored_holds_collection {
                tracing::debug!(
                    ?lhs,
                    "CHC: store through a reference of a value holding a collection"
                );
                self.record_sound_fallback_reason("deref_store_collection_side_state_unmodelled");
            }
            return;
        }
        let target = self
            .ref_resolution
            .ref_targets
            .get(&lhs.local)
            .filter(|rt| rt.projections.is_empty())
            .map(|rt| rt.local);
        // A pointer into a `Vec`'s or `String`'s heap buffer (`v.as_mut_ptr()`,
        // and the casts and steps of it that `pointer_addresses_vec_buffer`
        // follows) names the OWNER in `ref_targets`, not the allocation it
        // addresses. A store through it writes an element of the buffer, never
        // the owner's length, capacity or presence. A later read of the owner's
        // model is the Vec-buffer rule's (`vec_model_read_after_buffer_write`),
        // and a stored value that holds a collection still fails closed below.
        // Without this, `*p = 5` for `p = v.as_mut_ptr()` failed closed here and
        // four rows fix/chc-false-certificates proves (`safe_moved_store`,
        // `safe_moved_vec_ptr_write_call`, `safe_store_then_len`,
        // `safe_store_then_raw_read`) failed on the merge with main.
        let writes_owner_buffer = target.is_some() && self.pointer_addresses_vec_buffer(lhs.local);
        let target_has_side_state = !writes_owner_buffer
            && target.is_some_and(|t| {
                self.collections.len_state.get_len_var(t).is_some()
                    || self.collections.len_state.get_cap_var(t).is_some()
                    || self.collections.len_state.get_present_var(t).is_some()
            });
        let lhs_is_collection = lhs.ty(self.body.locals()).is_ok_and(|ty| {
            use rustc_public::CrateDef;
            use rustc_public::ty::{RigidTy, TyKind};
            let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
                return false;
            };
            let name = def.name();
            matches!(
                name.rsplit("::").next().unwrap_or(&name),
                "Vec"
                    | "String"
                    | "VecDeque"
                    | "HashMap"
                    | "HashSet"
                    | "BTreeMap"
                    | "BTreeSet"
                    | "BinaryHeap"
            )
        });
        if !(target_has_side_state
            || (target.is_none() && lhs_is_collection)
            || stored_holds_collection)
        {
            return;
        }
        tracing::debug!(
            ?lhs,
            ?target,
            "CHC: whole store through a reference into a collection — side state not modelled"
        );
        self.record_sound_fallback_reason("deref_store_collection_side_state_unmodelled");
    }
}

/// Does a value of type `ty` hold a collection whose length, capacity or
/// membership the CHC encoder keeps as side state (`Vec`, `String`,
/// `VecDeque`, the maps and sets, `BinaryHeap`), directly or in a field,
/// tuple element or array element? Through a reference or pointer it does
/// not (the store writes the pointer). Unknown shapes past the depth bound
/// count as holding one.
pub(in crate::codegen_ay::chc) fn ty_holds_collection(
    ty: rustc_public::ty::Ty,
    depth: usize,
) -> bool {
    use rustc_public::CrateDef;
    use rustc_public::ty::{RigidTy, TyKind};
    if depth > 6 {
        return true;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let name = def.name();
            let last = name.rsplit("::").next().unwrap_or(&name);
            if matches!(
                last,
                "Vec"
                    | "String"
                    | "VecDeque"
                    | "HashMap"
                    | "HashSet"
                    | "BTreeMap"
                    | "BTreeSet"
                    | "BinaryHeap"
            ) {
                return true;
            }
            if matches!(last, "Box" | "Rc" | "Arc" | "NonNull" | "PhantomData") {
                return false;
            }
            def.variants().iter().any(|variant| {
                variant.fields().iter().any(|field| {
                    // A field whose type does not instantiate may hold one.
                    crate::codegen_ay::shared::mono_ty::field_ty(field, &args)
                        .is_none_or(|field_ty| ty_holds_collection(field_ty, depth + 1))
                })
            })
        }
        TyKind::RigidTy(RigidTy::Tuple(elems)) => {
            elems.iter().any(|elem| ty_holds_collection(*elem, depth + 1))
        }
        TyKind::RigidTy(RigidTy::Array(elem, _)) => ty_holds_collection(elem, depth + 1),
        _ => false,
    }
}
