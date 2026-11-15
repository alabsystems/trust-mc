// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Projection assignment encoding for CHC block statements.
//!
//! Handles `_N.field = rhs` assignments including:
//! - Deref store at Mem level: `*ptr = value`, `(*ptr).field = value` (#905, #1100)
//! - Array element store via Index/ConstantIndex (#1739)
//! - Deref store at Reg level via ref_targets (#1957)
//! - Flattened tuple/enum field projection (#2214)
//! - Regular field projection with datatype functional update (#600)
//!
//! Extracted from codegen_stmt.rs to keep production LOC under 500.

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

use super::codegen_call_coerce::coerce_eq_constraint;
use super::codegen_decl_flatten::compute_nested_flat_slot;
use super::codegen_stmt_store_array::StmtStoreArray;
use super::codegen_stmt_store_ref::StmtStoreRef;
use super::codegen_types::CodegenTypes;
use super::stmt_accumulator::StmtAccumulator;
use super::{ChcCtx, FieldProjection, UnknownProjectionPolicy, collect_field_projections};

/// One projection element, reduced to the shape this decision needs. Keeps the
/// rule below testable without a rustc type context (`ProjectionElem::Field`
/// carries a `Ty`, which cannot be built outside one).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(in crate::codegen_ay::chc) enum ProjShape {
    Index,
    Other,
}

fn proj_shape(p: &ProjectionElem) -> ProjShape {
    match p {
        ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => ProjShape::Index,
        _ => ProjShape::Other, // external enum: ProjectionElem
    }
}

/// Does this store place NEST a projection under an element index in a shape no
/// handler can encode exactly? See the call site in `encode_projection_assignment`.
///
/// `real_deref` says the leading `Deref` is a genuine pointer indirection (some
/// range-lowered MIR carries a spurious one over a scalar local).
pub(in crate::codegen_ay::chc) fn store_nests_under_element_index(
    projection: &[ProjectionElem],
    real_deref: bool,
) -> bool {
    let shapes: Vec<ProjShape> = projection.iter().map(proj_shape).collect();
    store_nests_under_element_index_shape(&shapes, real_deref)
}

fn store_nests_under_element_index_shape(shapes: &[ProjShape], real_deref: bool) -> bool {
    let Some(first_idx) = shapes.iter().position(|p| *p == ProjShape::Index) else {
        return false;
    };
    let tail = &shapes[first_idx + 1..];
    tail.contains(&ProjShape::Index) || (real_deref && !tail.is_empty())
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Is `ty` a pointer, or a SHALLOW carrier of one?
    ///
    /// `mem::replace` of a `&mut T` stores a bare pointer; `Option::replace`
    /// stores an `Option<&mut T>`; `mem::swap` of two `Box`es stores a `Box`.
    /// All three rebind what the written storage points at. Bounded at depth 2
    /// plus an explicit list of the pointer wrappers, so `Vec` and `String`,
    /// whose raw pointer sits deeper and whose buffer identity this lane does
    /// not key on a points-at edge, do not arm the guard.
    pub(in crate::codegen_ay::chc) fn ty_carries_a_pointer_value(ty: rustc_public::ty::Ty) -> bool {
        Self::ty_carries_a_pointer_value_at(ty, 0)
    }

    fn ty_carries_a_pointer_value_at(ty: rustc_public::ty::Ty, depth: u32) -> bool {
        if depth > 2 {
            return false;
        }
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)) => true,
            TyKind::RigidTy(RigidTy::Tuple(tys)) => {
                tys.iter().any(|t| Self::ty_carries_a_pointer_value_at(*t, depth + 1))
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let name = def.name();
                let trimmed = def.trimmed_name();
                if matches!(
                    name.as_str(),
                    "std::boxed::Box"
                        | "alloc::boxed::Box"
                        | "std::rc::Rc"
                        | "alloc::rc::Rc"
                        | "std::sync::Arc"
                        | "alloc::sync::Arc"
                ) || trimmed == "NonNull"
                    || trimmed == "Unique"
                    || trimmed == "Box"
                {
                    return true;
                }
                def.variants().into_iter().any(|v| {
                    v.fields().into_iter().any(|f| {
                        mono_ty::field_ty(&f, &args)
                            .is_none_or(|t| Self::ty_carries_a_pointer_value_at(t, depth + 1))
                    })
                })
            }
            _ => false,
        }
    }

    /// Return whether a projection base local represents a real dereference.
    ///
    /// Mirrors `deref_pointee_ty` for pointer-like wrappers without emitting
    /// warnings on the scalar fast path probe logic.
    fn projection_base_supports_real_deref(local_ty: rustc_public::ty::Ty) -> bool {
        match local_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)) => true,
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                let wrapper_name = def.name();
                let trimmed_name = def.trimmed_name();
                matches!(
                    wrapper_name.as_str(),
                    "std::boxed::Box"
                        | "alloc::boxed::Box"
                        | "std::rc::Rc"
                        | "alloc::rc::Rc"
                        | "std::sync::Arc"
                        | "alloc::sync::Arc"
                ) || trimmed_name == "NonNull"
                    || trimmed_name == "Unique"
            }
            _ => false,
        }
    }

    /// Emit a sound over-approximation fallback for a projection assignment.
    ///
    /// Makes the local nondeterministic (universally quantified in CHC) and
    /// records a categorized sound_fallback counter for diagnostic triage.
    ///
    /// Part of #3561: extracted from 11 duplicate fallback sites.
    pub(super) fn projection_sound_fallback(
        &mut self,
        local_idx: usize,
        category: &'static str,
        acc: &mut StmtAccumulator<'_>,
    ) {
        acc.modified.insert(local_idx);
        acc.replace_constraint(local_idx, Expr::bool_const(true));
        self.record_sound_fallback_categorized(category);
    }

    /// Write a projected store of interior-mutable data to the place's memory
    /// image (see the call site in `encode_projection_assignment`). A store
    /// that cannot be mirrored exactly fails closed.
    fn mirror_interior_mut_projected_store(
        &mut self,
        lhs: &Place,
        rhs_expr: &Expr,
        acc: &mut StmtAccumulator<'_>,
    ) {
        let Ok(place_ty) = lhs.ty(self.body.locals()) else { return };
        let place_ty = self.resolve_body_ty(place_ty);
        if !self.ty_has_interior_mut(place_ty) {
            return;
        }
        if Self::translate_ty(place_ty).as_ref() != Some(rhs_expr.sort()) {
            self.record_sound_fallback_reason("interior_mut_projected_store_unmirrored");
            return;
        }
        let modified = acc.modified.clone();
        let Some(loc) = self.translate_ref_to_address(lhs, &modified) else {
            self.record_sound_fallback_reason("interior_mut_projected_store_unmirrored");
            return;
        };
        let addr = loc.into_expr();
        let prev_suppress = self.suppress_heap_store_checks;
        self.suppress_heap_store_checks = true;
        #[allow(deprecated)]
        if let Some(store) =
            self.build_memory_store_untyped(addr.clone(), rhs_expr.clone(), place_ty)
        {
            acc.constraints.push(store);
        }
        if rhs_expr.sort().is_datatype() {
            self.try_decompose_struct_store(&addr, rhs_expr, place_ty, acc.constraints);
        }
        self.suppress_heap_store_checks = prev_suppress;
        debug!(?lhs, "CHC: interior-mutable projected store mirrored to memory");
    }

    /// Encode a projection assignment (`_N.field = rhs`, `*ptr = rhs`, etc.).
    ///
    /// Dispatches to the appropriate handler for deref stores, array stores,
    /// flattened tuple fields, and datatype functional updates.
    pub(in crate::codegen_ay::chc) fn encode_projection_assignment(
        &mut self,
        lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        self.encode.local_signedness.remove(&local_idx);

        // Some range-lowered MIR paths materialize `(*x).0` where `x` is already a
        // scalar local (no actual pointer indirection). Treat this projection as an
        // identity assignment to avoid dropping the update.
        let local_ty = self.body.locals()[local_idx].ty;
        let lhs_has_deref = matches!(lhs.projection.first(), Some(ProjectionElem::Deref));
        let lhs_base_is_pointer = Self::projection_base_supports_real_deref(local_ty);
        let strip_spurious_deref = lhs_has_deref && !lhs_base_is_pointer;

        // Soundness: a raw-pointer deref STORE (`*p = v`, `(*p).field = v`)
        // carries a `p != 0` obligation no matter which store handler below
        // resolves it (Mem-level memory store, ref_targets, fallback, or
        // mem-promote retry). Mirrors the load-side hook at the top of
        // try_resolve_deref_cascade. The helper itself is a no-op for
        // non-raw-pointer bases and provably non-null pointers.
        if lhs_has_deref && lhs_base_is_pointer {
            self.emit_raw_ptr_null_deref_check(lhs, acc.modified);
            // A store through a raw pointer to a local whose storage is dead
            // (`{ let mut z = 0; p = &mut z; } *p = 1`): the load side has
            // failed such a dereference since #762, the store side wrote the
            // dead local's register and proved the program clean where Kani
            // reports a dangling write (self-review of round 10 of
            // fix/chc-false-certificates, `q_dangle.rs` dg01, dg03; the same on
            // main f5dfb8d48).
            self.push_dead_raw_target_check(lhs, acc.modified);
            self.emit_const_object_deref_bound_check(lhs, acc.modified);
            // A store through a pointer chosen on a path: the register and
            // memory lanes below resolve ONE referent (the producer encoded
            // last), so the store may miss the object it writes on another
            // path. No proof or certified counterexample may rest on it.
            if self.pointer_value_is_path_dependent(local_idx) {
                self.record_sound_fallback_reason("deref_through_path_merged_pointer");
            }
        }
        // A projection NESTED UNDER an element index that no handler below can
        // encode exactly. The handlers resolve ONE index and drop whatever
        // follows it: `handle_field_index_store` refuses a trailing projection
        // outright, and the ref_target route picks the FIRST index in
        // `lhs.projection[1..]` and ignores the rest. The store then lands
        // nowhere while the harness still claims a proof —
        // `let r: &mut [[u8; 2]; 2] = &mut g; r[i][1] = 9; assert!(g[i][1] == 0)`
        // verified SUCCESSFUL and `r[1].x = 9` certified a Genuine counterexample
        // for its safe twin (negative/ref_index_ops.rs, main 31793ccc3).
        //
        // Exactly two shapes are unencodable, and both fail closed here:
        //   * two element indices in one place (`(*r)[i][j]`, `g[i][j]`), and
        //   * anything after the index under a REAL dereference (`(*r)[i].x`).
        // `g[i].x = v` (index first, fields after, no dereference) IS exact —
        // `handle_array_element_store` rebuilds the element — and `s.buf[i] = v`
        // (index last) is exact too; neither is touched.
        if store_nests_under_element_index(&lhs.projection, lhs_has_deref && lhs_base_is_pointer) {
            warn!(?lhs, "CHC: store nested under an element index is not encodable — fail closed");
            self.record_sound_fallback_reason("store_nested_under_element_index");
        }
        // The same nesting with the element index in the REFERENT rather than
        // in the place: `let p = &mut a[1]; p.b[0] = 9;` is `[Deref, Field,
        // Index]` over a pointer whose ref_target is already `a[1]`, so the
        // rule above cannot see the outer index and no handler below resolves
        // both. The store landed nowhere and `assert!(a[1].b[0] == 0)` verified
        // SUCCESSFUL (adversarial review of m3/soundness-fixes-2, 2026-09-14).
        if lhs_has_deref
            && lhs_base_is_pointer
            && lhs.projection.len() > 1
            && lhs.projection[1..].iter().any(|p| {
                matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
            })
            && self.ref_resolution.ref_targets.get(&local_idx).is_some_and(|t| {
                t.projections.iter().any(|p| {
                    matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
                })
            })
        {
            warn!(
                ?lhs,
                "CHC: store nested under a REFERENCED element index is not encodable — fail closed"
            );
            self.record_sound_fallback_reason("store_nested_under_referenced_element");
        }

        // A POINTER VALUE stored THROUGH a dereference rebinds what the written
        // storage points at, and the points-at edges this lane keeps were
        // computed from the BORROWS in the body — they know nothing about a
        // pointer that travels through memory. `mem::replace`, `mem::take`,
        // `Option::replace` and `ptr::replace` are INLINED, so no call
        // terminator names them, and they all lower to exactly this store:
        // `let old = mem::replace(&mut a, &mut y); *old = 7; *a = 9;
        // assert!(y == 2)` verified SUCCESSFUL because `*a = 9` still resolved
        // through `a`'s PRE-CALL target (adversarial review of
        // m3/soundness-fixes-2, 2026-09-14; pre-existing on main). The written
        // storage's edge is dropped, so a later store through it is unresolved
        // and fails closed rather than writing the wrong object.
        if lhs_has_deref
            && lhs_base_is_pointer
            && lhs.projection.len() == 1
            && lhs.ty(self.body.locals()).is_ok_and(Self::ty_carries_a_pointer_value)
            && let Some(target) = self.ref_resolution.ref_targets.get(&local_idx).map(|t| t.local)
        {
            warn!(
                ?lhs,
                target,
                "CHC: a pointer stored through a dereference rebinds its target — fail closed"
            );
            // The REASON alone is what makes this fail closed: no proof over
            // this harness is clean and no counterexample through it is
            // certified. Dropping the target's points-at edge as well was
            // measured to cost 420s+ on
            // negative/frozen_views_indirect.rs::rc_cells_set_through_view_must_fail
            // (quick and decided on the pre-repair bundle) — the extra havoc
            // blew the search space up — for no soundness the reason does not
            // already give.
            let _ = target;
            self.record_sound_fallback_reason("pointer_stored_through_deref_rebinds_target");
        }

        // The same rebinding one step out: a pointer stored into an AGGREGATE
        // SLOT of a local (`h.p = &mut y`, `t.0 = &mut y`, `(*r).p = &mut y`).
        // The guard above covers a store THROUGH a dereference whose place is
        // exactly `[Deref]`; a field or element store is a different handler and
        // kept the stale points-at edge, so `*h.p = 9` afterwards wrote the OLD
        // target. `struct H { p: *mut u8 } let mut h = H { p: &mut x };
        // h.p = &mut y; *h.p = 9; assert!(y == 2)` verified SUCCESSFUL with
        // `[AY:PROOF_QUALIFIERS:clean]` and ZERO recorded drop reasons, and its
        // safe twin was FAILED [AY:CTREX_CAT:Genuine] (fourth adversarial review
        // of m3/soundness-fixes-2, 2026-09-14, defect M3/D4). The same shapes
        // through an array element, an `Option`, a call return and a branch join
        // already failed closed; this is the aggregate-slot hole.
        //
        // A store of a WHOLE local (`lhs.projection.is_empty()`) is not this
        // shape: the local's own edge is re-derived from the new value.
        if !lhs.projection.is_empty()
            && !(lhs_has_deref && lhs_base_is_pointer && lhs.projection.len() == 1)
            && lhs.ty(self.body.locals()).is_ok_and(Self::ty_carries_a_pointer_value)
        {
            warn!(
                ?lhs,
                "CHC: a pointer stored into an aggregate slot rebinds its target — fail closed"
            );
            self.record_sound_fallback_reason("pointer_stored_into_aggregate_rebinds_target");
        }

        // A projected write of interior-mutable data (`s.c = Cell::new(200)`,
        // `a[0] = Cell::new(200)`) must reach the local's memory image too:
        // the Cell lane reads and writes a cell at its memory-mirror address,
        // and a projected borrow (`&s.c`, the `get` receiver) never re-mirrors
        // the register. Updating only the register left an earlier `set`'s
        // value in memory, and `s.c.set(7); s.c = Cell::new(200);
        // assert!(s.c.get() < 100)` verified SUCCESSFUL clean (review of
        // fix/chc-cell-set-write, 2026-09-26).
        if !lhs_has_deref && !lhs.projection.is_empty() {
            self.mirror_interior_mut_projected_store(lhs, &rhs_expr, acc);
        }

        let scalar_deref_field_zero = matches!(
            lhs.projection.as_slice(),
            [ProjectionElem::Deref, ProjectionElem::Field(0, field_ty)] if *field_ty == local_ty
        ) && strip_spurious_deref;
        if scalar_deref_field_zero {
            // Part of #3768: graceful fallback instead of panic on unregistered locals
            let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
                self.projection_sound_fallback(local_idx, "state_idx_missing_scalar_deref", acc);
                return;
            };
            if let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
            {
                let out_var = Expr::var(&*out_name, out_sort.clone());
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, rhs_expr.clone(), &out_sort, false)
                {
                    self.encode.local_expr_env.insert(local_idx, rhs_expr);
                    acc.replace_constraint(local_idx, constraint);
                    acc.modified.insert(local_idx);
                } else {
                    warn!(
                        local_idx,
                        ?lhs,
                        "CHC: scalar deref-field projection sort mismatch — constraint dropped"
                    );
                    self.projection_sound_fallback(local_idx, "proj_sort_mismatch", acc);
                }
            } else {
                warn!(
                    local_idx,
                    vec_idx,
                    output_state_len = self.state_var_mgr.output_state_vars.len(),
                    "CHC: scalar deref-field projection missing output slot"
                );
                self.projection_sound_fallback(local_idx, "proj_missing_state_var", acc);
            }
            return;
        }

        let flattened_deref_field = self.flatten.flattened_tuple_locals.contains(&local_idx)
            && matches!(lhs.projection.first(), Some(ProjectionElem::Deref));
        let proj_slice = if flattened_deref_field || strip_spurious_deref {
            &lhs.projection[1..]
        } else {
            lhs.projection.as_slice()
        };

        // Flattened locals can appear with a no-op leading Deref after range lowering
        // (pattern: [Deref, Field(..)]). Handle this directly to avoid routing through
        // pointer-store handlers that expect pointer-typed base locals.
        if flattened_deref_field {
            let field_projections = collect_field_projections(
                proj_slice,
                UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
            );
            if field_projections.len() == 1 {
                self.encode_flattened_field_projection(
                    rhs_expr,
                    local_idx,
                    &field_projections[0],
                    acc,
                );
            } else {
                warn!(?lhs, "CHC: unsupported flattened deref projection — sound fallback");
                self.projection_sound_fallback(local_idx, "proj_unsupported_deref", acc);
            }
            return;
        }

        // Deref store at Mem level: *ptr = value, (*ptr).field = value (#1100)
        if !strip_spurious_deref
            && self.handle_deref_store_mem_level(lhs, &rhs_expr, local_idx, bb_idx, acc)
        {
            return;
        }

        // Array element store via Index/ConstantIndex (#1739)
        if self.handle_array_element_store(lhs, rhs_expr.clone(), local_idx, acc) {
            return;
        }

        // Part of #3561: Mixed Field+Index projection assignment (e.g., _N.data[i] = rhs).
        if self.handle_field_index_store(lhs, rhs_expr.clone(), local_idx, acc) {
            return;
        }

        // Deref store at Reg level via ref_targets (#1957)
        if !strip_spurious_deref
            && self.handle_deref_store_via_ref_targets(lhs, rhs_expr.clone(), local_idx, acc)
        {
            return;
        }

        // Part of #2967: Fallback for Deref+Field on pointer locals whose ref_target is
        // a flattened bv-encoded struct (e.g., std::slice::Iter/IterMut encoded as bv128).
        // The Mem-level handler defers when ref_targets exists (deref_mem.rs:64), and the
        // ref_targets handler fails because apply_projection_update can't handle bv128 sort.
        // Resolve through ref_targets and route to the flattened field projection path.
        //
        // Part of #3041: Use collect_field_projections_with_downcast to preserve Downcast
        // cons_idx in the projection chain, enabling correct payload slot resolution for
        // BV-flattened multi-ctor enums via EnumBvLayout.
        //
        // Part of #3041: Guard: skip this fallback when the LHS contains Index/ConstantIndex
        // after the Deref. Those patterns must be handled by handle_lhs_index_through_ref_target_projs
        // in the ref_targets handler above. Without this guard, the fallback drops the Index
        // projection and overwrites the whole payload field as a scalar.
        let lhs_has_index_after_deref = lhs.projection[1..]
            .iter()
            .any(|p| matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }));
        if lhs_base_is_pointer && lhs_has_deref && !lhs_has_index_after_deref {
            if let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx) {
                let target_local = ref_target.local;
                if self.flatten.flattened_tuple_locals.contains(&target_local) {
                    let mut combined_field_projs = collect_field_projections(
                        &ref_target.projections,
                        UnknownProjectionPolicy::Skip,
                    );
                    combined_field_projs.extend(collect_field_projections(
                        &lhs.projection[1..],
                        UnknownProjectionPolicy::Break,
                    ));
                    if combined_field_projs.len() == 1 {
                        debug!(
                            local_idx,
                            target_local,
                            field_idx = combined_field_projs[0].field_idx,
                            cons_idx = ?combined_field_projs[0].cons_idx,
                            "CHC: Deref+Field fallback to flattened ref_target (#2967)"
                        );
                        self.encode_flattened_field_projection(
                            rhs_expr,
                            target_local,
                            &combined_field_projs[0],
                            acc,
                        );
                        return;
                    }
                }
            }
        }

        // Real deref stores that survive the Reg-level handlers require the
        // Mem-level store path. Request a retry at Mem so `*box = ...` and
        // similar wrapper-backed writes do not fall through to projection
        // sound fallback.
        if lhs_has_deref
            && lhs_base_is_pointer
            && self.track_level < crate::args::ChcTrackLevel::Mem
        {
            self.needs_mem_promote = true;
            warn!(
                ?lhs,
                track_level = ?self.track_level,
                "CHC: deref store requires mem-track promotion"
            );
            return;
        }

        let field_projections = collect_field_projections(
            proj_slice,
            UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
        );

        // Part of #2214: Flattened locals (tuples, Option, Result) -
        // field projection assignment directly constrains the scalar
        // state var. For enums (Downcast+Field), cons_idx is Some
        // and payload is always at vec_idx + 1.
        if self.flatten.flattened_tuple_locals.contains(&local_idx) && field_projections.len() == 1
        {
            self.encode_flattened_field_projection(rhs_expr, local_idx, &field_projections[0], acc);
            return;
        }

        // Part of #2989: Multi-level field projections on recursively flattened locals.
        // For nested single-constructor ADTs, compute the leaf slot offset and write
        // directly to that scalar state var while preserving all other fields.
        if self.flatten.flattened_tuple_locals.contains(&local_idx)
            && field_projections.len() > 1
            && field_projections.iter().all(|fp| fp.cons_idx.is_none())
        {
            // The slot must be the one read case C reads: drop the same
            // sort-identity steps it drops (`t.0.c` on `t: (P,)` resolved
            // `[0, 1]` against P's sort, which is `inner.b`), and refuse the
            // paths it refuses. A write to an unfaithful slot landed on a
            // sibling: `o.k1.k2.k3.k4.y = v` on a five-level owner wrote `o.z`.
            let field_projections = match self
                .faithful_flat_field_path(local_idx, &field_projections)
            {
                Ok(path) => path,
                Err(why) => {
                    warn!(
                        ?lhs,
                        why, "CHC: nested flattened store has no faithful slot (fail closed)"
                    );
                    self.havoc_local_fail_closed(local_idx, "flat_nested_store_unfaithful", acc);
                    return;
                }
            };
            if let Some(local_decl) = self.body.locals().get(local_idx)
                && let Some(sort) = Self::translate_ty(local_decl.ty)
            {
                let field_indices: Vec<usize> =
                    field_projections.iter().map(|fp| fp.field_idx).collect();
                if let Some(leaf_slot) = compute_nested_flat_slot(&sort, &field_indices) {
                    self.encode_flattened_field_slot(rhs_expr, local_idx, leaf_slot, acc);
                    return;
                }
            }
            // Fall through to datatype functional update if slot computation fails.
        }

        if field_projections.is_empty() {
            // Other unsupported projection types
            warn!(?lhs, "CHC: unsupported projection type (no field projections) — sound fallback");
            self.projection_sound_fallback(local_idx, "proj_no_field_projections", acc);
            return;
        }

        // Part of #3041: Union field projection assignment (e.g., `u.g = 42`).
        // All union fields overlap at offset 0, so writing a field writes its
        // bytes into the low end of the union's bitvector, in memory order
        // (`codegen_stmt_union_bits.rs`). For ZST field writes (e.g.,
        // `u.f = ()`), the write is a no-op.
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = local_ty.kind() {
            if def.kind() == rustc_public::ty::AdtKind::Union {
                // Part of #3768: graceful fallback instead of panic
                let Some(proj_vec_idx) = self.try_state_idx_for_local(local_idx) else {
                    self.projection_sound_fallback(local_idx, "state_idx_missing_union_proj", acc);
                    return;
                };
                if let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(proj_vec_idx).cloned()
                {
                    // Check if the field being written is ZST.
                    let field_is_zst = field_projections
                        .last()
                        .and_then(|fp| fp.field_ty)
                        .and_then(|ty| ty.layout().ok())
                        .map(|l| l.shape().size.bytes() == 0)
                        .unwrap_or(false);

                    if field_is_zst {
                        // ZST field write is a no-op — union value unchanged.
                        debug!(local_idx, "CHC: union ZST field write — no-op");
                        return;
                    }

                    // Non-ZST field: the field's MEMORY image replaces the
                    // union's low bytes; the bytes past the field keep their
                    // value. A write into a field of the field (`u.q.b = v`)
                    // reads the field out of the union, updates it, and writes
                    // it back. The old coercion wrote the right-hand side over
                    // the WHOLE union, whatever the projection: `u.q.b = 1` made
                    // the union 1 (subfield_assign_bug SUCCESSFUL) and a narrow
                    // field zeroed the tail.
                    if let Some(target_width) = out_sort.bitvec_width()
                        && self.flat_union_width(local_ty) == Some(target_width)
                        && let Some(field_ty) = field_projections.first().and_then(|fp| fp.field_ty)
                    {
                        use super::codegen_stmt_union_bits::UnionLane;
                        let old = if acc.modified.contains(&local_idx) {
                            self.encode
                                .local_expr_env
                                .get(&local_idx)
                                .cloned()
                                .unwrap_or_else(|| Expr::var(&*out_name, out_sort.clone()))
                        } else {
                            match self.state_var_mgr.state_vars.get(proj_vec_idx) {
                                Some((in_name, in_sort)) => Expr::var(&**in_name, in_sort.clone()),
                                None => {
                                    self.projection_sound_fallback(
                                        local_idx,
                                        "state_idx_missing_union_proj",
                                        acc,
                                    );
                                    return;
                                }
                            }
                        };
                        let field_value = if field_projections.len() == 1 {
                            Some(rhs_expr)
                        } else {
                            match self.union_field_lane(&old, field_ty) {
                                UnionLane::Exact(current) if current.sort().is_datatype() => {
                                    Self::apply_projection_update(
                                        &current,
                                        &field_projections[1..],
                                        rhs_expr,
                                    )
                                }
                                _ => None,
                            }
                        };
                        let lane = match field_value {
                            Some(value) => self.union_bits_of_field_write(
                                Some(&old),
                                target_width,
                                field_ty,
                                &value,
                            ),
                            None => UnionLane::Unmodeled("union sub-field update not modeled"),
                        };
                        match lane {
                            UnionLane::Exact(bits) => {
                                let out_var = Expr::var(&*out_name, out_sort);
                                acc.replace_constraint(local_idx, out_var.eq(bits.clone()));
                                self.encode.local_expr_env.insert(local_idx, bits);
                                acc.modified.insert(local_idx);
                                debug!(
                                    local_idx,
                                    target_width, "CHC: union field write in memory order"
                                );
                            }
                            UnionLane::Unmodeled(why) => {
                                debug!(
                                    local_idx,
                                    why, "CHC: union field write not modeled; fresh union"
                                );
                                self.havoc_local_fail_closed(
                                    local_idx,
                                    "transmute_layout_fallback",
                                    acc,
                                );
                            }
                        }
                        return;
                    }
                    if let Some(target_width) = out_sort.bitvec_width() {
                        let coerced = coerce_bitvec_width_safe(
                            rhs_expr,
                            target_width,
                            SignExtension::ZeroExtend,
                        );
                        let out_var = Expr::var(&*out_name, out_sort);
                        acc.replace_constraint(local_idx, out_var.eq(coerced.clone()));
                        self.encode.local_expr_env.insert(local_idx, coerced);
                        acc.modified.insert(local_idx);
                        debug!(local_idx, target_width, "CHC: union field write — coerced to BV");
                        return;
                    }
                }
                // Fall through to datatype update if state var missing.
            }
        }

        // Regular field projection with datatype functional update
        self.encode_datatype_field_update(lhs, rhs_expr, local_idx, &field_projections, acc);
    }

    /// Encode a regular datatype field update via functional update.
    ///
    /// Resolves the root expression, applies `apply_projection_update`, and
    /// constrains the output variable with sort-safe equality.
    fn encode_datatype_field_update(
        &mut self,
        _lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        field_projections: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) {
        // Get the root expression, using expr env or OUTPUT for modified locals
        // Fix #2055: Check local_expr_env first
        // Fix #2238: Use local_to_state_idx mapping for correct vector index
        // Part of #3768: graceful fallback instead of panic
        let Some(proj_vec_idx) = self.try_state_idx_for_local(local_idx) else {
            self.projection_sound_fallback(local_idx, "state_idx_missing_dt_field_update", acc);
            return;
        };
        let root_in = if acc.modified.contains(&local_idx) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&local_idx) {
                env_expr.clone()
            } else {
                let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(proj_vec_idx)
                else {
                    warn!(
                        local_idx,
                        proj_vec_idx,
                        "CHC: datatype field update missing output state var — recording fallback"
                    );
                    // Local is already in `modified` (branch condition above);
                    // helper re-insert is a no-op.
                    self.projection_sound_fallback(local_idx, "proj_missing_state_var", acc);
                    return;
                };
                Expr::var(&**out_name, out_sort.clone())
            }
        } else {
            let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(proj_vec_idx) else {
                warn!(
                    local_idx,
                    proj_vec_idx,
                    "CHC: datatype field update missing input state var — recording fallback"
                );
                self.projection_sound_fallback(local_idx, "proj_missing_state_var", acc);
                return;
            };
            Expr::var(&**in_name, in_sort.clone())
        };

        let updated = if root_in.sort().is_bitvec() {
            let local_ty = self.body.locals()[local_idx].ty;
            Self::bv_projection_update(&root_in, local_ty, field_projections, rhs_expr.clone())
                .or_else(|| Self::apply_projection_update(&root_in, field_projections, rhs_expr))
        } else {
            Self::apply_projection_update(&root_in, field_projections, rhs_expr)
        };

        if let Some(updated_expr) = updated {
            // Get output variable for the root local
            if let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(proj_vec_idx)
            {
                let out_var = Expr::var(&**out_name, out_sort.clone());
                // Part of #2244: use coerce_eq_constraint for sort-safe
                // equality. Datatype field updates may produce a different
                // sort than the declared output variable.
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, updated_expr.clone(), out_sort, false)
                {
                    // Fix #2055: Record updated whole value in expression env
                    self.encode.local_expr_env.insert(local_idx, updated_expr);
                    // Fix #2055: Replace previous constraint for same local
                    acc.replace_constraint(local_idx, constraint);
                    acc.modified.insert(local_idx);
                } else {
                    warn!(
                        local_idx,
                        ?proj_vec_idx,
                        "CHC: datatype field update sort mismatch — constraint dropped"
                    );
                    self.projection_sound_fallback(local_idx, "proj_sort_mismatch", acc);
                }
            } else {
                warn!(
                    local_idx,
                    proj_vec_idx,
                    output_state_len = self.state_var_mgr.output_state_vars.len(),
                    "CHC: projection output slot missing — constraint dropped"
                );
                self.projection_sound_fallback(local_idx, "proj_missing_state_var", acc);
            }
        } else {
            warn!(
                local_idx,
                projection_depth = field_projections.len(),
                "CHC: apply_projection_update failed — constraint dropped"
            );
            self.projection_sound_fallback(local_idx, "proj_update_failed", acc);
        }
    }
}

#[cfg(test)]
mod nested_index_store_tests {
    use super::{
        ProjShape::Index, ProjShape::Other, store_nests_under_element_index_shape as nested,
    };

    #[test]
    fn plain_element_store_is_encodable() {
        // `a[i] = v` and `(*r)[i] = v`
        assert!(!nested(&[Index], false));
        assert!(!nested(&[Other, Index], true));
    }

    #[test]
    fn field_before_the_index_is_encodable() {
        // `s.buf[i] = v`, `(*r).buf[i] = v`
        assert!(!nested(&[Other, Index], false));
        assert!(!nested(&[Other, Other, Index], true));
    }

    #[test]
    fn field_after_the_index_on_a_local_is_encodable() {
        // `a[i].x = v` — handle_array_element_store rebuilds the element.
        assert!(!nested(&[Index, Other], false));
    }

    #[test]
    fn field_after_the_index_under_a_deref_fails_closed() {
        // `(*r)[1].x = v` — the ref_target route drops the field.
        assert!(nested(&[Other, Index, Other], true));
    }

    #[test]
    fn two_indices_fail_closed_with_or_without_a_deref() {
        // `g[i][j] = v` and `(*r)[i][j] = v`
        assert!(nested(&[Index, Index], false));
        assert!(nested(&[Other, Index, Index], true));
    }

    #[test]
    fn a_spurious_deref_over_a_scalar_does_not_fail_closed() {
        // Range-lowered MIR writes `(*x).0` where `x` is a scalar local.
        assert!(!nested(&[Other, Index, Other], false));
    }

    #[test]
    fn a_place_without_an_index_is_never_nested() {
        assert!(!nested(&[Other, Other], false));
        assert!(!nested(&[Other, Other], true));
    }
}
