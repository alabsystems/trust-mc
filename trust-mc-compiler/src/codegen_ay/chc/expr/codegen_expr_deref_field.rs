// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Deref resolution helpers: ref-target and argument-ref paths.
//!
//! Extracted from `codegen_expr_deref.rs` per #2884 (500 LOC threshold).
//! Methods: try_resolve_deref_via_ref_targets, resolve_arg_ref_deref,
//! emit_ptr_obj_valid_check.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Place, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::args::ChcTrackLevel;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
use crate::rustc_public_bridge::IndexedVal;

use super::ChcCtx;
use super::codegen_stmt_projection::FieldProjection;
use super::codegen_types::CodegenTypes;
use super::constant_index_offset;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve a deref chain via ref_targets tracking (#1712).
    ///
    /// Pattern: `(*ref_local).field` → `target_local.field` when `ref_local → target_local`.
    /// Handles RefTarget with pre-existing projections (e.g., `Pin<&mut T>` wrappers).
    pub(in crate::codegen_ay::chc) fn try_resolve_deref_via_ref_targets(
        &mut self,
        place: &Place,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Guard: translate_place_with_deref ↔ try_resolve_deref_via_ref_targets
        // mutual recursion. Self-referencing ref_targets (propagated_ref_target)
        // cause unbounded cycles. Cap at 4 hops (Pin<&mut T> needs ≤3). #3823
        self.deref_resolve_depth += 1;
        if self.deref_resolve_depth > 4 {
            warn!(local_idx, depth = self.deref_resolve_depth, "CHC: deref resolve depth exceeded");
            self.deref_resolve_depth -= 1;
            return None;
        }
        // Dereferencing a pointer whose target local's STORAGE IS DEAD is
        // use-after-scope. Stage a violated obligation for it.
        //
        // ADDITIVE ON PURPOSE. An earlier attempt REFUSED to resolve here, and
        // that REGRESSED: the caught cases (`let v = *p;`) were resolving
        // through this lane, and diverting them dropped the obligation that was
        // catching them — two detected bugs became clean proofs. Fail-closed is
        // safe when it drops a PROOF; here it dropped a REFUTATION. So resolve
        // exactly as before and only ADD the check.
        //
        // DEREF ONLY: #112 records that MIR legitimately READS a storage-dead
        // local as a source operand, so liveness must never gate a value read —
        // but a pointer INTO dead storage is UB however it is later used.
        //
        // A pointer a heap owner's accessor produced names the OWNER local, not
        // its allocation: [`Self::access_through_dead_ref_target`] tells the
        // dead owner's own storage from its moved buffer, and answers no for a
        // constant pointer's pointee, which the branch above bounds.
        if self.memory_safety_checks
            && let Some(rt) = self.ref_resolution.ref_targets.get(&local_idx)
            && self.liveness.dead_locals.contains(&rt.local)
            && self.ref_target_through_constant(rt.local, &rt.projections)
        {
            // A constant pointer's pointee never dies: bounded by the
            // global-object lane, or the read fails closed.
            self.bound_access_through_constant_or_fail_close(place, modified_locals);
        } else if self.memory_safety_checks && self.access_through_dead_ref_target(local_idx) {
            let dead = Expr::bool_const(false);
            if !self.heap_state.pending_checks.contains(&dead) {
                self.heap_state.pending_checks.push(dead);
            }
            warn!(
                local_idx,
                target = self.ref_resolution.ref_targets.get(&local_idx).map(|rt| rt.local),
                "CHC: deref through a pointer into DEAD storage (use-after-scope)"
            );
        }
        let result =
            self.try_resolve_deref_via_ref_targets_inner(place, local_idx, modified_locals);
        self.deref_resolve_depth -= 1;
        result
    }

    fn try_resolve_deref_via_ref_targets_inner(
        &mut self,
        place: &Place,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let base_local_ty = self.body.locals()[local_idx].ty;
        let is_raw_ptr = matches!(base_local_ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(_, _)));

        // Dead object detection (#762, #2055): check BEFORE the Mem-level early return
        // so that raw-pointer dereferences to dead locals emit error rules even when
        // the value load is routed through the memory path.
        if is_raw_ptr
            && let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx)
            && self.liveness.dead_locals.contains(&ref_target.local)
            && self.ref_target_through_constant(ref_target.local, &ref_target.projections)
        {
            self.bound_access_through_constant_or_fail_close(place, modified_locals);
        } else if is_raw_ptr && self.access_through_dead_ref_target(local_idx) {
            debug!(
                ptr_local = local_idx,
                target_local = self.ref_resolution.ref_targets.get(&local_idx).map(|rt| rt.local),
                "CHC: dead_object violation — deref of pointer to dead local (#762)"
            );
            self.heap_state.pending_checks.push(Expr::bool_const(false));
        }

        // At Mem level, raw-pointer dereferences must go through the memory path
        // to match the store side which uses build_memory_store for *ptr = val (#892).
        // Safe reference dereferences can still resolve through ref_targets because
        // ref targets are assigned via register (+ memory mirror), and the register
        // value is guaranteed to be the correct concrete value.
        // Fix #2110: The blanket Mem rejection broke test_raw_ptr_read_access and
        // test_raw_pointer_validity_tracking which use safe reference dereferences.
        //
        // Exception: call-forwarded raw pointers (e.g., UnsafeCell::get results)
        // are allowed through because their ref_targets were set by call handlers
        // from register-assigned locals, not from memory stores. The register value
        // is guaranteed correct. Part of #3452: Atomic/Stable dispatch gap.
        //
        // Fix #4228: Also allow ref_target resolution when the raw pointer maps to
        // a state-tracked local with no offset — mirrors the store side
        // (deref_mem.rs:278-285) which defers to Reg for this same case.
        // Without this, stores go to Reg but loads fall to the (empty) memory
        // array, making the assertion unprovable.
        if self.track_level >= ChcTrackLevel::Mem
            && is_raw_ptr
            && (!self.ref_resolution.call_forwarded_raw_ptrs.contains(&local_idx)
                || self.ref_resolution.subslice_offset.contains_key(&local_idx))
        {
            let has_reg_store_path =
                self.ref_resolution.ref_targets.get(&local_idx).is_some_and(|rt| {
                    self.try_state_idx_for_local(rt.local).is_some()
                        && !self.ref_resolution.subslice_offset.contains_key(&local_idx)
                });
            if !has_reg_store_path {
                return None;
            }
        }

        // Find position of first Deref projection
        let deref_idx = place.projection.iter().position(|p| matches!(p, ProjectionElem::Deref))?;

        // Part of #4181: Only resolve when Deref is the first projection.
        // When deref_idx > 0, there are field/downcast projections BEFORE
        // the Deref (e.g., _local.Field(0).Deref). These pre-deref projections
        // must be applied to _local's value first — ref_targets[local] only
        // describes what *_local resolves to, not _local.Field(N). Attempting
        // to resolve through ref_targets here drops the pre-deref projections,
        // producing the wrong value (e.g., whole coroutine instead of a field).
        if deref_idx > 0 {
            return None;
        }

        // Check if base local is tracked in ref_targets
        let ref_target = self.ref_resolution.ref_targets.get(&local_idx)?.clone();
        let referent_target = ref_target.clone();

        // Get projections after the Deref
        let remaining_projs = &place.projection[deref_idx + 1..];

        // Only proceed if remaining projections are value-semantics projections (no Deref).
        let all_value_projs = remaining_projs.iter().all(|p| {
            matches!(
                p,
                ProjectionElem::Field(_, _)
                    | ProjectionElem::Downcast(_)
                    | ProjectionElem::Index(_)
                    | ProjectionElem::ConstantIndex { .. }
                    | ProjectionElem::Subslice { .. }
            )
        });

        if !all_value_projs {
            return None;
        }

        // Part of #1712: Combine pre-existing projections from RefTarget with the
        // remaining projections from this place access. Destructure to move projections
        // instead of cloning (Part of #2267: clone elimination).
        let target_local = ref_target.local;
        let pre_proj_count = ref_target.projections.len();

        // If the resolved ref-target still denotes a pointer/reference value, the
        // original Deref has not been consumed yet. Re-apply one Deref before the
        // remaining projections so `*tmp_ref` loads the pointee value instead of
        // forwarding pointer bits (Part of #2323 closure capture regression).
        // Move projections into a temporary Place for the type check, then take back.
        let target_place = Place { local: target_local, projection: ref_target.projections };
        let target_ty_is_ptr = target_place.ty(self.body.locals()).ok().is_some_and(|ty| {
            matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, _, _) | RigidTy::RawPtr(_, _)))
        });
        let mut combined_projs = target_place.projection;
        // Part of #3041: Skip extra Deref for double references (&&T / &*T).
        // When base_local is &&T, *local dereferences the outer & → &T.
        // The ref_target resolves to the inner &T local, which IS the result.
        // Adding another Deref would consume the inner & too, giving T (value)
        // instead of &T (address). The original Part of #2323 Deref is only
        // needed when the target is a single-level reference (closure capture).
        let is_double_ref = matches!(
            base_local_ty.kind(),
            TyKind::RigidTy(RigidTy::Ref(_, inner_ty, _))
                if matches!(inner_ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, _, _) | RigidTy::RawPtr(_, _)))
        );
        if target_ty_is_ptr && !is_double_ref {
            combined_projs.push(ProjectionElem::Deref);
        }
        combined_projs.extend(remaining_projs.iter().cloned());

        // Fix #2919: Resolve Index(idx_local) to ConstantIndex when the index local
        // is dead (StorageDead). Dead locals are dropped from the CHC relation, so
        // referencing their state variable produces an unconstrained symbolic value.
        self.resolve_dead_index_projections(&mut combined_projs);

        // Rewrite: use target_local with combined projections
        let resolved_place = Place { local: target_local, projection: combined_projs };

        // The rewrite is only legitimate when it names the SAME place. When the
        // rewritten place has a different type, the chain landed one indirection
        // short of the original: `*_p` with `_p: &mut u32` rewritten onto
        // `_box.0.0: NonNull<u32>` reads the POINTER where the program reads the
        // POINTEE, so the `+= 1` in a contract body adds to the Box's ADDRESS and
        // the store lands on a cell the read never sees. A place rewrite that
        // changes the type is not a rewrite of the same place — decline it and let
        // the memory lane translate the deref through the pointer's value.
        // No fact is asserted here, so declining cannot fabricate: the caller
        // falls through to the remaining resolution lanes and finally to the
        // Mem projection loop, which records its own drop if it too declines.
        // A POINTER CAST between the reference and its target is decided at the
        // deref boundary: the type of `*p` against the type of the place it
        // resolves to. The whole-place types below cannot see it once a field
        // follows the deref, because a `Field` projection carries its own type:
        // `(*(&x as *const u128 as *const Words)).hi` resolves to `x.1: u64`,
        // the same type as the original place, and the u128 register's field 1
        // then read through the bitvector selector's `Layout` convention (the
        // LOW half): `hi == 1` PROVED for `x = 1 | (7 << 64)` (review probe
        // p1_ptr_cast.rs `field_read_bug`, a missed bug).
        let in_body = |local: usize| local < self.body.locals().len();
        let boundary_orig_ty = in_body(local_idx)
            .then(|| {
                Place { local: local_idx, projection: vec![ProjectionElem::Deref] }
                    .ty(self.body.locals())
                    .ok()
            })
            .flatten()
            .map(|ty| self.resolve_body_ty(ty));
        let boundary_len = resolved_place.projection.len() - remaining_projs.len();
        let boundary_place = Place {
            local: target_local,
            projection: resolved_place.projection[..boundary_len].to_vec(),
        };
        let boundary_resolved_ty = in_body(target_local)
            .then(|| boundary_place.ty(self.body.locals()).ok())
            .flatten()
            .map(|ty| self.resolve_body_ty(ty));
        // A read through a raw pointer whose definition chain puts it at a
        // nonzero byte offset from its ref target that no offset metadata
        // records (`(&p.a as *const u32 as *const u8).byte_add(4) as *const
        // u32`): the ref target names `p.a` and the read took `p.a` whatever
        // the type, so `*s == 1` was a clean proof where Kani reads `p.b == 2`,
        // and its `== 2` twin a certified false counterexample (self-review of
        // round 10 of fix/chc-false-certificates, `q_step.rs` st02, st04; the
        // same on main f5dfb8d48). The bytes at the referent's offset in its
        // local plus the chain's offset are read when they stay in the local
        // and its register is authoritative; any other such read fails closed.
        if is_raw_ptr
            && !target_ty_is_ptr
            && !self.ref_resolution.subslice_offset.contains_key(&local_idx)
            && let Some(chain) = self.store_pointer_referent_byte_offset(local_idx, &referent_target)
            && chain != 0
        {
            if remaining_projs.is_empty()
                && let Some(read_ty) = boundary_orig_ty
                && let Some(value) = self.ref_target_local_bytes_read(
                    &referent_target,
                    chain,
                    read_ty,
                    modified_locals,
                )
            {
                self.emit_ptr_obj_valid_check(local_idx, modified_locals);
                debug!(
                    orig_local = local_idx,
                    target_local,
                    chain,
                    "CHC: read at the chain's offset from its ref target, from its local's bytes"
                );
                return Some(value);
            }
            self.record_sound_fallback_reason("deref_read_offset_metadata_lost");
            return None;
        }
        // A read WIDER than its referent through a pointer cast (`*(&s.a as
        // *const u16 as *const u32)`): the bytes at the referent's offset in
        // its local plus the pointer's offset from the referent, when they stay
        // in the local and its register is the only place it changes. The
        // memory lane read the bytes past the referent from a cell no store
        // wrote: a certified false counterexample on main (first review of the
        // sixth round, `chc_wide_store_dual.rs` `safe_field_widen_read`). A read
        // past the local keeps the memory lane, which checks its bound.
        if let (Some(read_ty), Some(referent_ty)) = (boundary_orig_ty, boundary_resolved_ty)
            && read_ty != referent_ty
            && remaining_projs.is_empty()
            && let Some(value) = self.wider_ref_target_read(
                local_idx,
                &referent_target,
                referent_ty,
                read_ty,
                modified_locals,
            )
        {
            if is_raw_ptr {
                self.emit_ptr_obj_valid_check(local_idx, modified_locals);
            }
            debug!(
                orig_local = local_idx,
                target_local,
                ?read_ty,
                ?referent_ty,
                "CHC: wider read through a pointer cast taken from its local's bytes"
            );
            return Some(value);
        }
        if let (Some(read_ty), Some(referent_ty)) = (boundary_orig_ty, boundary_resolved_ty)
            && read_ty != referent_ty
            && self.transmute_aggregate_memory_order_applies(referent_ty, read_ty)
        {
            // The referent's bytes read as another type of the SAME size, one
            // side a multi-field struct or tuple (`*(&w as *const Words as *const
            // u128)`, or a field after it). The memory lane this used to fall
            // back to reads a typed cell no store wrote (the referent lives in
            // its register): a havoc, or a stale value when some store did
            // write it. Build the value from the memory layout when the
            // referent's register is the only place it changes (never borrowed
            // mutably, or no write in this body can reach memory around the
            // register; no projection before the deref), and read a FRESH
            // value with a booking otherwise. `&mut w as *mut AWords as *mut
            // u128` borrows `w` mutably only to cast it: with no store through
            // any pointer the register is exact (chc_reinterpret_routes_dual.rs
            // `bug_ptr_cast_mut_read` keeps the Genuine it had on the baseline).
            let eligible =
                pre_proj_count == 0 && self.local_register_is_authoritative(target_local);
            let reinterpreted = if eligible {
                self.reinterpret_ref_target_read(
                    &boundary_place,
                    referent_ty,
                    read_ty,
                    modified_locals,
                )
                .and_then(|value| {
                    if remaining_projs.is_empty() {
                        Some(value)
                    } else {
                        self.translate_place_field_index(
                            remaining_projs,
                            value,
                            Some(read_ty),
                            modified_locals,
                        )
                    }
                })
            } else {
                None
            };
            if is_raw_ptr {
                self.emit_ptr_obj_valid_check(local_idx, modified_locals);
            }
            if let Some(value) = reinterpreted {
                debug!(
                    orig_local = local_idx,
                    target_local,
                    ?read_ty,
                    ?referent_ty,
                    projections = remaining_projs.len(),
                    "CHC: ref_target deref through a pointer cast read in memory order"
                );
                return Some(value);
            }
            let orig_ty = place.ty(self.body.locals()).ok().map(|ty| self.resolve_body_ty(ty))?;
            let sort = Self::translate_ty(orig_ty)?;
            debug!(
                orig_local = local_idx,
                target_local,
                ?read_ty,
                ?referent_ty,
                eligible,
                "CHC: pointer-cast reinterpretation not modeled; fresh value"
            );
            let booked = self.record_sound_fallback_reason("transmute_layout_fallback");
            if sort.is_datatype() {
                self.declare_datatype_sort_if_needed(&sort);
            }
            return Some(crate::codegen_ay::chc::codegen_ctx::Havoc::booked(
                booked,
                crate::codegen_ay::chc::chc_fresh_name("__ptr_cast_layout_nondet"),
                sort,
            ));
        }

        // The rewrite is only legitimate when it names the SAME place. When the
        // rewritten place has a different type, the chain landed one indirection
        // short of the original: `*_p` with `_p: &mut u32` rewritten onto
        // `_box.0.0: NonNull<u32>` reads the POINTER where the program reads the
        // POINTEE, so the `+= 1` in a contract body adds to the Box's ADDRESS and
        // the store lands on a cell the read never sees. A place rewrite that
        // changes the type is not a rewrite of the same place — decline it and let
        // the memory lane translate the deref through the pointer's value.
        // No fact is asserted here, so declining cannot fabricate: the caller
        // falls through to the remaining resolution lanes and finally to the
        // Mem projection loop, which records its own drop if it too declines.
        let orig_ty = place.ty(self.body.locals()).ok();
        let resolved_ty = resolved_place.ty(self.body.locals()).ok();
        if let (Some(orig_ty), Some(resolved_ty)) = (orig_ty, resolved_ty)
            && orig_ty != resolved_ty
        {
            debug!(
                orig_local = local_idx,
                target_local,
                ?orig_ty,
                ?resolved_ty,
                "CHC: declining ref_target deref rewrite — resolved place has a different type"
            );
            return None;
        }

        debug!(
            orig_local = local_idx,
            target_local,
            pre_projs = pre_proj_count,
            remaining = remaining_projs.len(),
            "CHC: resolved deref chain via ref_targets"
        );

        // Part of #4278: obj_valid guard for raw-ptr ref_target resolution.
        // Without this, freed heap ptrs bypass the memory-path obj_valid check.
        if is_raw_ptr {
            self.emit_ptr_obj_valid_check(local_idx, modified_locals);
        }

        self.translate_place_with_deref(&resolved_place, modified_locals)
    }

    /// The value of `resolved` (MIR type `resolved_ty`) reinterpreted as
    /// `read_ty` in memory order, when exactly one side is a multi-field
    /// struct or tuple and the other a bitvector of the same size. `None`
    /// otherwise (the caller keeps its fallback).
    fn reinterpret_ref_target_read(
        &mut self,
        resolved: &Place,
        resolved_ty: rustc_public::ty::Ty,
        read_ty: rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use crate::codegen_ay::chc::stmt::codegen_stmt_transmute_layout::AggregateTransmute;
        // Translating the referent stages checks and read marks; do it only when
        // the lane can use the value, so a declined lane leaves nothing behind
        // (a pointer cast between two scalars, `4 as *mut u32` through
        // `NonNull::new_unchecked`, must read exactly as before).
        if !self.transmute_aggregate_memory_order_applies(resolved_ty, read_ty) {
            return None;
        }
        let staged = self.heap_state.pending_checks.len();
        let Some(value) = self.translate_place_with_deref(resolved, modified_locals) else {
            self.heap_state.pending_checks.truncate(staged);
            return None;
        };
        match self.transmute_aggregate_memory_order(&value, resolved_ty, read_ty) {
            AggregateTransmute::Precise(reinterpreted) => {
                if let Some(sort) = Self::translate_ty(self.resolve_body_ty(read_ty))
                    && sort.is_datatype()
                {
                    self.declare_datatype_sort_if_needed(&sort);
                }
                Some(reinterpreted)
            }
            AggregateTransmute::NotApplicable | AggregateTransmute::Unsupported(_) => {
                self.heap_state.pending_checks.truncate(staged);
                None
            }
        }
    }

    /// The value a read of `read_ty`, wider than its referent `referent_ty`,
    /// through the pointer `ptr_local` reads: the bytes of the referent's
    /// containing local from the referent's field offset plus the pointer's
    /// offset from the referent (`store_pointer_referent_byte_offset`), when
    /// they stay inside the local and the local's register is authoritative.
    /// `None` otherwise (the caller keeps its other lanes).
    fn wider_ref_target_read(
        &mut self,
        ptr_local: usize,
        referent: &crate::codegen_ay::chc::RefTarget,
        referent_ty: rustc_public::ty::Ty,
        read_ty: rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let size_of = |ty: rustc_public::ty::Ty| {
            ty.layout().ok().and_then(|l| u64::try_from(l.shape().size.bytes()).ok())
        };
        let read = size_of(read_ty)?;
        if read <= size_of(referent_ty)? {
            return None;
        }
        let chain = self.store_pointer_referent_byte_offset(ptr_local, referent)?;
        self.ref_target_local_bytes_read(referent, chain, read_ty, modified_locals)
    }

    /// The `read_ty` value at byte `chain` past the referent `referent` in its
    /// containing local, read from the local's register (which must be the only
    /// place the local changes), when the bytes stay inside the local.
    fn ref_target_local_bytes_read(
        &mut self,
        referent: &crate::codegen_ay::chc::RefTarget,
        chain: i128,
        read_ty: rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use crate::codegen_ay::chc::stmt::codegen_stmt_union_bits::UnionLane;
        let size_of = |ty: rustc_public::ty::Ty| {
            ty.layout().ok().and_then(|l| u64::try_from(l.shape().size.bytes()).ok())
        };
        let read = size_of(read_ty)?;
        if !self.local_register_is_authoritative(referent.local) {
            return None;
        }
        let local_ty = self.resolve_body_ty(self.body.locals().get(referent.local)?.ty);
        let local_size = size_of(local_ty)?;
        let field_offset = self.field_path_byte_offset(local_ty, &referent.projections)?;
        let start = u64::try_from(i128::from(field_offset) + chain).ok()?;
        if start.checked_add(read)? > local_size {
            return None;
        }
        let staged = self.heap_state.pending_checks.len();
        let local = Place { local: referent.local, projection: Vec::new() };
        let value = self
            .translate_place_with_modified(&local, modified_locals)
            .map(|old| self.bytes_at(&old, local_ty, start, read_ty));
        match value {
            Some(UnionLane::Exact(value)) => {
                if let Some(sort) = Self::translate_ty(self.resolve_body_ty(read_ty))
                    && sort.is_datatype()
                {
                    self.declare_datatype_sort_if_needed(&sort);
                }
                Some(value)
            }
            _ => {
                self.heap_state.pending_checks.truncate(staged);
                None
            }
        }
    }

    /// Resolve dead `Index(idx_local)` projections to `ConstantIndex`.
    ///
    /// When a RefTarget stores `Index(idx_local)` and `idx_local` is dead
    /// (StorageDead at the current program point), the state variable for
    /// `idx_local` is not in the CHC relation — reading it produces an
    /// unconstrained symbolic value, causing spurious counterexamples.
    ///
    /// This scans MIR for the constant assignment `_idx = Use(Const(N))` and
    /// replaces `Index(idx_local)` with `ConstantIndex { offset: N, ... }`.
    ///
    /// Part of #2919: fixes 4 read-side spurious CTREX in array ref deref tests.
    fn resolve_dead_index_projections(&self, projs: &mut [ProjectionElem]) {
        for proj in projs.iter_mut() {
            let idx_local = match proj {
                ProjectionElem::Index(local) => {
                    let local_idx: usize = *local;
                    if !self.liveness.dead_locals.contains(&local_idx) {
                        continue;
                    }
                    local_idx
                }
                _ => continue,
            };

            // Scan MIR for `_idx_local = Use(Const(N))` to find the constant value.
            // Part of #3117: collect ALL constant assignments to validate uniqueness.
            // Without dominance analysis, multiple assignments could come from
            // different branches — resolving to the wrong one is unsound.
            let mut const_vals: Vec<usize> = Vec::new();
            for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                        && lhs.projection.is_empty()
                        && lhs.local == idx_local
                        && let Rvalue::Use(Operand::Constant(const_op), ..) = rhs
                        && let Some(val) = Self::extract_const_usize(&const_op.const_)
                    {
                        const_vals.push(val);
                    }
                }
            }
            // Deduplicate: multiple blocks may assign the same constant (e.g.,
            // loop unrolling). Only ambiguous if distinct values exist.
            const_vals.sort_unstable();
            const_vals.dedup();
            match const_vals.as_slice() {
                [val] => {
                    debug!(
                        idx_local,
                        val, "CHC: resolved dead Index local to ConstantIndex (Part of #2919)"
                    );
                    *proj = ProjectionElem::ConstantIndex {
                        offset: *val as u64,
                        min_length: *val as u64 + 1,
                        from_end: false,
                    };
                }
                [] => {
                    warn!(
                        idx_local,
                        "CHC: dead Index local has no constant assignment — deref may be unconstrained"
                    );
                }
                _ => {
                    warn!(
                        idx_local,
                        count = const_vals.len(),
                        "CHC: dead Index local has multiple distinct constant assignments — \
                         skipping resolution to avoid unsound index selection (Part of #3117)"
                    );
                }
            }
        }
    }

    /// Extract a `usize`-typed constant integer from a MIR constant.
    /// The one constant every definition of `local` assigns (`_l = const N`),
    /// or `None` when any definition is something else (a call, a computed
    /// value, a partial write) or two definitions disagree.
    pub(in crate::codegen_ay::chc) fn unique_const_usize_definition(
        &self,
        local: usize,
    ) -> Option<usize> {
        use rustc_public::mir::TerminatorKind;
        let mut value: Option<usize> = None;
        for bb_data in &self.body.blocks {
            if let TerminatorKind::Call { destination, .. } = &bb_data.terminator.kind
                && destination.local == local
            {
                return None;
            }
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if lhs.local != local {
                    continue;
                }
                let Rvalue::Use(Operand::Constant(const_op), ..) = rhs else { return None };
                if !lhs.projection.is_empty() {
                    return None;
                }
                let val = Self::extract_const_usize(&const_op.const_)?;
                if value.is_some_and(|seen| seen != val) {
                    return None;
                }
                value = Some(val);
            }
        }
        value
    }

    fn extract_const_usize(mir_const: &rustc_public::ty::MirConst) -> Option<usize> {
        if !matches!(mir_const.ty().kind(), TyKind::RigidTy(RigidTy::Uint(_))) {
            return None;
        }
        crate::codegen_ay::shared::const_pointer::const_uint(mir_const)
            .and_then(|v| usize::try_from(v).ok())
    }

    /// Resolve deref through argument reference locals (#2844).
    ///
    /// Function arguments with type &T/&mut T have no `_N = &_M` in MIR,
    /// so ref_targets has no entry for them. ref_arg_pointee_idx maps the
    /// argument local directly to the auxiliary pointee state_vars vec index.
    /// Mirrors the store-side handler in codegen_stmt_store_ref.rs (#2496).
    ///
    /// Returns `Some(expr)` if the deref was resolved, `None` otherwise.
    pub(in crate::codegen_ay::chc) fn resolve_arg_ref_deref(
        &mut self,
        place: &Place,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let pointee_vec_idx = *self.ref_resolution.ref_arg_pointee_idx.get(&local_idx)?;

        let deref_idx =
            place.projection.iter().position(|p| matches!(p, ProjectionElem::Deref)).unwrap_or(0);
        let remaining_projs = &place.projection[deref_idx + 1..];

        // Use the same synthetic track_key as the store side for
        // block-local SSA chaining (write-then-read in the same block).
        let track_key = usize::MAX - pointee_vec_idx;
        let pointee_expr = if let Some(env_expr) = self.encode.local_expr_env.get(&track_key) {
            debug!(local_idx, pointee_vec_idx, "CHC: resolved *arg_ref via local_expr_env (#2844)");
            env_expr.clone()
        } else if self.encode.modified_state_indices.contains(&pointee_vec_idx) {
            let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(pointee_vec_idx)?;
            debug!(
                local_idx,
                pointee_vec_idx, "CHC: resolved *arg_ref via output state var (#2844)"
            );
            Expr::var(&**out_name, out_sort.clone())
        } else {
            let (in_name, in_sort) = self.state_var_mgr.state_vars.get(pointee_vec_idx)?;
            debug!(
                local_idx,
                pointee_vec_idx, "CHC: resolved *arg_ref via input state var (#2844)"
            );
            Expr::var(&**in_name, in_sort.clone())
        };

        // Apply remaining projections (Field, Index, Downcast) after the Deref.
        if remaining_projs.is_empty() {
            return Some(pointee_expr);
        }

        // Part of #3116: Track current MIR type through projections for bounds
        // checks and BV→Datatype unflattening (matching translate_place_with_deref).
        let arg_ty = self.body.locals()[local_idx].ty;
        let mut current_ty = match arg_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _)) => Some(pointee_ty),
            _ => None,
        };

        // Apply field selections from remaining projections.
        let mut current = pointee_expr;
        let mut active_variant: Option<usize> = None;
        for proj in remaining_projs {
            match proj {
                ProjectionElem::Field(field_idx, field_ty) => {
                    let selections = vec![FieldProjection {
                        field_idx: *field_idx,
                        cons_idx: active_variant.take(),
                        field_ty: Some(*field_ty),
                    }];
                    current = Self::apply_field_selections(current, &selections)?;
                    current_ty = Some(*field_ty);
                }
                ProjectionElem::Downcast(variant_idx) => {
                    active_variant = Some(variant_idx.to_index());
                }
                ProjectionElem::Index(index_local) => {
                    let index_expr = self.resolve_local_expr(*index_local, modified_locals)?;
                    let index_expr = coerce_bitvec_width_safe(
                        index_expr,
                        POINTER_WIDTH,
                        SignExtension::ZeroExtend,
                    );
                    // Part of #3116: Emit bounds check matching translate_place_with_deref.
                    if let Some(ty) = current_ty {
                        if let Some(array_len) = self.get_array_length(ty) {
                            let len_expr = Expr::bitvec_const(array_len as u128, POINTER_WIDTH);
                            let bounds_check = index_expr.clone().bvult(len_expr);
                            self.heap_state.pending_checks.push(bounds_check);
                            debug!(
                                array_len,
                                "CHC: resolve_arg_ref_deref - emitted Index bounds check (Part of #3116)"
                            );
                        }
                    }
                    if !current.sort().is_array() {
                        return None;
                    }
                    current = current.select(index_expr);
                    // Part of #3296: Update type tracking and unflatten BV→DT.
                    current_ty = current_ty.and_then(|ty| self.get_array_element_ty(ty));
                    if let Some(ty) = current_ty {
                        current = self.try_unflatten_bv_to_datatype(current, ty);
                    }
                    active_variant = None;
                }
                ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                    // #from_end needs the slice's runtime length -> fail closed (projection_path.rs)
                    let Some(actual_offset) =
                        constant_index_offset(*offset, *min_length, *from_end)
                    else {
                        return None;
                    };
                    // Part of #3116: Emit bounds check matching translate_place_with_deref.
                    if let Some(ty) = current_ty {
                        if let Some(array_len) = self.get_array_length(ty) {
                            let index_expr_check =
                                Expr::bitvec_const(actual_offset as u128, POINTER_WIDTH);
                            let len_expr = Expr::bitvec_const(array_len as u128, POINTER_WIDTH);
                            let bounds_check = index_expr_check.bvult(len_expr);
                            self.heap_state.pending_checks.push(bounds_check);
                            debug!(
                                actual_offset,
                                array_len,
                                from_end,
                                "CHC: resolve_arg_ref_deref - emitted ConstantIndex bounds check (Part of #3116)"
                            );
                        }
                    }
                    let index_expr = Expr::bitvec_const(actual_offset as u128, POINTER_WIDTH);
                    if !current.sort().is_array() {
                        return None;
                    }
                    current = current.select(index_expr);
                    // Part of #3296: Update type tracking and unflatten BV→DT.
                    current_ty = current_ty.and_then(|ty| self.get_array_element_ty(ty));
                    if let Some(ty) = current_ty {
                        current = self.try_unflatten_bv_to_datatype(current, ty);
                    }
                    active_variant = None;
                }
                ProjectionElem::Subslice { from, to, from_end } => {
                    // Part of #3306: SubSlice via shared helper.
                    let ty = current_ty?;
                    current = self.build_subslice_expr(&current, ty, *from, *to, *from_end)?;
                    active_variant = None;
                }
                _ => return None, // external enum: ProjectionElem
            }
        }
        Some(current)
    }
}
