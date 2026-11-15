// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BFS worklist engine for constant-reference value propagation.
//!
//! Propagates const_ref_values through Copy/Move, Cast, Field projection,
//! Reborrow, and DerefField chains. Extracted from codegen_decl_ref_const_values.rs
//! per #4147 (large-file decomposition).
//!
//! Moved into codegen_decl_ref_const_values/collect.rs per #3694
//! (collect/provenance-first module split).

use std::collections::{HashMap, HashSet, VecDeque};

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Place, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::chc::codegen_ctx::ConstRefObject;
use crate::codegen_ay::chc::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::decl::global_objects::InitSite;
use crate::codegen_ay::shared::const_pointer::{self, ConstRead, ConstRef};
use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;

/// Sound-fallback reason: a promoted constant reference whose target object is
/// registered (its address resolves) but whose contents were not decoded, so
/// its memory cells and `obj_size` are free (`codegen_ctx::fallback_soundness`).
pub(in crate::codegen_ay::chc) const CONST_REF_CONTENTS_UNMODELED: &str =
    "const_ref_contents_unmodeled";

#[derive(Copy, Clone)]
pub(in crate::codegen_ay::chc::decl) enum ConstRefValuePropagationKind {
    CopyMove,
    Cast,
    /// Field projection from a datatype source (Part of #3235).
    /// The usize is the field index in the first constructor.
    Field(usize),
    /// Reborrow: `_dest = &(*_src)` — preserves const_ref_values from source.
    /// Part of #4070: assert!() macro temporaries reborrow promoted constant
    /// references through `&(*_N)` patterns that the CopyMove/Cast/Field
    /// propagation doesn't cover.
    Reborrow,
    /// DerefField: `_dest = &((*_src).field_idx)` — extracts a field from
    /// the dereferenced promoted constant. Part of #4070: derived PartialEq
    /// on tuples creates references to individual fields of the promoted
    /// constant tuple, e.g., `_38 = &((*_33).1: bool)` where _33 points to
    /// `(3u8, true)`. The propagated value is the field extraction.
    DerefField(usize),
}

#[derive(Copy, Clone)]
pub(in crate::codegen_ay::chc::decl) struct ConstRefValuePropagationCandidate {
    pub(in crate::codegen_ay::chc::decl) dest_local: usize,
    pub(in crate::codegen_ay::chc::decl) kind: ConstRefValuePropagationKind,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc::decl) fn build_const_ref_value_propagation_candidates(
        &self,
    ) -> HashMap<usize, Vec<ConstRefValuePropagationCandidate>> {
        let mut by_src: HashMap<usize, Vec<ConstRefValuePropagationCandidate>> = HashMap::new();
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                Self::collect_propagation_candidate(lhs.local, rhs, &mut by_src);
            }
        }
        by_src
    }

    /// Classify a single `Assign` rvalue into zero or more propagation candidates.
    fn collect_propagation_candidate(
        dest_local: usize,
        rhs: &Rvalue,
        by_src: &mut HashMap<usize, Vec<ConstRefValuePropagationCandidate>>,
    ) {
        // Copy/Move: `_dest = Copy/Move(_src)`.
        if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) = rhs
            && place.projection.is_empty()
        {
            by_src.entry(place.local).or_default().push(ConstRefValuePropagationCandidate {
                dest_local,
                kind: ConstRefValuePropagationKind::CopyMove,
            });
        }
        // Part of #2173: Cast propagation (Transmute, PtrToPtr, etc.).
        if let Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) = rhs
            && place.projection.is_empty()
        {
            by_src.entry(place.local).or_default().push(ConstRefValuePropagationCandidate {
                dest_local,
                kind: ConstRefValuePropagationKind::Cast,
            });
        }
        // Part of #3235: Field projection propagation.
        // `_dest = Copy/Move(_src.field)` — makes field extraction transitive.
        if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) = rhs
            && place.projection.len() == 1
            && let rustc_public::mir::ProjectionElem::Field(field_idx, _) = place.projection[0]
        {
            by_src.entry(place.local).or_default().push(ConstRefValuePropagationCandidate {
                dest_local,
                kind: ConstRefValuePropagationKind::Field(field_idx),
            });
        }
        // Part of #4070: Reborrow and DerefField from Ref/AddressOf rvalues.
        Self::collect_ref_propagation_candidate(dest_local, rhs, by_src);
    }

    /// Collect Reborrow and DerefField propagation candidates from Ref/AddressOf.
    fn collect_ref_propagation_candidate(
        dest_local: usize,
        rhs: &Rvalue,
        by_src: &mut HashMap<usize, Vec<ConstRefValuePropagationCandidate>>,
    ) {
        let place: &Place = match rhs {
            Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p) => p,
            _ => return,
        };
        if place.projection.len() == 1
            && matches!(place.projection[0], rustc_public::mir::ProjectionElem::Deref)
        {
            by_src.entry(place.local).or_default().push(ConstRefValuePropagationCandidate {
                dest_local,
                kind: ConstRefValuePropagationKind::Reborrow,
            });
        }
        // `_dest = &((*_src).field_idx)` — derived PartialEq on tuples.
        if place.projection.len() == 2
            && matches!(place.projection[0], rustc_public::mir::ProjectionElem::Deref)
            && let rustc_public::mir::ProjectionElem::Field(field_idx, _) = place.projection[1]
        {
            by_src.entry(place.local).or_default().push(ConstRefValuePropagationCandidate {
                dest_local,
                kind: ConstRefValuePropagationKind::DerefField(field_idx),
            });
        }
    }

    fn enqueue_const_ref_value_local(
        queue: &mut VecDeque<usize>,
        queued: &mut HashSet<usize>,
        local: usize,
    ) {
        if queued.insert(local) {
            queue.push_back(local);
        }
    }

    /// Whether `dest = src as _` reads the window `src` points at as the same
    /// (or an element-compatible) type (`global_objects::fact_types_compatible`).
    /// A non-pointer side keeps the old behaviour.
    fn cast_keeps_window_type(&self, src_local: usize, dest_local: usize) -> bool {
        let locals = self.body.locals();
        let pointee = |local: usize| locals.get(local).and_then(|l| Self::deref_pointee_ty(l.ty));
        match (pointee(src_local), pointee(dest_local)) {
            (Some(src), Some(dest)) => {
                crate::codegen_ay::chc::decl::global_objects::fact_types_compatible(src, dest)
            }
            _ => true,
        }
    }

    /// Compute the propagated value for a single candidate, or None to skip.
    fn compute_propagated_value(
        src_value: &Expr,
        candidate: &ConstRefValuePropagationCandidate,
        src_local: usize,
    ) -> Option<Expr> {
        match candidate.kind {
            ConstRefValuePropagationKind::CopyMove => {
                debug!(
                    "Pass4.2 propagate const_ref_value: _{} = _{} -> {:?}",
                    candidate.dest_local, src_local, src_value
                );
                Some(src_value.clone())
            }
            ConstRefValuePropagationKind::Cast => {
                debug!(
                    "Pass4.2 cast const_ref_value: _{} = Cast(_{}) -> {:?}",
                    candidate.dest_local, src_local, src_value
                );
                Some(src_value.clone())
            }
            ConstRefValuePropagationKind::Reborrow => {
                debug!(
                    "Pass4.2 reborrow const_ref_value: _{} = &(*_{}) -> {:?}",
                    candidate.dest_local, src_local, src_value
                );
                Some(src_value.clone())
            }
            ConstRefValuePropagationKind::Field(field_idx)
            | ConstRefValuePropagationKind::DerefField(field_idx) => {
                Self::extract_field_from_propagation(src_value, candidate, src_local, field_idx)
            }
        }
    }

    /// Extract a datatype field from a propagation source value.
    fn extract_field_from_propagation(
        src_value: &Expr,
        candidate: &ConstRefValuePropagationCandidate,
        src_local: usize,
        field_idx: usize,
    ) -> Option<Expr> {
        let ay_bindings::SortInner::Datatype(dt) = src_value.sort().inner() else {
            return None;
        };
        let cons = dt.constructors.first()?;
        let field = cons.fields.get(field_idx)?;
        let extracted = src_value.clone().field_select(&dt.name, &field.name, field.sort.clone());
        debug!(
            dest_local = candidate.dest_local,
            src_local,
            field_name = %field.name,
            "Pass4.3 field/deref_field const_ref_value (worklist)"
        );
        Some(extracted)
    }

    pub(in crate::codegen_ay::chc::decl) fn propagate_const_ref_values_worklist(
        &mut self,
        by_src: &HashMap<usize, Vec<ConstRefValuePropagationCandidate>>,
    ) {
        let mut queue: VecDeque<usize> =
            self.ref_resolution.const_ref_values.keys().copied().collect();
        let mut queued: HashSet<usize> =
            self.ref_resolution.const_ref_values.keys().copied().collect();

        while let Some(src_local) = queue.pop_front() {
            queued.remove(&src_local);
            let Some(src_value) = self.ref_resolution.const_ref_values.get(&src_local).cloned()
            else {
                continue;
            };
            let Some(candidates) = by_src.get(&src_local) else { continue };
            for candidate in candidates {
                if !self.path_insensitive_metadata_copy_is_unique(src_local, candidate.dest_local) {
                    self.clear_path_insensitive_ref_metadata(candidate.dest_local);
                    continue;
                }
                if self.ref_resolution.const_ref_values.contains_key(&candidate.dest_local) {
                    continue;
                }
                // A cast to another pointee type reads another window: the
                // fact is re-decoded there (a fixed target) or not carried.
                let propagated_value =
                    if matches!(candidate.kind, ConstRefValuePropagationKind::Cast)
                        && !self.cast_keeps_window_type(src_local, candidate.dest_local)
                    {
                        self.moved_const_value_fact(src_local, candidate.dest_local, 0)
                    } else {
                        Self::compute_propagated_value(&src_value, candidate, src_local)
                    };
                let Some(propagated_value) = propagated_value else {
                    continue;
                };
                self.ref_resolution.const_ref_values.insert(candidate.dest_local, propagated_value);
                self.propagate_metadata(src_local, candidate);
                Self::enqueue_const_ref_value_local(&mut queue, &mut queued, candidate.dest_local);
            }
        }
    }

    /// Copy subslice_len and the object record from source to destination.
    ///
    /// The object record (D4) is the object AND the offset the pointer points
    /// at: a copy, cast or reborrow is the same pointer; `&(*src).f` points
    /// `f`'s layout offset further into the same object; a plain field copy
    /// (`src.f`) is not a pointer into the object at all.
    fn propagate_metadata(
        &mut self,
        src_local: usize,
        candidate: &ConstRefValuePropagationCandidate,
    ) {
        let dest_local = candidate.dest_local;
        // Part of #3495: Propagate subslice_len through Copy/Move/Cast.
        if let Some(len) = self.ref_resolution.subslice_len.get(&src_local).cloned() {
            self.ref_resolution.subslice_len.insert(dest_local, len);
        }
        let Some(object) = self.ref_resolution.const_ref_objects.get(&src_local).copied() else {
            return;
        };
        let moved = match candidate.kind {
            ConstRefValuePropagationKind::CopyMove
            | ConstRefValuePropagationKind::Cast
            | ConstRefValuePropagationKind::Reborrow => Some(object),
            ConstRefValuePropagationKind::DerefField(field_idx) => {
                let src_ty = self.body.locals()[src_local].ty;
                Self::deref_pointee_ty(src_ty)
                    .and_then(|pointee| {
                        crate::kani_middle::abi::LayoutOf::new(pointee).field_offset(field_idx)
                    })
                    .and_then(|off| object.moved(off as i128))
            }
            ConstRefValuePropagationKind::Field(_) => None,
        };
        if let Some(moved) = moved {
            self.ref_resolution.const_ref_objects.insert(dest_local, moved);
        }
    }

    /// Collects scalar values from constant references to primitive types.
    ///
    /// Part of #1919: When we see `_ref = const &0u8`, the allocation contains a
    /// pointer with provenance. We follow it to read the pointee value and record
    /// a AY expression. This enables `translate_place_with_deref` to resolve
    /// `(*_ref)` for promoted constant references that aren't tracked in ref_targets.
    pub(in crate::codegen_ay::chc) fn collect_const_ref_values(&mut self) {
        // D2's read set comes from the blocks that can CONTINUE, exactly as
        // in `global_objects::mint_reachable_objects`: a constant assigned in
        // a panic-only block (a precondition or assertion message) is read
        // only on a path that fails there whatever it reads.
        let may_continue =
            crate::codegen_ay::chc::decl::codegen_decl_panic_filter::compute_may_continue_blocks(
                self.body,
            );
        // Pass 4.1: Direct constant reference assignments to scalar types
        for (bb_idx, bb_data) in self.body.blocks.iter().enumerate() {
            let panic_only = !may_continue.get(bb_idx).copied().unwrap_or(true);
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.projection.is_empty()
                    && let Rvalue::Use(Operand::Constant(const_op), ..)
                    | Rvalue::Cast(
                        rustc_public::mir::CastKind::PointerCoercion(
                            rustc_public::mir::PointerCoercion::Unsize,
                        ),
                        Operand::Constant(const_op),
                        _,
                    ) = rhs
                {
                    self.try_collect_single_const_ref(lhs.local, const_op, panic_only);
                }
            }
        }

        // Pass 4.2+4.3: Propagate through Copy/Move, Cast, and Field projections.
        let propagation_candidates = self.build_const_ref_value_propagation_candidates();
        self.propagate_const_ref_values_worklist(&propagation_candidates);

        debug!(
            count = self.ref_resolution.const_ref_values.len(),
            memory_inits_count = self.ref_resolution.const_ref_memory_inits.len(),
            "CHC: collected constant reference values"
        );
    }

    /// Attempt to extract and record a const-ref value for one assignment.
    ///
    /// The constant pointer is what const-eval recorded (`const_pointer`): the
    /// relocation at the constant's own byte 0 names the target, and its bytes
    /// carry the offset. The local's object record is that target's ONE object
    /// and that offset (D4); its value fact is the pointee WINDOW at that
    /// offset, decoded only when the target is fixed (D5); its slice length is
    /// the fat pointer's metadata word (R3). The target is noted as read at the
    /// pointee type, so it is seeded whole (D2).
    ///
    /// A live static target is the static collector's (its state variable);
    /// a function or vtable target has no pointee value here.
    ///
    /// `panic_only`: the assignment sits in a block from which every path
    /// fails (`compute_may_continue_blocks`). Its value fact is still
    /// recorded, so the block translates as before, but its target is not
    /// noted as read and its window is not seeded: a 221-byte
    /// `ptr::copy` precondition message cost 221 entry-rule seeds and took
    /// `negative/copy_family_symbolic.rs`'s must-fail harnesses from 0.01 s
    /// to 18-22 s (round-10 full CHC gate), for bytes no continuing path reads.
    fn try_collect_single_const_ref(
        &mut self,
        dest_local: usize,
        const_op: &rustc_public::mir::ConstOperand,
        panic_only: bool,
    ) {
        if self.local_has_multiple_whole_definitions(dest_local) {
            self.clear_path_insensitive_ref_metadata(dest_local);
            return;
        }
        let mir_const = &const_op.const_;
        let ty = mir_const.ty();
        debug!("Pass4.1 scan: _{} = Use(Const), ty={:?}", dest_local, ty.kind());
        if self.ref_resolution.const_ref_values.contains_key(&dest_local) {
            return;
        }
        let Some(bytes) = const_pointer::const_bytes(mir_const) else { return };
        // The constant pointer's slot: the constant itself for `&T`; the Some
        // payload's slot for an `Option<&T>` VALUE (whose unwrap carries this
        // local's facts to the reference, `propagate_unwrapped_ref_metadata`).
        let (inner_ty, slot) = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner_ty, _) | RigidTy::RawPtr(inner_ty, _)) => {
                (inner_ty, 0)
            }
            _ => match Self::option_ref_const_payload_slot(&bytes, ty) {
                Some(found) => found,
                None => return,
            },
        };
        let Some(r) = const_pointer::const_ref(&bytes, slot, inner_ty) else { return };
        let Some(key) = r.ptr.key() else { return };
        let Some(object) = self.global_object(&key) else {
            debug!(dest_local, ?key, "const ref: target has no object; left to translation");
            return;
        };
        // A LIVE static's pointee is its state variable (the static collector,
        // D6): no value fact here. A FIXED static's window is folded exactly
        // like constant memory's (D5).
        if key.static_def().is_some()
            && object.fixed != Some(crate::codegen_ay::shared::const_pointer::Fixedness::Fixed)
        {
            return;
        }
        let offset = r.ptr.offset();
        self.ref_resolution.const_ref_objects.insert(
            dest_local,
            ConstRefObject { obj_id: object.obj_id, offset, ptr: Some(r.ptr), nested: None },
        );
        if !panic_only {
            self.note_object_read(key, inner_ty);
        }
        // Earlier deferred notes are noted now, so the ones this decode leaves
        // can be told apart (and dropped for a panic-only constant).
        self.drain_deferred_object_reads();

        let site = InitSite { obj_id: object.obj_id, base: offset };
        let mut local_memory_inits = Vec::new();
        let mut nested_str = None;
        let expr = const_pointer::fixed_pointee(self.tcx, &bytes, slot, inner_ty).and_then(
            |(_, window)| {
                if panic_only && matches!(inner_ty.kind(), TyKind::RigidTy(RigidTy::Str)) {
                    return self.extract_panic_only_str_value(&window);
                }
                self.try_extract_with_fallbacks(
                    &window,
                    inner_ty,
                    &mut local_memory_inits,
                    site,
                    &mut nested_str,
                )
            },
        );
        if panic_only {
            self.discard_deferred_object_reads();
        } else {
            self.drain_deferred_object_reads();
        }
        // The constant's target object has an address (`const_ptr_address`),
        // but when its contents do not decode, nothing seeds its cells: a deref
        // reads free cells, which admits every value (a proof over it is a
        // proof) but can fabricate a failure. Record it so no counterexample in
        // this harness is certified on the strength of those cells (T1 review,
        // 2026-09-24: `read_f32(&-0.0f32)` was certified Genuine on a free
        // `obj_size`).
        let Some(expr) = expr else {
            // A zero-sized pointee has no cells, so no read through this
            // constant can see a free one (`&Plain` behind a `&dyn Trait`
            // coercion): nothing to record. Recording it cost six bug rows
            // their certificate (walker_validity_intrinsics_dual.rs and
            // others, round-10 full CHC gate).
            if const_pointer::pointee_extent(inner_ty, r.metadata) == Some(0) {
                debug!(dest_local, ?inner_ty, "const ref: zero-sized pointee, no cells");
                return;
            }
            // Its free cells are read only on a path that fails anyway.
            if panic_only {
                return;
            }
            debug!(dest_local, ?inner_ty, "const ref: contents not decoded — recorded");
            self.record_sound_fallback_reason(CONST_REF_CONTENTS_UNMODELED);
            return;
        };
        debug!("Pass4 const_ref_value: _{} = {:?}", dest_local, expr);
        // A static's memory is its collector's (its typed-memory mirror and
        // layout record); seeding it here as well gave one object two sizes
        // (`obj_size` 4096 here, the static's own 8) — an unsatisfiable entry.
        if key.static_def().is_none() && !panic_only {
            self.push_const_memory_inits(local_memory_inits);
        }
        if !panic_only
            && matches!(inner_ty.kind(), TyKind::RigidTy(RigidTy::Array(..)))
            && !self.ty_has_interior_mut(inner_ty)
            && Self::translate_ty(inner_ty).as_ref() == Some(expr.sort())
        {
            self.ref_resolution
                .window_values
                .entry((key, offset, r.metadata, inner_ty))
                .or_insert_with(|| expr.clone());
        }
        self.ref_resolution.const_ref_values.insert(dest_local, expr);
        self.record_subslice_len(dest_local, inner_ty, &r, nested_str.as_ref().map(|n| n.len));
        if let Some(nested) = nested_str {
            if !panic_only {
                self.note_object_read(nested.target, nested.str_ty);
            }
            if let Some(record) = self.ref_resolution.const_ref_objects.get_mut(&dest_local) {
                record.nested = nested.inner;
            }
        }
    }

    /// For a constant `Option<&T>` (or `Option<*const T>`) VALUE holding
    /// `Some`: the pointee type and the byte offset of the payload's pointer
    /// slot. `None` for any other type, or a `None` value.
    pub(in crate::codegen_ay::chc) fn option_ref_const_payload_slot(
        bytes: &dyn ConstRead,
        ty: rustc_public::ty::Ty,
    ) -> Option<(rustc_public::ty::Ty, usize)> {
        use crate::codegen_ay::chc::expr::codegen_expr_constant_payload::decode_option_like_variant_index;
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
        let variants = def.variants();
        if variants.len() != 2 {
            return None;
        }
        let (v0, v1) = (variants[0].fields().len(), variants[1].fields().len());
        let some_idx = match (v0, v1) {
            (1, 0) => 0,
            (0, 1) => 1,
            _ => return None,
        };
        let payload_ty = mono_ty::field_ty(variants[some_idx].fields().first()?, &args)?;
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) =
            payload_ty.kind()
        else {
            return None;
        };
        let variant = decode_option_like_variant_index(bytes, ty, payload_ty, some_idx, 2)?;
        if variant != some_idx {
            return None;
        }
        let slot = crate::kani_middle::abi::LayoutOf::new(ty).variant_field_offset(some_idx, 0)?;
        Some((pointee, slot))
    }

    /// The facts of `Option::unwrap(const C)` for a constant `Option<&T>` VALUE
    /// operand holding `Some`: the payload pointer's object record (its
    /// target's object and its offset) and, for a fixed target, the pointee
    /// WINDOW's value — what Pass 4 records for `_N = const C`, for the
    /// constant that reaches the call directly as its operand.
    pub(in crate::codegen_ay::chc) fn record_const_option_payload_facts(
        &mut self,
        mir_const: &rustc_public::ty::MirConst,
        dest_local: usize,
    ) {
        let Some(bytes) = const_pointer::const_bytes(mir_const) else { return };
        let Some((pointee, slot)) = Self::option_ref_const_payload_slot(&bytes, mir_const.ty())
        else {
            return;
        };
        let Some(r) = const_pointer::const_ref(&bytes, slot, pointee) else { return };
        let Some(key) = r.ptr.key() else { return };
        let Some(object) = self.global_object(&key) else { return };
        self.ref_resolution.const_ref_objects.insert(
            dest_local,
            ConstRefObject {
                obj_id: object.obj_id,
                offset: r.ptr.offset(),
                ptr: Some(r.ptr),
                nested: None,
            },
        );
        let Some((_, window)) = const_pointer::fixed_pointee(self.tcx, &bytes, slot, pointee)
        else {
            return;
        };
        let site = InitSite { obj_id: object.obj_id, base: r.ptr.offset() };
        let mut scratch = Vec::new();
        if let Some(value) = self.decode_window(&window, pointee, &mut scratch, site) {
            self.ref_resolution.const_ref_values.insert(dest_local, value);
            self.record_subslice_len(dest_local, pointee, &r, None);
        }
    }

    /// Decode the pointee window: a nested `&&str` as its string's bytes (the
    /// representation the `str` comparison models consume), everything else by
    /// `decode_window`.
    fn try_extract_with_fallbacks(
        &self,
        window: &dyn ConstRead,
        inner_ty: rustc_public::ty::Ty,
        memory_inits: &mut Vec<(std::sync::Arc<str>, ay_bindings::Sort, Expr, u32, u64)>,
        site: InitSite,
        nested_str: &mut Option<super::super::codegen_decl_ref_const_extract::NestedStr>,
    ) -> Option<Expr> {
        // Part of #3607: nested `&&str`.
        if let TyKind::RigidTy(RigidTy::Ref(_, nested_inner_ty, _)) = inner_ty.kind()
            && matches!(nested_inner_ty.kind(), TyKind::RigidTy(RigidTy::Str))
        {
            let nested = self.extract_nested_str_from_const_ref(window)?;
            let bytes = nested.bytes.clone();
            *nested_str = Some(nested);
            return Some(bytes);
        }
        self.decode_window(window, inner_ty, memory_inits, site)
    }

    /// Record subslice_len for slice, str, and nested-str inner types: the fat
    /// pointer's own metadata word, never the size of its target allocation
    /// (R3: `T = "hello".split_at(2).1` has length 3, not 5).
    fn record_subslice_len(
        &mut self,
        dest_local: usize,
        inner_ty: rustc_public::ty::Ty,
        r: &ConstRef,
        nested_str_len: Option<usize>,
    ) {
        if const_pointer::pointee_has_len_metadata(inner_ty)
            && let Some(len) = r.metadata
        {
            let len_expr = Expr::bitvec_const(u128::from(len), POINTER_WIDTH);
            self.ref_resolution.subslice_len.insert(dest_local, len_expr);
        }
        if let Some(nested_len) = nested_str_len {
            let len_expr = Expr::bitvec_const(nested_len as u128, POINTER_WIDTH);
            self.ref_resolution.subslice_len.insert(dest_local, len_expr);
        }
    }
}
