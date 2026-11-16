// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Mirror-store helpers for Mem-level deref stores.
//!
//! These methods mirror `*ref = value` updates into register state so that
//! subsequent deref reads via `ref_targets` observe the updated value.
//!
//! Part of #2278: Extracted from `deref_mem.rs` for #2884 file decomposition.

use crate::codegen_ay::chc::codegen_ctx::{Havoc, sound_havoc};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::CrateDef;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use ay_bindings::Expr;

use crate::codegen_ay::shared::mono_ty;

use super::super::codegen_call_coerce::coerce_eq_constraint;
use super::super::codegen_ctx::CollectionProjectionKind;
use super::super::codegen_types::CodegenTypes;
use super::super::stmt_accumulator::StmtAccumulator;
use super::super::{
    ChcCtx, FieldProjection, POINTER_WIDTH, RefTarget, UnknownProjectionPolicy, chc_fresh_name,
    collect_field_projections, constant_index_offset,
};
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

use super::deref_mem_mirror_struct::RefTargetJoin;

struct DatatypeMirrorTarget {
    ref_local: usize,
    target_local: usize,
    target_vec_idx: usize,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Opaque iterator adapters are intentionally encoded as pointer-width
    /// scalar symbols rather than datatypes. A write through `&mut self.field`
    /// must therefore update the whole opaque abstraction, not attempt a field
    /// slot mirror against the scalar state var.
    fn try_build_opaque_iterator_adapter_store_expr(
        &self,
        target_local: usize,
        out_sort: &ay_bindings::Sort,
        combined_field_projs: &[FieldProjection],
    ) -> Option<Expr> {
        if combined_field_projs.is_empty() || out_sort.is_datatype() {
            return None;
        }

        let local_ty = self.body.locals().get(target_local)?.ty;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = local_ty.kind() else {
            return None;
        };
        // Std's adapters only (the sort rule makes no other type opaque): a
        // user `Chain<T>`'s `self.n -= 1` wrote a fresh value that only an
        // unread gap counter recorded (walker fail-closed repair round 5,
        // `user_type_named_like_std_dual.rs`).
        if !matches!(def.trimmed_name().as_str(), "FlatMap" | "FlattenCompat" | "Chain" | "Fuse")
            || def.krate().is_local
        {
            return None;
        }

        self.record_aggregate_gap("opaque_iterator_adapter_field_store_symbolic");
        Some(Havoc::mint_deferred(
            self,
            sound_havoc::UNTRACKED_COLLECTION_STATE,
            chc_fresh_name("__opaque_iter_adapter_store"),
            out_sort.clone(),
        ))
    }

    /// Check whether this is an unmodeled VecIntoIter projection (field index
    /// beyond the Datatype constructor arity). Uses the typed
    /// `CollectionProjectionKind` enum instead of string-based name matching.
    fn is_unmodeled_vec_into_iter_projection(
        &self,
        target_local: usize,
        out_sort: &ay_bindings::Sort,
        combined_field_projs: &[FieldProjection],
    ) -> bool {
        if self.collections.projection_locals.get(&target_local).copied()
            != Some(CollectionProjectionKind::VecIntoIter)
        {
            return false;
        }
        let Some(dt) = out_sort.datatype_sort() else {
            return false;
        };
        let Some(ctor) = dt.constructors.first() else {
            return false;
        };
        let modeled_fields = ctor.fields.len();
        combined_field_projs.iter().any(|proj| proj.field_idx >= modeled_fields)
    }

    /// Fail closed when a Mem-level deref store could not be mirrored into the
    /// target's register image.
    ///
    /// The memory store has already been emitted by the caller
    /// (`handle_deref_store_mem_level`), so returning without touching the
    /// register image LOSES the write: later reads of the owner (read case C
    /// in `translate_flattened_place`, `flattened_local_field_expr`) see the
    /// old value, and a proof or a Genuine certificate can rest on it. Here
    /// every register slot of the target takes its free output variable (a
    /// `true` constraint registered per slot key, so `build_block_output_args`
    /// uses the OUTPUT var), every cached value for the target is dropped, and
    /// an unblessed reason is recorded. Unlisted reasons default to
    /// `FallbackSoundness::FailClose`, so a Success becomes Unknown and a
    /// counterexample that depends on the havocked slots is OverApproximation.
    /// How a store through `*local_idx` relates to its ref target's type
    /// ([`Self::mirror_scalar_ref_store`]).
    pub(in crate::codegen_ay::chc) fn ref_store_reinterpretation(
        &self,
        ref_target: &RefTarget,
        lhs: &Place,
        rhs_expr: &Expr,
        local_idx: usize,
        modified: &std::collections::HashSet<usize>,
    ) -> RefStoreReinterpretation {
        use crate::codegen_ay::chc::stmt::codegen_stmt_transmute_layout::AggregateTransmute;
        // `Place::ty` indexes the body's locals and panics on one outside it.
        let n_locals = self.body.locals().len();
        if local_idx >= n_locals || ref_target.local >= n_locals {
            return RefStoreReinterpretation::SameType;
        }
        let written_ty = Place { local: local_idx, projection: vec![ProjectionElem::Deref] }
            .ty(self.body.locals())
            .ok()
            .map(|ty| self.resolve_body_ty(ty));
        let referent_ty =
            Place { local: ref_target.local, projection: ref_target.projections.clone() }
                .ty(self.body.locals())
                .ok()
                .map(|ty| self.resolve_body_ty(ty));
        let (Some(written_ty), Some(referent_ty)) = (written_ty, referent_ty) else {
            return RefStoreReinterpretation::SameType;
        };
        if written_ty == referent_ty {
            // A store of the referent's own type through a raw pointer whose
            // definition chain puts it at a nonzero byte offset from the
            // referent that no offset metadata records (`(&mut p.a as *mut
            // u32 as *mut u8).byte_add(4) as *mut u32`) writes the bytes there,
            // not the referent: mirrored as the same type, `*d = 7` wrote
            // `p.a`, a clean proof where Kani writes `p.b`, and its twin a
            // certified false counterexample (self-review of round 10 of
            // fix/chc-false-certificates, `q_step.rs` st01, st03; the same on
            // main f5dfb8d48). The wider-store lane splices them into the
            // containing local at that offset, or reports the store out of
            // bounds, or fails closed.
            let is_raw = matches!(
                self.resolve_body_ty(self.body.locals()[local_idx].ty).kind(),
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::RawPtr(..))
            );
            if is_raw
                && !self.ref_resolution.subslice_offset.contains_key(&local_idx)
                && let Some(chain) = self.store_pointer_referent_byte_offset(local_idx, ref_target)
                && chain != 0
                && let Some(written) = written_ty
                    .layout()
                    .ok()
                    .and_then(|l| usize::try_from(l.shape().size.bytes()).ok())
            {
                return self.wider_ref_store(
                    ref_target, lhs, rhs_expr, written_ty, written, local_idx, modified,
                );
            }
            return RefStoreReinterpretation::SameType;
        }
        // A NARROWER store through a pointer cast writes only some of the
        // referent's bytes: a `u16` into a struct, a `u32` into a `u64`. Mirrored
        // as the same type, the narrow value replaced the whole register,
        // zero-extended (review probes p_store_width.rs `s_u16_store_bug` /
        // `scalar_partial_store_bug` SUCCESSFUL where Kani fails, their safe
        // twins FAILED certified Genuine). The referent is its old image with
        // those bytes spliced in AT THE POINTER'S OFFSET, or fresh when the lane
        // cannot build it. The ref target does not carry that offset: the
        // pointer's definition chain in this body must establish it
        // (`store_pointer_referent_byte_offset`), or the store is not modeled.
        // Splicing at offset 0 regardless proved `*p.byte_add(3) = 0` cleared
        // the LOW byte (third review: `ns_byte_add_bug`, `of_byte_add_store_bug`,
        // `o2_byte_sub_bug`, clean proofs where main and Kani fail).
        let size_of = |ty: rustc_public::ty::Ty| ty.layout().ok().map(|l| l.shape().size.bytes());
        // A pointer to an array's (or a SIMD vector's) element type addresses an
        // ELEMENT: the element-wise store below places it at the index the
        // offset metadata records (`subslice_offset`, 0 without it). A byte step
        // that metadata does not record (`p.byte_add(2)` on a `*mut u16` into a
        // `[u16; 4]`) put the element at index 0 (`o2_elem_byte_add_store_bug`, a
        // clean proof on main and the branch); the chain must agree with the
        // metadata or the store is not modeled.
        let element_store = self
            .get_array_element_ty(referent_ty)
            .is_some_and(|elem| self.resolve_body_ty(elem) == written_ty);
        if element_store {
            let tracked_elems = match self.ref_resolution.subslice_offset.get(&local_idx) {
                None => Some(0i128),
                Some(offset) => {
                    Self::const_usize_from_expr(offset).and_then(|o| i128::try_from(o).ok())
                }
            };
            let elem_bytes = size_of(written_ty).and_then(|b| i128::try_from(b).ok());
            let agrees = match (
                tracked_elems.zip(elem_bytes).and_then(|(n, b)| n.checked_mul(b)),
                self.store_pointer_referent_byte_offset(local_idx, ref_target),
            ) {
                (Some(tracked), Some(chain)) => tracked == chain,
                _ => false,
            };
            if !agrees {
                return RefStoreReinterpretation::Unmodeled(
                    "an element store through a pointer whose offset its metadata does not record",
                );
            }
        }
        // A referent that IS a pointer to the written type — a `Box<T>`, a `&T`,
        // a `*mut T`, a `Unique<T>` written with a `T` — names that pointee
        // through other lanes: `Box::as_mut` writes the pointee through a
        // reference whose ref target is the box itself, and the store reaches
        // the pointee, not the box's bytes. It keeps the same-type mirror
        // unless the pointer's definition chain ends at a borrow of the
        // referent itself (a reference into the pointee, `&mut *b`, has no such
        // chain): then the pointer is at the referent's own bytes.
        //
        // Every other narrower store writes the referent's own bytes, whatever
        // the referent holds: a union (whose image is its bitvector), a struct
        // with a pointer field (whose pointer bytes are its address, converted
        // both ways the way a transmute does), plain data. The first cut
        // spliced only referents holding no address and mirrored the rest as
        // the same type, which wrote the narrow value, zero-extended, over the
        // whole referent and ignored the offset: `*(&mut u as *mut U as *mut
        // u16).byte_add(2) = 3` left a union's `h[0] == 3` provable and
        // certified `h[1] == 3` a Genuine counterexample (fourth review of
        // fix/chc-false-certificates, 2026-09-28: `us_off2_u16_bug`,
        // `us_sp_y_bug`, `us2_up_hi_bug`, `ob_union_h_bug` clean proofs where
        // Kani fails, on main and the branch). A referent the image lane cannot
        // build fails closed below.
        if self.ty_is_pointer_to(referent_ty, written_ty, 4)
            && self.store_pointer_referent_byte_offset(local_idx, ref_target).is_none()
        {
            return RefStoreReinterpretation::SameType;
        }
        // A WIDER store through a pointer cast writes past the referent: into
        // the rest of the local that contains it, or past that local's end.
        // Mirrored as the same type, it wrote the referent's register with no
        // allocation bound and no bytes past the referent, so `*(&mut x as *mut
        // u32 as *mut u64) = 1` and a widened field pointer's store were clean
        // proofs where Kani reports a pointer outside object bounds, and `s.y`
        // kept its value after a store through `&mut s.x as *mut u64` (first
        // review of the sixth round, 2026-10-02: `p_store_width.rs`
        // `scalar_wide_store_oob_bug`, `r1g.rs`, `r1h.rs`, `r1k.rs`).
        // A store of the referent's own size at a nonzero offset from it (`*(a
        // .as_mut_ptr().add(1) as *mut u64) = 1` into a `[u32; 2]`) also writes
        // past it; read at offset 0 it was not modeled (or, through the
        // same-size transmute below, written at the wrong offset).
        let chain = self.store_pointer_referent_byte_offset(local_idx, ref_target);
        if !element_store
            && let (Some(written), Some(referent_size)) =
                (size_of(written_ty), size_of(referent_ty))
            && (written > referent_size
                || (written == referent_size && chain.is_some_and(|offset| offset != 0)))
        {
            return self.wider_ref_store(
                ref_target, lhs, rhs_expr, written_ty, written, local_idx, modified,
            );
        }
        if !element_store
            && let (Some(written), Some(total)) = (size_of(written_ty), size_of(referent_ty))
            && written > 0
            && written < total
        {
            if lhs.projection.len() != 1 || !ref_target.projections.is_empty() {
                return RefStoreReinterpretation::Unmodeled(
                    "a narrower store through a pointer cast into a sub-place",
                );
            }
            let Some(offset) = self.store_pointer_referent_byte_offset(local_idx, ref_target)
            else {
                return RefStoreReinterpretation::Unmodeled(
                    "a narrower store through a pointer whose offset its definition chain does not establish",
                );
            };
            let Some(offset) = usize::try_from(offset)
                .ok()
                .filter(|&o| o.checked_add(written).is_some_and(|end| end <= total))
                .and_then(|o| u64::try_from(o).ok())
            else {
                return RefStoreReinterpretation::Unmodeled(
                    "a narrower store through a pointer cast outside its referent",
                );
            };
            let referent = Place { local: ref_target.local, projection: Vec::new() };
            let Some(old) = self.translate_place_with_modified(&referent, modified) else {
                return RefStoreReinterpretation::Unmodeled("the referent's value is unavailable");
            };
            use crate::codegen_ay::chc::stmt::codegen_stmt_union_bits::UnionLane;
            return match self.splice_bytes_at(&old, referent_ty, rhs_expr, written_ty, offset) {
                UnionLane::Exact(value) => RefStoreReinterpretation::Converted(value),
                UnionLane::Unmodeled(why) => RefStoreReinterpretation::Unmodeled(why),
            };
        }
        if !self.transmute_aggregate_memory_order_applies(written_ty, referent_ty) {
            return RefStoreReinterpretation::SameType;
        }
        if lhs.projection.len() != 1 || !ref_target.projections.is_empty() {
            return RefStoreReinterpretation::Unmodeled(
                "a field store or a sub-place target through a pointer cast",
            );
        }
        // The whole referent re-read in its layout: only at its start. A
        // pointer with recorded offset metadata whose chain does not put it at
        // offset 0 is not modeled.
        if self.ref_resolution.subslice_offset.contains_key(&local_idx) && chain != Some(0) {
            return RefStoreReinterpretation::Unmodeled(
                "a same-size store through a pointer whose offset its definition chain does not establish",
            );
        }
        match self.transmute_aggregate_memory_order(rhs_expr, written_ty, referent_ty) {
            AggregateTransmute::Precise(value) => RefStoreReinterpretation::Converted(value),
            AggregateTransmute::NotApplicable => {
                RefStoreReinterpretation::Unmodeled("stored value is not its type's encoding")
            }
            AggregateTransmute::Unsupported(why) => RefStoreReinterpretation::Unmodeled(why),
        }
    }

    /// [`Self::ref_store_reinterpretation`] for a store of `written` bytes,
    /// wider than its referent: the bytes land at the referent's offset in its
    /// containing local plus the pointer's offset from the referent
    /// (`store_pointer_referent_byte_offset`). Inside the local they are
    /// spliced into the local's whole image (`ConvertedLocal`); past its end
    /// the store is out of bounds; an offset the definition chain does not
    /// establish is not modeled.
    #[allow(clippy::too_many_arguments)]
    fn wider_ref_store(
        &self,
        ref_target: &RefTarget,
        lhs: &Place,
        rhs_expr: &Expr,
        written_ty: rustc_public::ty::Ty,
        written: usize,
        local_idx: usize,
        modified: &std::collections::HashSet<usize>,
    ) -> RefStoreReinterpretation {
        let local_ty = self.resolve_body_ty(self.body.locals()[ref_target.local].ty);
        let Some(local_size) =
            local_ty.layout().ok().and_then(|l| usize::try_from(l.shape().size.bytes()).ok())
        else {
            return RefStoreReinterpretation::Unmodeled(
                "a wider store into a local of unknown size",
            );
        };
        let Some(field_offset) = self.field_path_byte_offset(local_ty, &ref_target.projections)
        else {
            return RefStoreReinterpretation::Unmodeled(
                "a wider store through a referent whose offset in its local is unknown",
            );
        };
        let Some(chain) = self.store_pointer_referent_byte_offset(local_idx, ref_target) else {
            return RefStoreReinterpretation::Unmodeled(
                "a wider store through a pointer whose offset its definition chain does not establish",
            );
        };
        let start = i128::from(field_offset) + chain;
        let end = start + written as i128;
        if start < 0 || end > local_size as i128 {
            return RefStoreReinterpretation::OutOfBounds;
        }
        if lhs.projection.len() != 1 {
            return RefStoreReinterpretation::Unmodeled(
                "a wider store with a projection past the deref",
            );
        }
        let Ok(offset) = u64::try_from(start) else {
            return RefStoreReinterpretation::OutOfBounds;
        };
        // The store covers the whole local: its value read back in the local's
        // layout, as a same-size store through a pointer cast is.
        if offset == 0 && written == local_size {
            use crate::codegen_ay::chc::stmt::codegen_stmt_transmute_layout::AggregateTransmute;
            if self.transmute_aggregate_memory_order_applies(written_ty, local_ty) {
                return match self.transmute_aggregate_memory_order(rhs_expr, written_ty, local_ty) {
                    AggregateTransmute::Precise(value) => {
                        RefStoreReinterpretation::ConvertedLocal(value)
                    }
                    AggregateTransmute::NotApplicable => RefStoreReinterpretation::Unmodeled(
                        "stored value is not its type's encoding",
                    ),
                    AggregateTransmute::Unsupported(why) => {
                        RefStoreReinterpretation::Unmodeled(why)
                    }
                };
            }
            let local_sort = Self::translate_ty(local_ty);
            return if local_sort.is_some() && local_sort.as_ref() == Some(rhs_expr.sort()) {
                RefStoreReinterpretation::ConvertedLocal(rhs_expr.clone())
            } else {
                RefStoreReinterpretation::Unmodeled("a whole-local store of another encoding")
            };
        }
        let local = Place { local: ref_target.local, projection: Vec::new() };
        let Some(old) = self.translate_place_with_modified(&local, modified) else {
            return RefStoreReinterpretation::Unmodeled(
                "the containing local's value is unavailable",
            );
        };
        use crate::codegen_ay::chc::stmt::codegen_stmt_union_bits::UnionLane;
        match self.splice_bytes_at(&old, local_ty, rhs_expr, written_ty, offset) {
            UnionLane::Exact(value) => RefStoreReinterpretation::ConvertedLocal(value),
            UnionLane::Unmodeled(why) => RefStoreReinterpretation::Unmodeled(why),
        }
    }

    /// The byte offset of a place's FIELD projection path within `ty` (struct
    /// and tuple fields only), from the layout.
    pub(in crate::codegen_ay::chc) fn field_path_byte_offset(
        &self,
        ty: rustc_public::ty::Ty,
        projections: &[ProjectionElem],
    ) -> Option<u64> {
        let mut ty = ty;
        let mut offset = 0u64;
        for projection in projections {
            let ProjectionElem::Field(index, field_ty) = projection else { return None };
            let layout = ty.layout().ok()?;
            let rustc_public::abi::FieldsShape::Arbitrary { offsets } = layout.shape().fields
            else {
                return None;
            };
            offset = offset.checked_add(offsets.get(*index)?.bytes() as u64)?;
            ty = self.resolve_body_ty(*field_ty);
        }
        Some(offset)
    }

    /// Whether a value of `ty` is a pointer to `pointee`: a reference, a raw
    /// pointer or a `Box` of it, or a struct whose one non-zero-sized field is
    /// such a pointer (`Unique<T>`, `NonNull<T>`, a newtype), to `depth`
    /// levels.
    fn ty_is_pointer_to(
        &self,
        ty: rustc_public::ty::Ty,
        pointee: rustc_public::ty::Ty,
        depth: usize,
    ) -> bool {
        if depth == 0 {
            return false;
        }
        match self.resolve_body_ty(ty).kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => {
                self.resolve_body_ty(inner) == pointee
            }
            TyKind::RigidTy(RigidTy::Adt(def, args))
                if matches!(def.name().as_str(), "std::boxed::Box" | "alloc::boxed::Box") =>
            {
                matches!(
                    args.0.first(),
                    Some(rustc_public::ty::GenericArgKind::Type(inner))
                        if self.resolve_body_ty(*inner) == pointee
                )
            }
            TyKind::RigidTy(RigidTy::Adt(def, args))
                if def.kind() == rustc_public::ty::AdtKind::Struct =>
            {
                let Some(variant) = def.variants_iter().next() else { return false };
                // A field type Rule A refuses (`mono_ty::field_ty`) answers
                // "not a pointer": the store is reinterpreted or fails closed.
                let Some(fields) = variant
                    .fields()
                    .iter()
                    .map(|f| mono_ty::field_ty(f, &args))
                    .collect::<Option<Vec<_>>>()
                else {
                    return false;
                };
                let mut data = fields.into_iter().filter(|field_ty| {
                    self.resolve_body_ty(*field_ty)
                        .layout()
                        .ok()
                        .is_none_or(|layout| layout.shape().size.bytes() != 0)
                });
                match (data.next(), data.next()) {
                    (Some(only), None) => self.ty_is_pointer_to(only, pointee, depth - 1),
                    _ => false,
                }
            }
            _ => false,
        }
    }

    pub(in crate::codegen_ay::chc) fn fail_close_ref_mirror(
        &mut self,
        target_local: usize,
        reason: &'static str,
        acc: &mut StmtAccumulator<'_>,
    ) {
        self.havoc_local_fail_closed(target_local, reason, acc);
        warn!(target_local, reason, "CHC: Mem-level Deref register mirror failed closed");
    }

    /// Give every register slot of `target_local` its free output variable,
    /// drop every cached value of it, and record the unblessed `reason`.
    ///
    /// For a flattened local each slot has its own constraint key, so this
    /// registers `true` under every one of them; `projection_sound_fallback`
    /// registers only the local's own key, which frees slot 0 and leaves the
    /// others on their input values (the store they were meant to take is
    /// lost). Unlisted reasons default to `FallbackSoundness::FailClose`.
    pub(in crate::codegen_ay::chc) fn havoc_local_fail_closed(
        &mut self,
        target_local: usize,
        reason: &'static str,
        acc: &mut StmtAccumulator<'_>,
    ) {
        self.record_sound_fallback_reason(reason);
        if self.flatten.flattened_tuple_locals.contains(&target_local) {
            for slot in 0..self.flattened_field_count(target_local) {
                let key = self.flattened_field_constraint_key(target_local, slot);
                acc.replace_constraint(key, Expr::bool_const(true));
            }
        } else {
            acc.replace_constraint(target_local, Expr::bool_const(true));
        }
        self.encode.flattened_field_env.retain(|&(local, _), _| local != target_local);
        self.encode.local_expr_env.remove(&target_local);
        self.encode.invalidate_local_cache(target_local);
        acc.modified.insert(target_local);
    }

    /// Mirror a scalar/field ref store into register state.
    ///
    /// Part of #2278: Mem-level *ref stores must mirror into register state for
    /// scalar/field ref targets so subsequent deref reads via ref_targets don't
    /// observe stale __in values.
    pub(in crate::codegen_ay::chc) fn mirror_scalar_ref_store(
        &mut self,
        ref_target: &RefTarget,
        lhs: &Place,
        rhs_expr: &Expr,
        local_idx: usize,
        store_ty: rustc_public::ty::Ty,
        acc: &mut StmtAccumulator<'_>,
    ) {
        let target_local = ref_target.local;
        // The caller has emitted the physical memory write already. An
        // authenticated native Vec accessor addresses its buffer, not the
        // owner header named by ref_targets. Never splice this element into
        // or havoc that header; later logical-model reads retain their own
        // vec_model_read_after_buffer_write refusal.
        if lhs.projection.as_slice() == [rustc_public::mir::ProjectionElem::Deref]
            && self.native_vec_primitive_store_owner(local_idx, ref_target, store_ty)
                == Some(target_local)
        {
            // Custody alone does not synchronize Vec.data. Close or refuse
            // every reverse owner/model alias path before preserving header
            // fields; this runs independently of printed buffer-root names.
            self.book_native_vec_store_model_boundary(local_idx, target_local);
            return;
        }
        // Part of #3768: graceful fallback instead of panic
        let Some(target_vec_idx) = self.try_state_idx_for_local(target_local) else {
            debug!(target_local, "CHC: scalar ref store target not in state map — skipping");
            self.record_sound_fallback_reason("state_idx_missing_scalar_ref_store");
            return;
        };
        // Part of #3041/#3223: Track Downcast projections as cons_idx on subsequent Field.
        let mut combined_field_projs =
            collect_field_projections(&ref_target.projections, UnknownProjectionPolicy::Skip);
        combined_field_projs.extend(collect_field_projections(
            &lhs.projection[1..],
            UnknownProjectionPolicy::Break,
        ));

        // Part of #2323: when ref_targets resolves to a pointer-valued
        // field (for example Closure.cap0: &mut T), `*ref = value` should
        // update pointee memory, not overwrite the pointer field itself.
        // Skip register mirroring in this shape to avoid corrupting the
        // captured pointer local (which can fabricate pointer CTREX paths).
        let mirrors_pointer_field = combined_field_projs
            .last()
            .and_then(|proj| proj.field_ty)
            .and_then(|field_ty| match field_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)) => {
                    ChcCtx::deref_pointee_ty(field_ty)
                }
                TyKind::RigidTy(RigidTy::Adt(def, _))
                    if def.name() == "std::boxed::Box" || def.name() == "alloc::boxed::Box" =>
                {
                    ChcCtx::deref_pointee_ty(field_ty)
                }
                _ => None, // external enum: TyKind
            })
            .is_some_and(|field_pointee| field_pointee == store_ty);
        if mirrors_pointer_field {
            debug!(
                target_local,
                ref_local = local_idx,
                "CHC: skipped Mem-level Deref register mirror for pointer-valued ref_target field"
            );
            return;
        }

        // A store through a POINTER CAST between the reference and its target
        // (`*(&mut w as *mut Words as *mut u128) = v`) writes the target's bytes
        // as another type of the SAME size. Mirroring the u128 into the struct's
        // register did not reinterpret it, and the struct's fields kept their
        // old values: `w.lo == 5` after writing `5 | (6 << 64)` FAILED certified
        // Genuine (review probe p1_ptr_cast.rs `write_through_safe`). Write the
        // value read back in the target's layout, or give the target a fresh
        // value when the layout lane does not model the store.
        let converted;
        let mut whole_referent = false;
        let rhs_expr = match self.ref_store_reinterpretation(
            ref_target,
            lhs,
            rhs_expr,
            local_idx,
            acc.modified,
        ) {
            RefStoreReinterpretation::SameType => rhs_expr,
            RefStoreReinterpretation::Converted(value) => {
                converted = value;
                whole_referent = true;
                &converted
            }
            // A wider store inside the containing local: the value is the WHOLE
            // local's, written along no projection.
            RefStoreReinterpretation::ConvertedLocal(value) => {
                converted = value;
                whole_referent = true;
                combined_field_projs.clear();
                &converted
            }
            RefStoreReinterpretation::OutOfBounds => {
                self.record_block_violation(Expr::bool_const(true), OUT_OF_BOUNDS_MESSAGE);
                return;
            }
            RefStoreReinterpretation::Unmodeled(why) => {
                warn!(
                    target_local,
                    ref_local = local_idx,
                    why,
                    "CHC: pointer-cast store not modeled"
                );
                // A ref target that names another place than the reference's
                // pointee (`(*r).f = v` with the target's own type not `*r`'s)
                // is refused by the join check first, as before the wider
                // stores were modeled.
                let reason = if lhs.projection.len() != 1
                    && self.ref_mirror_join_check(ref_target, local_idx).is_err()
                {
                    "deref_mirror_ref_target_join_mismatch"
                } else {
                    "transmute_layout_fallback"
                };
                self.fail_close_ref_mirror(target_local, reason, acc);
                return;
            }
        };

        // R4: the composed path is the ref_target's projections (relative to
        // the target) followed by the store's projections after the Deref
        // (relative to the reference's pointee). Every arm below writes along
        // that path, so check the join once, before any of them.
        // A reinterpreted store is the WHOLE referent's new value, in the
        // referent's own type (`ref_store_reinterpretation` requires a store
        // with no projection past the deref into a target with none), so the
        // pointee type the join compares against is not the value's.
        let join = if whole_referent {
            Ok(RefTargetJoin::Place)
        } else {
            self.ref_mirror_join_check(ref_target, local_idx)
        };
        match join {
            Ok(RefTargetJoin::Place) => {}
            Ok(RefTargetJoin::ThroughPointer) => {
                debug!(
                    target_local,
                    ref_local = local_idx,
                    "CHC: skipped Mem-level Deref register mirror: the reference points through \
                     a pointer-typed ref_target place"
                );
                return;
            }
            Err(why) => {
                warn!(
                    target_local,
                    ref_local = local_idx,
                    why,
                    "CHC: Mem-level Deref mirror refused the ref_target join"
                );
                self.fail_close_ref_mirror(
                    target_local,
                    "deref_mirror_ref_target_join_mismatch",
                    acc,
                );
                return;
            }
        }

        // Part of #3814: Detect Field+Index pattern — when the LHS after Deref
        // contains an Index/ConstantIndex following the Field projections,
        // the store targets an array element, not the whole array field.
        // collect_field_projections with Break stops at the Index, so we
        // scan for it separately and build array.store(idx, val).
        let index_proj = lhs.projection[1..]
            .iter()
            .find(|p| matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }));
        if let Some(index_proj) = index_proj {
            if let Some(field_proj) = combined_field_projs.first() {
                let index_expr = match index_proj {
                    ProjectionElem::Index(index_local) => {
                        let idx_local: usize = *index_local;
                        self.resolve_local_expr(idx_local, &acc.modified)
                    }
                    ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                        // #from_end: needs the slice's runtime length -> fail closed (projection_path.rs)
                        constant_index_offset(*offset, *min_length, *from_end)
                            .map(|i| Expr::bitvec_const(i as u128, POINTER_WIDTH))
                    }
                    _ => None,
                };
                if let Some(index_expr) = index_expr {
                    let index_expr = coerce_bitvec_width_safe(
                        index_expr,
                        POINTER_WIDTH,
                        SignExtension::ZeroExtend,
                    );
                    // The array's slot is the one the whole field path names,
                    // placed as the read side places it; the first field's raw
                    // index is another slot whenever an earlier field has more
                    // than one leaf or the path is nested.
                    let array_slot = if self.flatten.flattened_tuple_locals.contains(&target_local)
                    {
                        self.faithful_nested_flat_slot(target_local, &combined_field_projs).ok()
                    } else {
                        None
                    };
                    let field_idx = array_slot.unwrap_or(field_proj.field_idx);
                    let arr_in = array_slot.and_then(|slot| {
                        self.flattened_local_field_expr(target_local, slot, &acc.modified)
                    });
                    if let Some(arr_in) = arr_in {
                        if arr_in.sort().is_array() {
                            let coerced_rhs = ChcCtx::coerce_store_value(
                                arr_in.sort(),
                                rhs_expr.clone(),
                                false,
                                &self.diagnostics,
                            );
                            let updated_array = arr_in.store(index_expr, coerced_rhs);
                            debug!(
                                target_local,
                                ref_local = local_idx,
                                field_idx,
                                "CHC: Field+Index mirror store on flattened local (#3814)"
                            );
                            let slot_proj = FieldProjection {
                                field_idx,
                                cons_idx: None,
                                field_ty: combined_field_projs.last().and_then(|fp| fp.field_ty),
                            };
                            self.mirror_flattened_field_store(
                                &slot_proj,
                                &updated_array,
                                local_idx,
                                target_local,
                                target_vec_idx,
                                acc,
                            );
                            return;
                        }
                    }
                }
            }
            // Fall through to existing paths if index resolution fails
        }

        let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(target_vec_idx).cloned()
        else {
            warn!(
                target_local,
                ref_local = local_idx,
                "CHC: skipped Mem-level Deref register mirror — missing output state var"
            );
            self.fail_close_ref_mirror(target_local, "deref_mirror_output_var_missing", acc);
            return;
        };

        if let Some(opaque_post_store_expr) = self.try_build_opaque_iterator_adapter_store_expr(
            target_local,
            &out_sort,
            &combined_field_projs,
        ) {
            let out_var = Expr::var(&*out_name, out_sort.clone());
            if let Some(constraint) =
                coerce_eq_constraint(&out_var, opaque_post_store_expr.clone(), &out_sort, false)
            {
                acc.replace_constraint(target_local, constraint);
                self.encode.local_expr_env.insert(target_local, opaque_post_store_expr);
                acc.modified.insert(target_local);
            } else {
                warn!(
                    target_local,
                    ref_local = local_idx,
                    "CHC: opaque iterator adapter post-store sort mismatch"
                );
                self.fail_close_ref_mirror(target_local, "deref_mirror_sort_mismatch", acc);
            }
        } else if combined_field_projs.is_empty() {
            // Part of #2876: When target is flattened and RHS is a Datatype
            // (whole struct store through deref), decompose into per-field
            // constraints instead of trying to equate scalar with Datatype.
            if self.flatten.flattened_tuple_locals.contains(&target_local)
                && rhs_expr.sort().is_datatype()
            {
                if let Some(dt) = rhs_expr.sort().datatype_sort()
                    && dt.constructors.len() == 1
                {
                    let ctor = &dt.constructors[0];
                    let n_fields = ctor.fields.len();
                    let mut values: Vec<Option<Expr>> = Vec::with_capacity(n_fields);
                    for field in &ctor.fields {
                        values.push(Some(rhs_expr.clone().field_select(
                            &dt.name,
                            &field.name,
                            field.sort.clone(),
                        )));
                    }
                    self.constrain_flattened_fields(target_local, &values, acc);
                } else {
                    warn!(
                        target_local,
                        ref_local = local_idx,
                        "CHC: Mem-level Deref mirror — multi-constructor Datatype to flattened local"
                    );
                    self.fail_close_ref_mirror(
                        target_local,
                        "deref_mirror_whole_store_unsupported",
                        acc,
                    );
                }
            } else {
                let out_var = Expr::var(&*out_name, out_sort.clone());
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, rhs_expr.clone(), &out_sort, false)
                {
                    acc.replace_constraint(target_local, constraint);
                    self.encode.local_expr_env.insert(target_local, rhs_expr.clone());
                    acc.modified.insert(target_local);
                } else {
                    warn!(
                        target_local,
                        ref_local = local_idx,
                        "CHC: Mem-level Deref scalar mirror sort mismatch"
                    );
                    self.fail_close_ref_mirror(target_local, "deref_mirror_sort_mismatch", acc);
                }
            }
        } else if self.flatten.flattened_tuple_locals.contains(&target_local)
            && !self.collections.projection_locals.contains_key(&target_local)
            && combined_field_projs.iter().all(|fp| fp.cons_idx.is_none())
        {
            // A Field path into a flattened struct, tuple or closure owner, of
            // any depth: `r.c = 7`, `r.inner.a = 7`, `r.inner = Q { .. }`.
            // Placed before the datatype test, which looks only at slot 0 (a
            // depth-capped datatype slot would send the whole path there).
            self.mirror_flat_struct_path_store(
                target_local,
                &combined_field_projs,
                rhs_expr,
                local_idx,
                acc,
            );
        } else if out_sort.is_datatype() {
            let target =
                DatatypeMirrorTarget { ref_local: local_idx, target_local, target_vec_idx };
            self.mirror_datatype_field_store(&target, &combined_field_projs, rhs_expr, acc);
        } else if combined_field_projs.len() == 1
            && self.flatten.flattened_tuple_locals.contains(&target_local)
            && !self.collections.projection_locals.contains_key(&target_local)
        {
            // Only an enum `Downcast + Field` path on a flattened enum is left
            // here (struct paths took the arm above). Its raw field index is
            // not its slot: the discriminant and the layout's payload slots
            // come first, so the old raw-index write landed on the wrong slot.
            warn!(
                target_local,
                ref_local = local_idx,
                "CHC: Mem-level Deref mirror of a flattened enum payload field"
            );
            self.fail_close_ref_mirror(target_local, "deref_mirror_flat_path_unresolved", acc);
        } else if combined_field_projs.len() == 1 {
            // Collection projection locals (#2912 VecIntoIter identity) and
            // targets with a single state variable.
            self.mirror_flattened_field_store(
                &combined_field_projs[0],
                rhs_expr,
                local_idx,
                target_local,
                target_vec_idx,
                acc,
            );
        } else if self.flatten.flattened_tuple_locals.contains(&target_local)
            && combined_field_projs.len() >= 2
            && combined_field_projs[0].cons_idx.is_some()
        {
            // Part of #435: Flattened enum with struct payload (e.g., Option<Point>).
            // combined_field_projs = [Downcast+Field(payload), Field(inner_field)].
            // Map the nested projection to the correct scalar slot:
            //   payload_start (1 for Option) + inner field offset.
            let n_fields = self.flattened_field_count(target_local);
            let cons_idx_val =
                combined_field_projs[0].cons_idx.expect("invariant: guard checked is_some()");
            let payload_field_idx = combined_field_projs[0].field_idx;
            let payload_start = if let Some(layout) =
                self.flatten.enum_bv_layouts.get(&target_local)
                && cons_idx_val < layout.ctor_field_slot.len()
                && payload_field_idx < layout.ctor_field_slot[cons_idx_val].len()
            {
                let Some(payload_slot) = layout.payload_slot(cons_idx_val, payload_field_idx)
                else {
                    // An omitted payload slot is a zero-sized field
                    // (`decl/codegen_decl_state_vars_enum_layout.rs`); every
                    // field inside it is zero-sized too, so the store changes
                    // no register state and there is nothing to lose.
                    warn!(
                        target_local,
                        cons_idx_val,
                        payload_field_idx,
                        "CHC: nested flattened enum mirror targeted omitted payload slot"
                    );
                    return;
                };
                1 + payload_slot
            } else if n_fields == 1 {
                // Part of #3041: Single-variant enum, no discriminant — payload IS fld0
                0
            } else if n_fields == 3 {
                let true_discr = self
                    .flatten
                    .flattened_enum_discr
                    .get(&target_local)
                    .map(|(t, _)| *t)
                    .unwrap_or(0);
                if (cons_idx_val as u64) == true_discr { 1 } else { 2 }
            } else {
                1 // 2-field enum: payload at fld1
            };

            // Follow-up (a): the nested offset inside the payload must come
            // from the payload's sort. The old fallback used the raw index of
            // the first inner field, which is a different slot whenever an
            // earlier payload field has more than one leaf. The inner path is
            // checked against the payload's MIR type first (C5b,
            // `flat_field_path_from`): a step `translate_ty` collapses has no
            // level in the payload's sort.
            let inner_indices: Option<Vec<usize>> = combined_field_projs[0]
                .field_ty
                .and_then(|payload_ty| {
                    Self::flat_field_path_from(payload_ty, &combined_field_projs[1..]).ok()
                })
                .filter(|inner| !inner.is_empty() && inner.iter().all(|fp| fp.cons_idx.is_none()))
                .map(|inner| inner.iter().map(|fp| fp.field_idx).collect());
            let inner_offset = if let Some(inner_indices) = inner_indices
                && let Some(payload_ty) = combined_field_projs[0].field_ty
                && let Some(local_decl) = self.body.locals().get(target_local)
                && let Some(sort) = <Self as CodegenTypes>::translate_ty(local_decl.ty)
                && let Some(dt) = sort.datatype_sort()
                && let Some(variant) = dt.constructors.get(cons_idx_val)
                && let Some(payload) = variant.fields.get(payload_field_idx)
                && <Self as CodegenTypes>::translate_ty(payload_ty).as_ref() == Some(&payload.sort)
            {
                crate::codegen_ay::chc::codegen_decl_flatten::compute_nested_flat_slot(
                    &payload.sort,
                    &inner_indices,
                )
            } else {
                None
            };
            let Some(inner_offset) = inner_offset else {
                warn!(
                    target_local,
                    ref_local = local_idx,
                    cons_idx_val,
                    payload_field_idx,
                    "CHC: nested flattened enum mirror payload offset unresolved"
                );
                self.fail_close_ref_mirror(target_local, "deref_mirror_flat_path_unresolved", acc);
                return;
            };

            let target_slot = payload_start + inner_offset;
            let corrected_proj = FieldProjection {
                field_idx: target_slot,
                cons_idx: None,
                field_ty: combined_field_projs.last().and_then(|fp| fp.field_ty),
            };
            debug!(
                target_local,
                ref_local = local_idx,
                payload_start,
                inner_offset,
                target_slot,
                "CHC: Downcast+nested field mirror on flattened enum (#435)"
            );
            self.mirror_flattened_field_store(
                &corrected_proj,
                rhs_expr,
                local_idx,
                target_local,
                target_vec_idx,
                acc,
            );
        } else {
            // A nested field path (two or more Field projections, no enum
            // Downcast) on a flattened struct whose first slot is a scalar:
            // `let r = &mut o; r.inner.a = 7;`. This arm used to warn and
            // return, which lost the write -- `assert!(o.inner.a == 0)` was
            // proved (tools/soundness-duals/nested_field_ref_write_dual.rs).
            warn!(
                target_local,
                ref_local = local_idx,
                field_count = combined_field_projs.len(),
                "CHC: unsupported nested flattened field mirror for Mem-level Deref store"
            );
            self.fail_close_ref_mirror(target_local, "deref_mirror_flat_path_unresolved", acc);
        }
    }

    /// Mirror a deref store into a datatype-sorted register field.
    fn mirror_datatype_field_store(
        &mut self,
        target: &DatatypeMirrorTarget,
        combined_field_projs: &[FieldProjection],
        rhs_expr: &Expr,
        acc: &mut StmtAccumulator<'_>,
    ) {
        let target_local = target.target_local;
        let target_vec_idx = target.target_vec_idx;
        let ref_local = target.ref_local;
        let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(target_vec_idx).cloned()
        else {
            warn!(
                target_local,
                ref_local,
                "CHC: skipped Mem-level Deref aggregate mirror — missing output state var"
            );
            self.fail_close_ref_mirror(target_local, "deref_mirror_output_var_missing", acc);
            return;
        };
        let out_var = Expr::var(&*out_name, out_sort.clone());
        let root_in = if acc.modified.contains(&target_local) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&target_local) {
                env_expr.clone()
            } else {
                Expr::var(&*out_name, out_sort.clone())
            }
        } else {
            self.state_var_mgr.state_vars.get(target_vec_idx).map_or_else(
                || Expr::var(&*out_name, out_sort.clone()),
                |(n, s)| Expr::var(&**n, s.clone()),
            )
        };

        match ChcCtx::apply_projection_update(&root_in, combined_field_projs, rhs_expr.clone()) {
            Some(mirrored_expr) => {
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, mirrored_expr.clone(), &out_sort, false)
                {
                    acc.replace_constraint(target_local, constraint);
                    self.encode.local_expr_env.insert(target_local, mirrored_expr);
                    acc.modified.insert(target_local);
                } else {
                    warn!(
                        target_local,
                        ref_local, "CHC: Mem-level Deref aggregate mirror sort mismatch"
                    );
                    self.fail_close_ref_mirror(target_local, "deref_mirror_sort_mismatch", acc);
                }
            }
            None => {
                if self.is_unmodeled_vec_into_iter_projection(
                    target_local,
                    &out_sort,
                    combined_field_projs,
                ) {
                    debug!(
                        target_local,
                        ref_local,
                        "CHC: VecIntoIter unmodeled projection in datatype mirror — emitting identity transition"
                    );
                    if let Some(constraint) =
                        coerce_eq_constraint(&out_var, root_in.clone(), &out_sort, false)
                    {
                        acc.replace_constraint(target_local, constraint);
                        self.encode.local_expr_env.insert(target_local, root_in);
                        acc.modified.insert(target_local);
                    } else {
                        // The intended transition is the identity, and with no
                        // new constraint the slot keeps its current value, so
                        // this exit loses nothing.
                        warn!(
                            target_local,
                            ref_local, "CHC: VecIntoIter identity mirror sort mismatch"
                        );
                    }
                } else {
                    warn!(
                        target_local,
                        ref_local,
                        "CHC: apply_projection_update failed for Mem-level Deref field mirror"
                    );
                    self.fail_close_ref_mirror(
                        target_local,
                        "deref_mirror_projection_update_failed",
                        acc,
                    );
                }
            }
        }
    }

    /// Mirror a deref store into a flattened (non-datatype) single-field slot.
    fn mirror_flattened_field_store(
        &mut self,
        field_proj: &FieldProjection,
        rhs_expr: &Expr,
        local_idx: usize,
        target_local: usize,
        target_vec_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        let field_idx = field_proj.field_idx;
        if self.flatten.flattened_tuple_locals.contains(&target_local) {
            let field_count = self.flattened_field_count(target_local);
            if field_idx >= field_count {
                // Part of #2912: VecIntoIter deep-flattening maps 5 fields
                // (Vec.ptr, Vec.len, Vec.cap, Vec.data, pos) but MIR's IntoIter
                // has additional fields (e.g. field 5 = `end: *const T`) with no
                // counterpart in the CHC model. The iteration bound is derived
                // from fld_len, so dropping `end` writes is sound.
                if self.collections.projection_locals.get(&target_local).copied()
                    == Some(CollectionProjectionKind::VecIntoIter)
                {
                    debug!(
                        target_local,
                        ref_local = local_idx,
                        field_idx,
                        field_count,
                        "CHC: VecIntoIter unmodeled MIR field — emitting identity transition"
                    );
                    // OI1 (#2876): Emit deterministic out==in constraints for all
                    // projected slots instead of silently dropping. This prevents
                    // the CHC relation from becoming underconstrained on the
                    // IntoIter internal-field write path.
                    let mut values = Vec::with_capacity(field_count);
                    for idx in 0..field_count {
                        values.push(self.flattened_local_field_expr(
                            target_local,
                            idx,
                            acc.modified,
                        ));
                    }
                    self.constrain_flattened_fields(target_local, &values, acc);
                } else {
                    warn!(
                        target_local,
                        ref_local = local_idx,
                        field_idx,
                        field_count,
                        "CHC: flattened field mirror index out of bounds"
                    );
                    self.fail_close_ref_mirror(
                        target_local,
                        "deref_mirror_flat_path_unresolved",
                        acc,
                    );
                }
                return;
            }

            // Preserve untouched flattened fields so updates through deref mirrors
            // do not unconstrain sibling fields (e.g., Range.end when writing Range.start).
            let mut values = Vec::with_capacity(field_count);
            for idx in 0..field_count {
                if idx == field_idx {
                    values.push(Some(rhs_expr.clone()));
                } else {
                    values.push(self.flattened_local_field_expr(target_local, idx, acc.modified));
                }
            }

            if !self.constrain_flattened_fields(target_local, &values, acc) {
                warn!(
                    target_local,
                    ref_local = local_idx,
                    field_idx,
                    "CHC: failed flattened field mirror constraint emission"
                );
                self.fail_close_ref_mirror(
                    target_local,
                    "deref_mirror_constraint_emission_failed",
                    acc,
                );
            }
            return;
        }

        // Fallback for a target with a single state variable. The old code
        // wrote `target_vec_idx + field_idx`, which for `field_idx > 0` is
        // ANOTHER local's slot, and coerced any sort into it. Follow-up (c):
        // write the whole variable only when the field is the whole value;
        // otherwise fail closed.
        let whole_value = self.state_var_mgr.output_state_vars.get(target_vec_idx).is_some_and(
            |(_, slot_sort)| {
                self.non_flattened_field_is_whole_value(
                    target_local,
                    field_proj,
                    slot_sort,
                    rhs_expr,
                )
            },
        );
        if !whole_value {
            warn!(
                target_local,
                ref_local = local_idx,
                field_idx,
                "CHC: Mem-level Deref field mirror into a single-variable target is not the whole value"
            );
            self.fail_close_ref_mirror(target_local, "deref_mirror_field_not_whole_value", acc);
            return;
        }
        // `whole_value` implies field 0, the variable's own sort and a stored
        // value of that sort, so this is a plain whole-variable write.
        let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(target_vec_idx).cloned()
        else {
            self.fail_close_ref_mirror(target_local, "deref_mirror_output_var_missing", acc);
            return;
        };
        let out_var = Expr::var(&*out_name, out_sort.clone());
        acc.replace_constraint(target_local, out_var.eq(rhs_expr.clone()));
        self.encode.local_expr_env.insert(target_local, rhs_expr.clone());
        self.encode.invalidate_local_cache(target_local);
        acc.modified.insert(target_local);
    }
}

/// See [`ChcCtx::ref_store_reinterpretation`].
pub(in crate::codegen_ay::chc) enum RefStoreReinterpretation {
    /// The reference writes its target's own type (or a cast the layout lane
    /// is not about): mirror the value as is.
    SameType,
    /// The stored value read back in the target's layout.
    Converted(Expr),
    /// A reinterpreting store the lane does not model: the target is fresh.
    Unmodeled(&'static str),
    /// A wider store inside the referent's containing local: that WHOLE
    /// local's new value.
    ConvertedLocal(Expr),
    /// A wider store past the end of the referent's containing local: a
    /// memory-safety violation on every path that reaches it.
    OutOfBounds,
}

/// Kani's message for an access outside its object.
pub(in crate::codegen_ay::chc) const OUT_OF_BOUNDS_MESSAGE: &str =
    "dereference failure: pointer outside object bounds";
