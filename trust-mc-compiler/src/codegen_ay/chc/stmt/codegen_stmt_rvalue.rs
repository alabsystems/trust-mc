// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rvalue translation for CHC statement encoding.
//!
//! Contains: translate_rvalue_with_modified and try_propagate_dst_metadata.
//! BinaryOp/CheckedBinaryOp extracted to `codegen_stmt_rvalue_binop.rs` per #3920.
//! Len extracted to `codegen_stmt_rvalue_len.rs` per #3920.
//! ShallowInitBox extracted to `codegen_stmt_rvalue_box.rs` per #3920.
//! Pointer offset extracted to `codegen_stmt_rvalue_offset.rs` per #3920.
//! Ref/AddressOf and Cast dispatch extracted to `codegen_stmt_rvalue_ref/` per #3199.

use crate::codegen_ay::chc::codegen_ctx::Havoc;
use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{
    AggregateKind, BorrowKind, CastKind, Operand, Place, PointerCoercion, ProjectionElem,
    RawPtrKind, Rvalue, UnOp,
};
#[cfg(not(trust_toolchain))]
use rustc_public::mir::{NullOp, RuntimeChecks};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::chc::call::canonical_zst_expr_for_sort;
use crate::codegen_ay::chc::call::codegen_call_kani_model_dst::is_zst_ty;
use crate::codegen_ay::chc::call::codegen_call_ptr_identity::trace_pointer_identity_ref_target;
use crate::codegen_ay::types::{ptr_sort, ty_to_bv_width};

use super::ChcCtx;
use super::codegen_ctx::globals::chc_fresh_name;
use super::codegen_expr_signedness::ExprSignedness;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translates a MIR rvalue using OUTPUT variables for modified locals.
    ///
    /// This method should be used when processing sequential statements within a block,
    /// where later statements may reference locals modified by earlier statements.
    /// For those locals, we must use the OUTPUT variable (which holds the new value)
    /// rather than the INPUT variable (which holds the pre-block value). (#657)
    ///
    /// At Mem track level, this also handles CopyForDeref using memory loads.
    /// Part of #892: Phase 3 - Memory load/store.
    pub(in crate::codegen_ay::chc) fn translate_rvalue_with_modified(
        &mut self,
        rvalue: &Rvalue,
        modified_locals: &HashSet<usize>,
        dest_local: Option<usize>,
    ) -> Option<Expr> {
        match rvalue {
            Rvalue::Use(operand, ..) => {
                // Part of #4163: Propagate subslice_len through Use(Copy/Move).
                if let Some(dest) = dest_local {
                    let src_local = match operand {
                        Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => {
                            Some(src.local)
                        }
                        _ => None,
                    };
                    if let Some(src) = src_local {
                        if self.path_insensitive_metadata_copy_is_unique(src, dest) {
                            if let Some(len) = self.ref_resolution.subslice_len.get(&src).cloned() {
                                self.ref_resolution.subslice_len.insert(dest, len);
                                debug!(src, dest, "subslice_len: propagated through Use");
                            }
                        } else {
                            self.clear_path_insensitive_ref_metadata(dest);
                        }
                    }
                }
                self.translate_operand_with_modified(operand, modified_locals)
            }
            Rvalue::BinaryOp(op, lhs_op, rhs_op) | Rvalue::CheckedBinaryOp(op, lhs_op, rhs_op) => {
                self.translate_rvalue_binop(rvalue, op, lhs_op, rhs_op, modified_locals, dest_local)
            }
            Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => {
                self.translate_ptr_metadata(operand, modified_locals).map(|meta| meta.into_expr())
            }
            Rvalue::UnaryOp(op, operand) => {
                // Part of #3043: derive BV width from operand's MIR type.
                // Part of #3243: bail instead of defaulting to 32 on type resolution failure.
                let int_bv_width = ty_to_bv_width(operand.ty(self.body.locals()).ok()?)?;
                // Part of #3055: derive signedness for bv2int conversion.
                // Part of #3247: Neg is only defined on signed types; default signed for Neg.
                let default_signed = matches!(op, UnOp::Neg);
                let is_signed = self.operand_signedness(operand).unwrap_or(default_signed);
                let expr = self.translate_operand_with_modified(operand, modified_locals)?;
                // Part of #3693: float negation is sign-bit flip, not two's complement.
                // bvneg gives wrong results on IEEE 754 bit patterns.
                if matches!(op, UnOp::Neg)
                    && matches!(
                        operand.ty(self.body.locals()).ok().map(|t| t.kind()),
                        Some(TyKind::RigidTy(RigidTy::Float(_)))
                    )
                {
                    crate::codegen_ay::float_arithmetic::bv_float_neg(expr, int_bv_width)
                } else {
                    self.translate_unop(*op, expr, int_bv_width, is_signed)
                }
            }
            // Part of #3044: dispatch on CastKind instead of wildcarding it.
            // Cast dispatch extracted to `codegen_stmt_rvalue_ref/` per #3199.
            Rvalue::Cast(kind, operand, target_ty) => {
                // A reference made by transmute from a pointer into a static
                // or a constant allocation must be dereferenceable, as `&*p`
                // must (`codegen_stmt_rvalue_offset_const_access.rs`).
                if matches!(kind, CastKind::Transmute)
                    && let Operand::Copy(src) | Operand::Move(src) = operand
                    && src.projection.is_empty()
                {
                    self.emit_const_object_transmuted_ref_check(
                        src.local,
                        *target_ty,
                        modified_locals,
                    );
                }
                // Part of #4163: Propagate subslice_len through all Cast variants.
                if let Some(dest) = dest_local {
                    let src_local = match operand {
                        Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => {
                            Some(src.local)
                        }
                        _ => None,
                    };
                    if let Some(src) = src_local {
                        if self.path_insensitive_metadata_copy_is_unique(src, dest) {
                            if let Some(len) = self.ref_resolution.subslice_len.get(&src).cloned() {
                                self.ref_resolution.subslice_len.insert(dest, len);
                            }
                        } else {
                            self.clear_path_insensitive_ref_metadata(dest);
                        }
                    }
                }
                // Fail-closed under `-Z uninit-checks`: a type-punning
                // `*mut` PtrToPtr cast (pointee sizes differ) lets subsequent
                // writes re-shape initialization/padding in ways the scalar
                // shadow-memory model does not track (delayed UB, e.g.
                // `&mut arr[..][0] as *mut u128 as *mut (u8, u32)` then
                // `*ptr = (4, 4)` leaves padding bytes uninit inside a u128).
                // Kani instruments this via points-to analysis (their
                // delayed-UB pass); until trust-mc has that (task #24),
                // record a demoting fallback so PROOF can never rest on the
                // untracked write. Scoped: uninit mode only, `*mut` only,
                // size-mismatched pointee reinterpretation only.
                // Both mutabilities: a size-mismatched `*const` reinterpretation
                // is a padding/uninit READ the shadow model equally cannot
                // track (access-padding-enum-diverging-variants: `addr_of!`
                // enum -> `*const u8`). Same-size re-typings (e.g.
                // delayed-ub-overapprox's u128 -> (u8,u32,u64), 16B -> 16B)
                // stay exempt — the byte-tracked shadow state remains aligned.
                if self.uninit_checks
                    && matches!(kind, CastKind::PtrToPtr)
                    && let TyKind::RigidTy(RigidTy::RawPtr(dst_pointee, _)) = target_ty.kind()
                    && let Some(src_pointee) = operand
                        .ty(self.body.locals())
                        .ok()
                        .and_then(ChcCtx::deref_pointee_ty)
                    && let (Some(src_size), Some(dst_size)) =
                        (self.get_type_size(src_pointee), self.get_type_size(dst_pointee))
                    // Zero-size ends are `*mut ()`-style pointer-ERASURE
                    // idioms (e.g. the `as *mut _` intermediate in a cast
                    // chain), not byte reinterpretations — the shadow state
                    // stays aligned. delayed-ub-overapprox regressed on this
                    // before the exclusion (its erasure hop resolved as `()`).
                    && src_size != 0
                    && dst_size != 0
                    && src_size != dst_size
                {
                    // P3-uninit: skip the demotion ONLY when every transitive
                    // use of the punned pointer is a shape whose value AND
                    // shadow-memory effects are encoded precise-or-fail-closed
                    // (copy-intrinsic operand, mem-init bookkeeping call, or
                    // pointer-identity flow into such uses). Any other use —
                    // punned deref write/read, escape into a call, pointer
                    // arithmetic — keeps the fail-closed demoting fallback
                    // (the delayed-UB gap, task #24).
                    if dest_local.is_some_and(|dest| self.punned_ptr_uses_are_tracked(dest)) {
                        debug!(
                            src_size,
                            dst_size,
                            "uninit-checks: type-punning PtrToPtr cast with fully \
                             tracked uses (copy/mem-init only) — no demotion"
                        );
                    } else {
                        debug!(
                            src_size,
                            dst_size,
                            "uninit-checks: type-punning *mut PtrToPtr cast — recording \
                             demoting chc_fallback (shadow memory cannot track the punned write)"
                        );
                        self.record_fallback();
                    }
                }
                // rustc's own null and alignment checks read a pointer's offset
                // bits only, the same in every mode Kani uses: not a far
                // pointer observation (heap/stack_address.rs).
                let check_cast = dest_local.is_some_and(|d| self.is_rustc_check_cast_dest(d));
                let suppressed = self.far_observation_suppressed.replace(check_cast);
                let result = self.translate_rvalue_cast(kind, operand, target_ty, modified_locals);
                self.far_observation_suppressed.set(suppressed);
                // Part of #3768 Layer 2: Also try DST metadata propagation.
                if matches!(
                    kind,
                    CastKind::PtrToPtr | CastKind::PointerCoercion(PointerCoercion::Unsize)
                ) {
                    if let Some(dest) = dest_local {
                        self.try_propagate_dst_metadata(operand, *target_ty, dest);
                    }
                }
                result
            }
            // Handle Ref/AddressOf rvalues (#667, #734, #824, #869, #891)
            //
            // Ref/AddressOf encoding depends on track level:
            // - Reg: value semantics for all simple locals (#2074 RC-1b)
            // - Ptr: stable symbolic addresses (Ordering → value for Discriminant)
            // - Mem: abstract heap model via translate_ref_to_address (#869)
            // With projections: BigInt/BigRational → value, deref chains → ref_target
            // resolution, others → auto-promote to Mem (#2084).
            // Split Ref vs AddressOf to access BorrowKind/Mutability (#2084, R748 Option B).
            // Shared borrows with non-deref projections use value semantics at Reg level;
            // mutable borrows still auto-promote to Mem so stores work.
            Rvalue::Ref(_, borrow_kind, place) => {
                // Part of #4163: Propagate subslice_len through Ref (including deref reborrows).
                if let Some(dest) = dest_local {
                    if self.path_insensitive_metadata_copy_is_unique(place.local, dest) {
                        if let Some(len) =
                            self.ref_resolution.subslice_len.get(&place.local).cloned()
                        {
                            self.ref_resolution.subslice_len.insert(dest, len);
                            debug!(src = place.local, dest, proj = ?place.projection,
                                "subslice_len: propagated through Ref");
                        }
                    } else {
                        self.clear_borrow_metadata_keeping_exact_edge(dest, place);
                    }
                }
                self.register_collection_elem_field_ref(dest_local, place);
                // A reference into dead storage is UB on creation, even when
                // the only read of it is unmodeled (format-args). AddressOf is
                // deliberately not checked: `&raw const (*p)` is not UB.
                self.emit_ref_into_dead_storage_check(place, modified_locals);
                self.fail_close_reborrow_of_path_merged_pointer(place);
                // `&*p` into a static or constant allocation: the object bound
                // (`codegen_stmt_rvalue_offset_const_object`).
                self.emit_const_object_reborrow_check(place, modified_locals);
                // `&*ptr` with `ptr: *const [T]` / `*const str`: the reference
                // is valid only for the pointer's whole metadata extent.
                self.emit_raw_slice_ref_extent_check(place, modified_locals);
                let is_shared = matches!(borrow_kind, BorrowKind::Shared | BorrowKind::Fake(_));
                // Design 4 C: a borrow of an unsized slice-like place carries
                // its length; the address lanes above produce a thin address.
                self.translate_ref_or_addressof(place, is_shared, modified_locals)
                    .map(|value| self.pack_unsized_borrow_len(place, value, modified_locals))
            }
            Rvalue::AddressOf(raw_ptr_kind, place) => {
                // Reg references contain their referent's value. A raw
                // address observes physical identity, so replay this host
                // body in the existing address-bearing memory model instead
                // of reusing those element bits as a pointer.
                let raw_identity = matches!(place.projection.as_slice(), [ProjectionElem::Deref])
                    && matches!(
                        self.resolve_body_ty(self.body.locals()[place.local].ty).kind(),
                        TyKind::RigidTy(RigidTy::RawPtr(..))
                    );
                // Bare &raw *raw_ptr is an identity even for a null,
                // dangling or misaligned pointer. It performs no load and
                // must not acquire reference-validity obligations on replay.
                if self.track_level < crate::args::ChcTrackLevel::Ptr && !raw_identity {
                    self.needs_mem_promote = true;
                    return None;
                }
                // Part of #4163: Propagate subslice_len through AddressOf.
                if let Some(dest) = dest_local {
                    if self.path_insensitive_metadata_copy_is_unique(place.local, dest) {
                        if let Some(len) =
                            self.ref_resolution.subslice_len.get(&place.local).cloned()
                        {
                            self.ref_resolution.subslice_len.insert(dest, len);
                        }
                    } else {
                        self.clear_borrow_metadata_keeping_exact_edge(dest, place);
                    }
                }
                self.register_collection_elem_field_ref(dest_local, place);
                if raw_identity {
                    return self.translate_place_with_modified(
                        &Place { local: place.local, projection: vec![] },
                        modified_locals,
                    );
                }
                let is_shared = matches!(raw_ptr_kind, RawPtrKind::Const);
                self.translate_ref_or_addressof(place, is_shared, modified_locals)
                    .map(|value| self.pack_unsized_borrow_len(place, value, modified_locals))
            }
            Rvalue::Len(place) => self.translate_rvalue_len(place, modified_locals),
            Rvalue::Aggregate(kind, operands) => {
                let result = self.translate_aggregate(kind, operands, modified_locals);
                // Part of #4163: Seed subslice_len from RawPtr aggregate metadata.
                // When slice_from_raw_parts{_mut} is inlined, MIR produces
                // Aggregate::RawPtr(data_ptr, len). The length operand is the
                // slice metadata that downstream PtrMetadata needs to resolve
                // size_of_val for custom DSTs.
                if let AggregateKind::RawPtr(_, _) = kind {
                    if let Some(dest) = dest_local {
                        if let Some(data_local) = operands.first().and_then(|operand| match operand
                        {
                            Operand::Copy(place) | Operand::Move(place)
                                if place.projection.is_empty() =>
                            {
                                Some(place.local)
                            }
                            _ => None,
                        }) {
                            if let Some(obj_id) = self
                                .known_alloc_ids
                                .get(&data_local)
                                .copied()
                                .or_else(|| self.trace_deref_store_alloc_id(data_local))
                            {
                                self.known_alloc_ids.insert(dest, obj_id);
                            }
                            if let Some(ref_target) = self
                                .ref_resolution
                                .ref_targets
                                .get(&data_local)
                                .cloned()
                                .or_else(|| trace_pointer_identity_ref_target(self, data_local))
                            {
                                self.ref_resolution.ref_targets.insert(dest, ref_target);
                                self.ref_resolution.call_forwarded_raw_ptrs.insert(dest);
                            }
                        }
                        if operands.len() > 1 {
                            if let Ok(meta_ty) = operands[1].ty(self.body.locals()) {
                                let is_usize = matches!(
                                    meta_ty.kind(),
                                    TyKind::RigidTy(RigidTy::Uint(rustc_public::ty::UintTy::Usize))
                                );
                                if is_usize {
                                    if let Some(len_expr) = self.translate_operand_with_modified(
                                        &operands[1],
                                        modified_locals,
                                    ) {
                                        self.ref_resolution.subslice_len.insert(dest, len_expr);
                                        debug!(
                                            dest,
                                            "RawPtr aggregate: seeded subslice_len from metadata operand"
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
                result
            }
            Rvalue::Discriminant(place) => self.translate_discriminant(place, modified_locals),
            #[cfg(not(trust_toolchain))]
            Rvalue::ShallowInitBox(operand, ty) => {
                self.translate_rvalue_shallow_init_box(operand, *ty, modified_locals)
            }
            Rvalue::CopyForDeref(place) => {
                // CopyForDeref(place) semantics = read *place.
                // Synthesize a Deref projection so deref resolution can resolve
                // through ref_targets (value semantics) or memory loads as appropriate.
                // Part of #3059: Deref must follow place projections, not precede them.
                // CopyForDeref(_5.1) = *(_5.1) not (*_5).1.
                let mut deref_projs = place.projection.clone();
                deref_projs.push(ProjectionElem::Deref);
                let deref_place = Place { local: place.local, projection: deref_projs };
                debug!(
                    ?place,
                    "CHC: CopyForDeref - synthesizing Deref projection for deref resolution"
                );
                self.translate_place_with_deref(&deref_place, modified_locals)
            }
            Rvalue::Repeat(operand, len_const) => {
                if let Some(dest) = dest_local {
                    let dest_ty = self.body.locals()[dest].ty;
                    if is_zst_ty(dest_ty)
                        && let Some(vec_idx) = self.try_state_idx_for_local(dest)
                        && let Some((_, dest_sort)) =
                            self.state_var_mgr.output_state_vars.get(vec_idx)
                        && let Some(canonical) = canonical_zst_expr_for_sort(dest_ty, dest_sort)
                    {
                        return Some(canonical);
                    }
                }

                // Array initialization: [value; count]
                // Use a const array with pointer-width indices; bounds are enforced by
                // separate array bounds checks, so we only validate `len_const` here.
                let mut elem_expr =
                    self.translate_operand_with_modified(operand, modified_locals)?;
                let Some(len) = len_const.eval_target_usize().ok() else {
                    // Part of #3447: Record that the Repeat rvalue failed to
                    // evaluate its length constant, leaving the array unconstrained.
                    self.record_fallback();
                    warn!(
                        "CHC: failed to evaluate Repeat length constant; falling back to unsupported rvalue"
                    );
                    return None;
                };
                // Part of #1739: Flatten DT array elements to BV for PDR compatibility.
                // translate_ty now produces Array(BV64, BV) for flattenable DT elements,
                // so the const_array default must also be BV.
                if elem_expr.sort().is_datatype() {
                    if let Some(width) =
                        crate::codegen_ay::types::flattenable_datatype_sort_width(elem_expr.sort())
                    {
                        if let Some(flattened) =
                            crate::codegen_ay::types::flatten_datatype_to_bitvec(&elem_expr, width)
                        {
                            // The flatten ITE references DT constructors/accessors,
                            // so declare the Datatype sort in the VC preamble.
                            self.declare_datatype_sort_if_needed(elem_expr.sort());
                            elem_expr = flattened;
                        }
                    }
                }
                debug!(
                    len,
                    elem_sort = ?elem_expr.sort(),
                    "CHC: translated Repeat to const array"
                );
                Some(Expr::const_array(ptr_sort(), elem_expr))
            }
            Rvalue::ThreadLocalRef(item) => {
                // Part of #4068: Under the single-thread assumption (matching Kani),
                // ThreadLocalRef is equivalent to a static pointer. Resolve the
                // CrateItem to the static's ONE object (`global_objects`), keyed
                // by its definition.
                let resolved = rustc_public::mir::mono::StaticDef::try_from(*item)
                    .ok()
                    .and_then(|def| {
                        self.object_base(
                            &crate::codegen_ay::shared::const_pointer::TargetKey::Static(def),
                        )
                    })
                    .map(|addr| addr.into_expr());
                if let Some(addr) = resolved {
                    debug!("CHC: ThreadLocalRef resolved to static address (single-thread model)");
                    Some(addr)
                } else {
                    // Fallback: static not yet materialized. Sound over-approximation.
                    warn!(
                        "CHC: ThreadLocalRef static address not found — sound over-approximation"
                    );
                    let booked = self.record_sound_fallback_reason("thread_local_ref_unresolved");
                    let name = chc_fresh_name("__thread_local_nondet");
                    Some(Havoc::booked(booked, name, ptr_sort()))
                }
            }
            #[cfg(not(trust_toolchain))]
            Rvalue::NullaryOp(null_op) => {
                // RuntimeChecks control conditional UB/overflow/contract checking at runtime.
                // In verification mode:
                // - UbChecks: false, as Kani (see `rustc_compat::runtime_checks_value`).
                // - ContractChecks: Return true (enable contract checking)
                // - OverflowChecks: Return false (verification handles overflow explicitly)
                // Part of #1840
                match null_op {
                    NullOp::RuntimeChecks(RuntimeChecks::UbChecks) => {
                        debug!("CHC translate_rvalue: UbChecks -> false (Kani parity)");
                        Some(Expr::bool_const(crate::rustc_compat::runtime_checks_value(
                            &RuntimeChecks::UbChecks,
                        )))
                    }
                    NullOp::RuntimeChecks(RuntimeChecks::ContractChecks) => {
                        debug!("CHC translate_rvalue: ContractChecks -> true");
                        Some(Expr::bool_const(true))
                    }
                    NullOp::RuntimeChecks(RuntimeChecks::OverflowChecks) => {
                        debug!("CHC translate_rvalue: OverflowChecks -> false");
                        Some(Expr::bool_const(false))
                    }
                }
            }
            // Trust: user-ADT reborrowing has no CHC encoding (see
            // `trust_reborrow`). Record the fail-close reason and return
            // `None`, so the caller takes its unsupported-rvalue path.
            #[cfg(trust_toolchain)]
            Rvalue::Reborrow(..) => {
                self.record_reborrow_unsupported("translate_rvalue_with_modified");
                None
            }
        }
    }

    /// Part of #3768 Layer 2: Propagate `subslice_len` through PtrToPtr casts
    /// targeting custom DST ADTs with unsized tails.
    ///
    /// When `*mut [u8]` is cast to `*mut MyStr` (where MyStr has a `str` tail),
    /// the fat pointer's length metadata must be preserved so that downstream
    /// `PtrMetadata` resolution finds a concrete length instead of falling to
    /// an unconstrained symbolic.
    fn try_propagate_dst_metadata(
        &mut self,
        operand: &Operand,
        target_ty: rustc_public::ty::Ty,
        dest_local: usize,
    ) {
        use crate::kani_middle::abi::LayoutOf;

        // Check if target is a raw pointer to an ADT with a slice tail.
        let pointee = match target_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
            | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            _ => return,
        };
        if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Adt(..))) {
            return;
        }
        let layout = LayoutOf::new(pointee);
        if !layout.has_slice_tail() {
            return;
        }

        // Extract source local and propagate its subslice_len.
        let src_local = match operand {
            Operand::Copy(place) | Operand::Move(place) => place.local,
            _ => return,
        };

        if !self.path_insensitive_metadata_copy_is_unique(src_local, dest_local) {
            self.clear_path_insensitive_ref_metadata(dest_local);
            return;
        }

        if let Some(len_expr) = self.ref_resolution.subslice_len.get(&src_local).cloned() {
            self.ref_resolution.subslice_len.insert(dest_local, len_expr);
            debug!(
                src_local,
                dest_local, "try_propagate_dst_metadata: propagated subslice_len for DST cast"
            );
        }
    }
}
