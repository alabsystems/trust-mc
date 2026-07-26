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

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::alloc::GlobalAlloc;
use rustc_public::mir::{
    AggregateKind, BorrowKind, CastKind, NullOp, Operand, Place, PointerCoercion, ProjectionElem,
    RawPtrKind, RuntimeChecks, Rvalue, UnOp,
};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::chc::call::canonical_zst_expr_for_sort;
use crate::codegen_ay::chc::call::codegen_call_kani_model_dst::is_zst_ty;
use crate::codegen_ay::chc::call::codegen_call_ptr_identity::trace_pointer_identity_ref_target;
use crate::codegen_ay::types::{ptr_sort, ty_to_bv_width};

use super::ChcCtx;
use super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
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
            Rvalue::Use(operand) => {
                // Part of #4163: Propagate subslice_len through Use(Copy/Move).
                if let Some(dest) = dest_local {
                    let src_local = match operand {
                        Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => {
                            Some(src.local)
                        }
                        _ => None,
                    };
                    if let Some(src) = src_local {
                        if let Some(len) = self.ref_resolution.subslice_len.get(&src).cloned() {
                            self.ref_resolution.subslice_len.insert(dest, len);
                            debug!(src, dest, "subslice_len: propagated through Use");
                        }
                    }
                }
                self.translate_operand_with_modified(operand, modified_locals)
            }
            Rvalue::BinaryOp(op, lhs_op, rhs_op) | Rvalue::CheckedBinaryOp(op, lhs_op, rhs_op) => {
                self.translate_rvalue_binop(rvalue, op, lhs_op, rhs_op, modified_locals, dest_local)
            }
            Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => {
                self.translate_ptr_metadata(operand, modified_locals)
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
                    let sign_mask = match int_bv_width {
                        32 => Expr::bitvec_const(0x8000_0000_i128, 32),
                        64 => Expr::bitvec_const(0x8000_0000_0000_0000_u64 as i128, 64),
                        _ => return self.translate_unop(*op, expr, int_bv_width, is_signed),
                    };
                    Some(expr.bvxor(sign_mask))
                } else {
                    self.translate_unop(*op, expr, int_bv_width, is_signed)
                }
            }
            // Part of #3044: dispatch on CastKind instead of wildcarding it.
            // Cast dispatch extracted to `codegen_stmt_rvalue_ref/` per #3199.
            Rvalue::Cast(kind, operand, target_ty) => {
                // Part of #4163: Propagate subslice_len through all Cast variants.
                if let Some(dest) = dest_local {
                    let src_local = match operand {
                        Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => {
                            Some(src.local)
                        }
                        _ => None,
                    };
                    if let Some(src) = src_local {
                        if let Some(len) = self.ref_resolution.subslice_len.get(&src).cloned() {
                            self.ref_resolution.subslice_len.insert(dest, len);
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
                let result = self.translate_rvalue_cast(kind, operand, target_ty, modified_locals);
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
                    if let Some(len) = self.ref_resolution.subslice_len.get(&place.local).cloned() {
                        self.ref_resolution.subslice_len.insert(dest, len);
                        debug!(src = place.local, dest, proj = ?place.projection,
                            "subslice_len: propagated through Ref");
                    }
                }
                let is_shared = matches!(borrow_kind, BorrowKind::Shared | BorrowKind::Fake(_));
                self.translate_ref_or_addressof(place, is_shared, modified_locals)
            }
            Rvalue::AddressOf(raw_ptr_kind, place) => {
                // Part of #4163: Propagate subslice_len through AddressOf.
                if let Some(dest) = dest_local {
                    if let Some(len) = self.ref_resolution.subslice_len.get(&place.local).cloned() {
                        self.ref_resolution.subslice_len.insert(dest, len);
                    }
                }
                let is_shared = matches!(raw_ptr_kind, RawPtrKind::Const);
                self.translate_ref_or_addressof(place, is_shared, modified_locals)
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
                // CrateItem's DefId to the static address already materialized by
                // codegen_decl_static.rs via static_address_exprs.
                let item_def_id = rustc_public::rustc_internal::internal(self.tcx, item.def_id());
                let resolved = self.ref_resolution.static_address_exprs.iter().find_map(
                    |(&alloc_id, addr_expr)| {
                        if let GlobalAlloc::Static(static_def) = GlobalAlloc::from(alloc_id) {
                            let static_def_id = rustc_public::rustc_internal::internal(
                                self.tcx,
                                static_def.def_id(),
                            );
                            if static_def_id == item_def_id {
                                return Some(addr_expr.clone());
                            }
                        }
                        None
                    },
                );
                if let Some(addr) = resolved {
                    debug!("CHC: ThreadLocalRef resolved to static address (single-thread model)");
                    Some(addr)
                } else {
                    // Fallback: static not yet materialized. Sound over-approximation.
                    warn!(
                        "CHC: ThreadLocalRef static address not found — sound over-approximation"
                    );
                    self.record_sound_fallback_reason("thread_local_ref_unresolved");
                    let name = chc_fresh_name("__thread_local_nondet");
                    Some(declare_pending_var(name, ptr_sort()))
                }
            }
            Rvalue::NullaryOp(null_op) => {
                // RuntimeChecks control conditional UB/overflow/contract checking at runtime.
                // In verification mode:
                // - UbChecks: Return true so MIR-generated UB assertions are reachable.
                //   Fixes #3299: returning false made Assert terminators for
                //   AddUnchecked/SubUnchecked/MulUnchecked dead, producing false PROOF.
                // - ContractChecks: Return true (enable contract checking)
                // - OverflowChecks: Return false (verification handles overflow explicitly)
                // Part of #1840
                match null_op {
                    NullOp::RuntimeChecks(RuntimeChecks::UbChecks) => {
                        debug!("CHC translate_rvalue: UbChecks -> true (#3299)");
                        Some(Expr::bool_const(true))
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

        if let Some(len_expr) = self.ref_resolution.subslice_len.get(&src_local).cloned() {
            self.ref_resolution.subslice_len.insert(dest_local, len_expr);
            debug!(
                src_local,
                dest_local, "try_propagate_dst_metadata: propagated subslice_len for DST cast"
            );
        }
    }
}
