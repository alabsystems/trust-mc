// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Simple stub dispatch — constant, identity, no-op, and diverging stubs.
//!
//! These stubs share common patterns (assign a constant, pass-through an
//! argument, no-op, or diverge) and don't require complex codegen logic.
//! Extracted from `stub_dispatch.rs` per #2246 to keep the main dispatch
//! table concise. Table-driven dispatch per #2268.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Stubs that decode first arg, coerce to pointer width, and assign.
/// Note: WithoutProvenance/WithoutProvenanceMut are handled separately (#3361)
/// because they also need obj_valid invalidation.
const PTR_IDENTITY_STUBS: &[StubKind] =
    &[StubKind::PtrCastConst, StubKind::PtrCast, StubKind::NonNullAsPtr, StubKind::PtrAddr];

/// Stubs that assign a constant boolean value to the destination.
const CONST_BOOL_STUBS: &[(StubKind, bool)] = &[
    // Part of #4249: KaniMemIsPtrAligned remains true — alignment checks need
    // type layout info (get_type_align) not available in the BMC context.
    (StubKind::KaniMemIsPtrAligned, true),
    (StubKind::KaniMemAssertIsInitialized, true),
    (StubKind::SetValZstDefault, true),
    // Part of #3470: RangeBounds::contains — over-approximate as true.
    (StubKind::RangeBoundsContains, true),
];

/// Part of #4249: kani::mem predicates that use the heap model for precise
/// validity/bounds checking instead of vacuously returning `true`.
/// These predicates translate the pointer argument and query the BMC heap
/// model (`obj_valid[ptr_obj]`, bounds checks via same-allocation).
const KANI_MEM_HEAP_STUBS: &[StubKind] = &[
    StubKind::KaniMemCanDereference,
    StubKind::KaniMemCanWrite,
    StubKind::KaniMemCanReadUnaligned,
    StubKind::KaniMemIsInbounds,
    StubKind::KaniMemSameAllocation,
];

/// Stubs that are no-ops (no assignment, just continue to target).
const NOOP_STUBS: &[StubKind] = &[StubKind::RustNoAllocShimIsUnstable];

/// UB/precondition check stubs — all pass, some assign true.
const UB_CHECK_STUBS: &[StubKind] = &[
    StubKind::UbCheckLanguageUb,
    StubKind::UbCheckMaybeIsAligned,
    StubKind::UbCheckMaybeIsNonoverlapping,
    StubKind::PreconditionCheck,
];

/// UB check stubs that additionally assign `true` to destination.
const UB_CHECK_ASSIGN_TRUE: &[StubKind] =
    &[StubKind::UbCheckMaybeIsAligned, StubKind::UbCheckMaybeIsNonoverlapping];

/// Fmt helper stubs that diverge (no successor block).
const FMT_DIVERGING_STUBS: &[StubKind] =
    &[StubKind::FmtArgumentNewDisplay, StubKind::FmtArgumentsNew, StubKind::FmtArgumentsFromStr];

/// Check membership in a StubKind table.
fn stub_in(table: &[StubKind], stub: StubKind) -> bool {
    table.contains(&stub)
}

/// Lookup a constant bool value for a StubKind.
fn lookup_const_bool(table: &[(StubKind, bool)], stub: StubKind) -> Option<bool> {
    table.iter().find(|(s, _)| *s == stub).map(|(_, v)| *v)
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Dispatch simple stubs that assign constants, pass through arguments,
    /// no-op, or diverge.
    ///
    /// Returns `Some(result)` if the stub was handled, `None` if not matched.
    /// Table-driven dispatch per #2268.
    pub(in crate::codegen_ay::statement) fn try_codegen_simple_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        callee_path: &str,
    ) -> Option<Option<BasicBlockIdx>> {
        // #3361: WithoutProvenance/WithoutProvenanceMut create pointers from integers
        // without allocation provenance. Same as ptr identity but also invalidate
        // obj_valid so dereference checks catch use of never-allocated addresses.
        if matches!(stub_kind, StubKind::WithoutProvenance | StubKind::WithoutProvenanceMut) {
            debug!(
                ?stub_kind,
                "codegen_stubbed_call: WithoutProvenance with obj_valid invalidation"
            );
            if let Some(arg_expr) = args.first().and_then(|a| self.codegen_operand(a)) {
                let ptr = self.coerce_to_ptr_width(arg_expr);
                self.ctx.heap_invalidate_no_provenance(ptr.clone());
                self.assign_value_to_place(destination, ptr);
            }
            return Some(target);
        }

        // Table-driven: pointer identity stubs.
        if stub_in(PTR_IDENTITY_STUBS, stub_kind) {
            debug!(?stub_kind, "codegen_stubbed_call: pointer identity stub");
            return Some(self.codegen_ptr_identity(args, destination, target));
        }

        if matches!(stub_kind, StubKind::PtrIsNull | StubKind::PtrIsNullRuntime) {
            debug!(?stub_kind, "codegen_stubbed_call: ptr::is_null comparison stub");
            return Some(self.codegen_ptr_is_null(args, destination, target));
        }

        // Part of #4249: kani::mem predicates with heap-model precision.
        // Uses obj_valid[ptr_obj] and same-allocation checks instead of
        // vacuously returning true.
        if stub_in(KANI_MEM_HEAP_STUBS, stub_kind) {
            debug!(?stub_kind, "codegen_stubbed_call: kani_mem heap-model predicate");
            return Some(self.codegen_kani_mem_heap_predicate(
                stub_kind,
                args,
                destination,
                target,
            ));
        }

        // Table-driven: constant boolean stubs.
        if let Some(value) = lookup_const_bool(CONST_BOOL_STUBS, stub_kind) {
            debug!(?stub_kind, value, "codegen_stubbed_call: constant bool stub");
            self.assign_value_to_place(destination, Expr::bool_const(value));
            return Some(target);
        }

        // Table-driven: no-op stubs.
        if stub_in(NOOP_STUBS, stub_kind) {
            debug!(?stub_kind, "codegen_stubbed_call: no-op stub");
            return Some(target);
        }

        // Table-driven: UB/precondition check stubs.
        if stub_in(UB_CHECK_STUBS, stub_kind) {
            debug!("codegen_stubbed_call: UB/precondition check stubbed as passing");
            if stub_in(UB_CHECK_ASSIGN_TRUE, stub_kind) {
                self.assign_value_to_place(destination, Expr::bool_const(true));
            }
            return Some(target);
        }

        // Table-driven: fmt diverging stubs.
        if stub_in(FMT_DIVERGING_STUBS, stub_kind) {
            debug!("codegen_stubbed_call: fmt helper stubbed as diverging");
            return Some(None);
        }

        // Table-driven: BigRational unsupported stubs.
        if stub_kind.is_big_rational() {
            warn!(
                ?stub_kind,
                %callee_path, "BigRational not supported in BMC path; use CHC mode (--ay-chc)"
            );
            self.ctx.unsupported_with_fallback(
                "BigRational in BMC",
                format!("{stub_kind:?} ({callee_path})"),
            );
            return Some(target);
        }

        match stub_kind {
            // --- Value identity: decode arg, assign as-is ---
            StubKind::NonZeroGet | StubKind::MaybeUninitAsPtr | StubKind::CharFromU32Unchecked => {
                debug!(?stub_kind, "codegen_stubbed_call: identity passthrough");
                if let Some(arg_expr) = args.first().and_then(|a| self.codegen_operand(a)) {
                    self.assign_value_to_place(destination, arg_expr);
                }
                Some(target)
            }

            // --- Null pointer: return zero bitvector ---
            // Part of #3477: PtrNull creates a null pointer. BMC parity with CHC
            // encoding which returns bitvec_const(0, POINTER_WIDTH).
            StubKind::PtrNull => {
                debug!("codegen_stubbed_call: ptr::null stubbed as zero bitvector");
                self.assign_value_to_place(destination, Expr::bitvec_const(0u64, POINTER_WIDTH));
                Some(target)
            }

            // --- Alignment constant ---
            StubKind::AlignmentAsUsize => {
                let align = Expr::bitvec_const(8, POINTER_WIDTH);
                self.assign_value_to_place(destination, align);
                debug!("codegen_stubbed_call: Alignment::as_usize -> 8");
                Some(target)
            }

            // MemSizeOf / MemAlignOf: moved to try_codegen_alloc_layout_stub
            // which has access to `func` to extract the generic type arg T.
            // Part of #3141.

            // --- FromResidual::from_residual ---
            StubKind::FromResidualFromResidual => {
                // Part of #4112 follow-up: for `Option<T>` destinations the
                // residual is `Option::<Infallible>::None`, so `from_residual`
                // returns exactly `None`. Encode the flattened None (`.0` = 0,
                // base = 0) — iterator `?` desugaring reaches this on every
                // loop exit, and leaving the destination unconstrained let the
                // solver fabricate a Some here. Non-Option destinations keep
                // the legacy no-op + warning (allocation failure modeling).
                if self.try_codegen_from_residual_option_none(destination) {
                    debug!(
                        "codegen_stubbed_call: from_residual -> flattened Option None (Part of #4112 follow-up)"
                    );
                } else {
                    warn!(
                        "codegen_stubbed_call: FromResidual::from_residual called - allocation failure path taken!"
                    );
                }
                Some(target)
            }

            // --- Diverging: panic records violation ---
            StubKind::PanicUnreachable | StubKind::PanicError => {
                debug!("codegen_stubbed_call: panic function - recording violation and diverging");
                self.record_violation_guarded(Expr::bool_const(true), "panic");
                Some(None)
            }
            StubKind::HandleAllocError => {
                debug!("codegen_stubbed_call: handle_alloc_error stubbed as diverging");
                Some(None)
            }

            // Table-driven stubs handled above; explicit unreachable for compile-time coverage.
            // WithoutProvenance/WithoutProvenanceMut handled above with invalidation (#3361).
            StubKind::PtrCastConst
            | StubKind::PtrCast
            | StubKind::NonNullAsPtr
            | StubKind::WithoutProvenance
            | StubKind::WithoutProvenanceMut
            | StubKind::PtrAddr
            | StubKind::PtrIsNull
            | StubKind::PtrIsNullRuntime
            | StubKind::KaniMemIsPtrAligned
            | StubKind::KaniMemIsInbounds
            | StubKind::SetValZstDefault
            | StubKind::RustNoAllocShimIsUnstable
            | StubKind::KaniMemAssertIsInitialized
            | StubKind::KaniMemCanReadUnaligned
            | StubKind::KaniMemCanDereference
            | StubKind::KaniMemCanWrite
            | StubKind::KaniMemSameAllocation
            | StubKind::UbCheckLanguageUb
            | StubKind::UbCheckMaybeIsAligned
            | StubKind::UbCheckMaybeIsNonoverlapping
            | StubKind::PreconditionCheck
            | StubKind::FmtArgumentNewDisplay
            | StubKind::FmtArgumentsNew
            | StubKind::FmtArgumentsFromStr => {
                unreachable!("handled by table-driven dispatch above")
            }

            // ~120 non-simple StubKind variants are handled by the main
            // dispatcher in stub_dispatch.rs; return None to signal "not mine".
            _other => None, // partial dispatch: StubKind
        }
    }

    /// Common pattern: decode first arg, coerce to pointer width, assign.
    fn codegen_ptr_identity(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if let Some(arg_expr) = args.first().and_then(|a| self.codegen_operand(a)) {
            let ptr = self.coerce_to_ptr_width(arg_expr);
            self.assign_value_to_place(destination, ptr);
        }
        target
    }

    /// Part of #4249: Encode kani::mem predicates using the BMC heap model.
    ///
    /// Instead of vacuously returning `true`, these predicates query the heap
    /// model for actual pointer validity:
    /// - `can_dereference(ptr)` / `can_write(ptr)` / `can_read_unaligned(ptr)`:
    ///   `heap_is_allocated(ptr, None)` -- checks `obj_valid[ptr_obj]`
    /// - `is_inbounds(ptr)`: same as above (bounds checking on the allocation)
    /// - `same_allocation(p1, p2)`:
    ///   `heap_pointer_object(p1) == heap_pointer_object(p2) && obj_valid[ptr_obj1]`
    ///
    /// Falls back to `true` (sound over-approximation) when pointer argument
    /// translation fails.
    fn codegen_kani_mem_heap_predicate(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if matches!(stub_kind, StubKind::KaniMemSameAllocation) {
            // same_allocation(p1, p2): both must be in the same allocation
            let ptr1 = args.first().and_then(|a| self.codegen_operand(a));
            let ptr2 = args.get(1).and_then(|a| self.codegen_operand(a));
            let result = match (ptr1, ptr2) {
                (Some(p1), Some(p2)) => {
                    let p1 = self.coerce_to_ptr_width(p1);
                    let p2 = self.coerce_to_ptr_width(p2);
                    let obj1 = self.ctx.heap_pointer_object(p1.clone());
                    let obj2 = self.ctx.heap_pointer_object(p2);
                    let same_obj = obj1.eq(obj2);
                    // Also require the first pointer is in a valid allocation
                    let is_valid = self.ctx.heap_is_allocated(p1, None);
                    same_obj.and(is_valid)
                }
                _ => {
                    debug!(
                        "kani_mem same_allocation: ptr translation failed, falling back to true"
                    );
                    Expr::bool_const(true)
                }
            };
            self.assign_value_to_place(destination, result);
            return target;
        }

        // Single-pointer predicates: can_dereference, can_write, can_read_unaligned, is_inbounds
        //
        // A pointer whose pointee is a DEAD local is the case the heap query
        // below cannot see: `obj_valid` is written only by heap_alloc, so a
        // stack pointee has no entry and the predicate silently evaluated over
        // unallocated memory — `can_dereference(new_dead_ptr())` proved
        // SUCCESSFUL, a false proof. Kani fails these harnesses with its own
        // unsupported check rather than answering, and so do we, reusing the
        // same evidence the deref path's dead_object check reads
        // (ref_pointees -> resolve_ref_chain_target -> dead_locals). Same
        // path-condition gate too: dead_locals is accumulated globally, and in
        // bb0 StorageDead of reference temporaries would false-positive.
        // ZST pointees are exempt: `can_dereference` on a zero-sized type is
        // TRUE by Kani's (and Rust's) semantics even for a dangling pointer —
        // a ZST access reads nothing. thin_ptr_validity::check_invalid_zst
        // pins exactly this: a DEAD pointer cast to *const [char; 0] must
        // still verify.
        let pointee_is_zst = args
            .first()
            .and_then(|a| a.ty(self.body.locals()).ok())
            .and_then(|ty| match ty.kind() {
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::RawPtr(pointee, _))
                | rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(_, pointee, _)) => {
                    crate::kani_middle::abi::LayoutOf::new(pointee).size_of()
                }
                _ => None,
            })
            == Some(0);
        if let (false, Some(Operand::Copy(place) | Operand::Move(place))) =
            (pointee_is_zst, args.first())
        {
            let ptr_base = self.ssa_base_name(place);
            if let Some(pointee_base) = self.ref_pointees.get(ptr_base.as_str()).cloned() {
                let target_local_idx =
                    Self::resolve_ref_chain_target(&self.ref_pointees, &pointee_base);
                // No path-condition gate here, unlike the deref path's
                // dead_object check: an explicit predicate call in a
                // straight-line harness has pc=None, and requiring one made
                // this detection unreachable everywhere. The ref-temporary
                // hazard that gate guards against is answered by the resolve
                // chain ending at the UNDERLYING local, which stays live in
                // every valid harness — the valid_access controls in the same
                // corpus files pin exactly that.
                if self.dead_locals.contains(&target_local_idx) {
                    self.record_violation_guarded_with_message(
                        Expr::bool_const(true),
                        "mem_predicate_unallocated",
                        Some(
                            "Kani does not support reasoning about pointer to unallocated memory"
                                .to_string(),
                        ),
                    );
                }
            }
        }
        let result = match args.first().and_then(|a| self.codegen_operand(a)) {
            Some(ptr_expr) => {
                let ptr = self.coerce_to_ptr_width(ptr_expr);
                // NULL is never allocated. `heap_is_allocated` alone cannot
                // say so — obj_valid[object(0)] is just another array cell the
                // solver may set true — and `!is_inbounds(null())` was
                // unprovable because of it.
                let nonnull = ptr.clone().eq(Expr::bitvec_const(0u128, POINTER_WIDTH)).not();
                if pointee_is_zst {
                    // A ZST access reads nothing: non-null is the ONLY
                    // requirement, and a dangling `NonNull::<ZST>::dangling()`
                    // is dereferenceable by Kani's semantics. Asking the heap
                    // model left exactly that case undecided.
                    nonnull
                } else {
                    nonnull.and(self.ctx.heap_is_allocated(ptr, None))
                }
            }
            None => {
                debug!("kani_mem predicate: ptr translation failed, falling back to true");
                Expr::bool_const(true)
            }
        };
        self.assign_value_to_place(destination, result);
        target
    }

    /// Lower `ptr.is_null()` and `ptr.is_null::runtime()` to `ptr == 0`.
    fn codegen_ptr_is_null(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let ptr = match args.first().and_then(|arg| self.codegen_operand(arg)) {
            Some(ptr) => self.coerce_to_ptr_width(ptr),
            None => {
                warn!("codegen_ptr_is_null: missing/untranslatable self arg; using symbolic ptr");
                self.ctx.unsupported_with_fallback(
                    "ptr_is_null_missing_arg",
                    "missing or untranslatable self arg",
                );
                let name = self.ctx.fresh_name("ptr_is_null_ptr");
                self.ctx.declare_var(&name, Sort::bitvec(POINTER_WIDTH))
            }
        };

        self.assign_value_to_place(destination, ptr.eq(Expr::bitvec_const(0u64, POINTER_WIDTH)));
        target
    }
}
