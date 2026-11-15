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

use crate::codegen_ay::shared::mono_ty;
use crate::rustc_compat::ValueAbi;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::abi::Scalar;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::target::MachineInfo;
use rustc_public::ty::{AdtKind, GenericArgKind, RigidTy, Ty, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{POINTER_WIDTH, bool_sort};
use crate::kani_middle::abi::LayoutOf;

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

/// Fmt helper stubs: they RETURN an `Arguments` value (no successor is cut).
///
/// These used to be modelled as diverging, which removed the edge into the
/// block that calls `panic_fmt` / `panic_nounwind_fmt` with the message. A
/// block with no incoming edge starts with NO path condition, which this lane
/// reads as `true`, so the panic in that block became UNCONDITIONAL: a
/// `NonZero::new_unchecked` precondition message on a value that is never
/// zero was reported as a certified failure (kani/Enum/discriminant_128bits.rs
/// `check_option_128bits`, "panic reached"). Returning keeps the edge, and the
/// panic is guarded by the condition that actually reaches it. The value is
/// only ever handed to a panic entry point, which reads nothing from it.
const FMT_RETURNING_STUBS: &[StubKind] =
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
                let resolved = self.box_pointer_value(&ptr).unwrap_or_else(|| ptr.clone());
                self.ctx.heap_invalidate_no_provenance(resolved);
                self.assign_value_to_place(destination, ptr);
            }
            return Some(target);
        }

        // Table-driven: pointer identity stubs.
        if stub_in(PTR_IDENTITY_STUBS, stub_kind) {
            debug!(?stub_kind, "codegen_stubbed_call: pointer identity stub");
            if stub_kind == StubKind::PtrAddr {
                let operand = args.first()?;
                let value = self.codegen_operand(operand)?;
                let value = self.coerce_to_ptr_width(value);
                let target_ty = destination.ty(self.body.locals()).ok()?;
                let previous = self.bmc_box_pointer_check_alignment.take();
                let result = self.box_cast_transport(operand, target_ty, value);
                self.bmc_box_pointer_check_alignment = previous;
                if let Some(value) = result {
                    self.assign_value_to_place(destination, value);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                return Some(target);
            }
            return self.codegen_ptr_identity(args, destination, target).map(Some);
        }

        if matches!(stub_kind, StubKind::PtrIsNull | StubKind::PtrIsNullRuntime) {
            debug!(?stub_kind, "codegen_stubbed_call: ptr::is_null comparison stub");
            return self.codegen_ptr_is_null(args, destination, target).map(Some);
        }

        // Part of #4249: kani::mem predicates with heap-model precision.
        // Uses obj_valid[ptr_obj] and same-allocation checks instead of
        // vacuously returning true.
        if stub_in(KANI_MEM_HEAP_STUBS, stub_kind) {
            debug!(?stub_kind, "codegen_stubbed_call: kani_mem heap-model predicate");
            return self
                .codegen_kani_mem_heap_predicate(stub_kind, args, destination, target)
                .map(Some);
        }

        // `RangeBounds::contains` used to be the constant `true`, which is not an
        // over-approximation: it proved every `(lo..hi).contains(x)` assertion,
        // e.g. `(4u8..8).contains(&1)` (tools/soundness-duals/negative/
        // review_r05_slice_range_contains.rs). The result is left unconstrained
        // and the harness is marked.
        if stub_kind == StubKind::RangeBoundsContains {
            debug!(%callee_path, "codegen_stubbed_call: RangeBounds::contains unconstrained");
            let name = format!("{}_range_contains_nondet", self.ssa_name(destination, true));
            let fresh = self.ctx.declare_var(&name, Sort::bool());
            self.assign_value_to_place(destination, fresh);
            self.ctx.unsupported_with_fallback("RangeBounds::contains", callee_path.to_string());
            return Some(target);
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

        // Table-driven: fmt helpers (return; see FMT_RETURNING_STUBS).
        if stub_in(FMT_RETURNING_STUBS, stub_kind) {
            debug!("codegen_stubbed_call: fmt helper returns an unread Arguments value");
            return Some(target);
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
    /// - `can_dereference` / `can_read_unaligned` additionally require the pointee
    ///   bytes to form a VALID value (`kani_mem_value_validity`).
    ///
    /// When pointer argument translation fails the result is a fresh Bool and the
    /// construct is recorded via `unsupported_with_fallback`. A constant `true`
    /// is not an over-approximation: the predicate is used under both polarities
    /// (`assert!(!can_dereference(p))` proved on it).
    fn codegen_kani_mem_heap_predicate(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if matches!(stub_kind, StubKind::KaniMemSameAllocation) {
            for argument in args.iter().take(2) {
                if let Operand::Copy(place) | Operand::Move(place) = argument {
                    let base = self.ssa_base_name(place);
                    if let Some(pointee) = self.ref_pointees.get(base.as_str()).cloned() {
                        let lifetime =
                            match Self::resolve_stack_storage_owner(&self.ref_pointees, &pointee) {
                                Ok(Some(owner)) => self.stack_owner_is_live(&owner),
                                Ok(None) => continue,
                                Err(_) => None,
                            };
                        match lifetime {
                            Some(true) => {}
                            Some(false) => {
                                self.assign_value_to_place(destination, Expr::bool_const(false));
                                return target;
                            }
                            None => {
                                let unknown = self.kani_mem_unknown_stack_lifetime(&pointee);
                                self.assign_value_to_place(destination, unknown);
                                return target;
                            }
                        }
                    }
                }
            }
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
                    debug!("kani_mem same_allocation: ptr translation failed, failing closed");
                    self.kani_mem_untranslatable_ptr(stub_kind)
                }
            };
            self.assign_value_to_place(destination, result);
            return target;
        }

        // Single-pointer predicates: can_dereference, can_write, can_read_unaligned, is_inbounds
        //
        // Stack storage lifetime is separate from heap metadata. An expired
        // nonzero pointee is inaccessible; a mixed-lifetime join has no single
        // boolean answer in this representation and must refuse certification.
        // ZST pointees are exempt: `can_dereference` on a zero-sized type is
        // TRUE by Kani's (and Rust's) semantics even for a dangling pointer —
        // a ZST access reads nothing. thin_ptr_validity::check_invalid_zst
        // pins exactly this: a DEAD pointer cast to *const [char; 0] must
        // still verify.
        let pointee_is_zst =
            args.first().and_then(|a| a.ty(self.body.locals()).ok()).and_then(|ty| {
                match ty.kind() {
                    rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::RawPtr(
                        pointee,
                        _,
                    ))
                    | rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(
                        _,
                        pointee,
                        _,
                    )) => crate::kani_middle::abi::LayoutOf::new(pointee).size_of(),
                    _ => None,
                }
            }) == Some(0);
        if let (false, Some(Operand::Copy(place) | Operand::Move(place))) =
            (pointee_is_zst, args.first())
        {
            let ptr_base = self.ssa_base_name(place);
            if let Some(pointee_base) = self.ref_pointees.get(ptr_base.as_str()).cloned() {
                let lifetime =
                    match Self::resolve_stack_storage_owner(&self.ref_pointees, &pointee_base) {
                        Ok(Some(owner)) => Some(self.stack_owner_is_live(&owner)),
                        Ok(None) => None,
                        Err(_) => Some(None),
                    };
                match lifetime {
                    Some(Some(true)) | None => {}
                    Some(Some(false)) => {
                        self.assign_value_to_place(destination, Expr::bool_const(false));
                        return target;
                    }
                    Some(None) => {
                        let unknown = self.kani_mem_unknown_stack_lifetime(&pointee_base);
                        self.assign_value_to_place(destination, unknown);
                        return target;
                    }
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
                    let access = nonnull.and(self.ctx.heap_is_allocated(ptr, None));
                    // Kani: `can_dereference` and `can_read_unaligned` end in
                    // `has_valid_value(ptr)`; `can_write` and `is_inbounds` do not.
                    if matches!(
                        stub_kind,
                        StubKind::KaniMemCanDereference | StubKind::KaniMemCanReadUnaligned
                    ) {
                        self.kani_mem_value_validity(args, access)
                    } else {
                        access
                    }
                }
            }
            None => {
                debug!("kani_mem predicate: ptr translation failed, failing closed");
                self.kani_mem_untranslatable_ptr(stub_kind)
            }
        };
        self.assign_value_to_place(destination, result);
        target
    }

    fn kani_mem_unknown_stack_lifetime(&mut self, owner: &str) -> Expr {
        self.ctx.unsupported_with_fallback("kani_mem_stack_lifetime_unknown", owner.to_owned());
        let name = self.ctx.fresh_name("kani_mem_stack_lifetime_unknown");
        self.ctx.declare_var(&name, bool_sort())
    }

    /// Fail-closed answer for a `kani::mem` predicate whose pointer argument did
    /// not translate: a fresh unconstrained Bool, recorded as fallback data so
    /// any proof resting on it is demoted.
    fn kani_mem_untranslatable_ptr(&mut self, stub_kind: StubKind) -> Expr {
        self.ctx.unsupported_with_fallback(
            "kani_mem_predicate_untranslatable_ptr",
            format!("{stub_kind:?}"),
        );
        let name = self.ctx.fresh_name("kani_mem_untranslatable_ptr");
        self.ctx.declare_var(&name, bool_sort())
    }

    /// Conjoin the pointee VALUE-validity requirement of `kani::mem::can_dereference`
    /// and `can_read_unaligned` onto the access predicate `access`.
    ///
    /// Kani defines both as `... && has_valid_value(ptr)`: bytes that are allocated
    /// but form an invalid `T` are NOT dereferenceable as `T`. The allocation-only
    /// query answered `true` for a `char` of `0x110000` and for a zero `NonZeroU32`,
    /// so `assert!(can_dereference(p))` over them PROVED (soundness duals
    /// `dual_candref_invalid_char`, `dual_candref_nonzero_zero`).
    ///
    /// Exact when every bit pattern of the pointee type is valid, or when the
    /// pointee is `char` / `bool` / `NonZero<int>` and its bytes are the register
    /// of a tracked primitive local of the same size. Every other case fails
    /// closed: the validity bit is a fresh Bool — the true answer is `false` or
    /// `access`, so `access && fresh` covers both polarities — and the construct is
    /// recorded via `unsupported_with_fallback`, which demotes any proof using it.
    fn kani_mem_value_validity(&mut self, args: &[Operand], access: Expr) -> Expr {
        let Some(arg) = args.first() else {
            return self.kani_mem_validity_fail_closed(access, "missing pointer argument");
        };
        let Some(pointee_ty) = arg.ty(self.body.locals()).ok().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _) | RigidTy::Ref(_, pointee, _)) => {
                Some(pointee)
            }
            _ => None,
        }) else {
            return self.kani_mem_validity_fail_closed(access, "pointee type unavailable");
        };
        if Self::kani_mem_ty_validity_free(pointee_ty, 0) {
            return access;
        }
        let Some(value) = self.kani_mem_pointee_register_value(arg, pointee_ty) else {
            return self.kani_mem_validity_fail_closed(
                access,
                format!("no exact value lane for pointee `{pointee_ty}`"),
            );
        };
        match Self::kani_mem_scalar_validity(pointee_ty, value) {
            Some(valid) => access.and(valid),
            None => self.kani_mem_validity_fail_closed(
                access,
                format!("unsupported validity invariant of `{pointee_ty}`"),
            ),
        }
    }

    fn kani_mem_validity_fail_closed(&mut self, access: Expr, reason: impl Into<String>) -> Expr {
        let reason = reason.into();
        debug!(%reason, "kani_mem value validity: failing closed");
        self.ctx.unsupported_with_fallback("kani_mem_value_validity", reason);
        let name = self.ctx.fresh_name("kani_mem_valid_value");
        let valid = self.ctx.declare_var(&name, bool_sort());
        access.and(valid)
    }

    /// True only when EVERY bit pattern of `ty` is a valid `ty`, so value validity
    /// adds nothing to `can_dereference`. Conservative: a layout-level scalar
    /// range that is not full (`bool`, `char`, `NonNull`, `NonZero`, references,
    /// niche-carrying newtypes) answers `false`, and so does every kind not
    /// listed (enums, references, fn pointers, `dyn` metadata, closures).
    fn kani_mem_ty_validity_free(ty: Ty, depth: usize) -> bool {
        const MAX_DEPTH: usize = 16;
        if depth > MAX_DEPTH {
            return false;
        }
        let Ok(layout) = ty.layout() else {
            return false;
        };
        let shape = layout.shape();
        let machine = MachineInfo::target();
        let scalar_full = |scalar: &Scalar| match scalar {
            Scalar::Initialized { value, valid_range } => {
                valid_range.is_full(value.size(&machine)).unwrap_or(false)
            }
            Scalar::Union { .. } => true,
        };
        let layout_ranges_full = match &layout_value_abi!(shape) {
            ValueAbi::Scalar(scalar) => scalar_full(scalar),
            scalar_pair_abi!(first, second) => scalar_full(first) && scalar_full(second),
            ValueAbi::Vector { .. } | ValueAbi::Aggregate { .. } => true,
            #[cfg(trust_toolchain)]
            ValueAbi::ScalableVector { .. } => false,
        };
        if !layout_ranges_full {
            return false;
        }
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)) => true,
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => {
                let pointee = LayoutOf::new(pointee);
                pointee.is_sized() || pointee.has_slice_tail()
            }
            TyKind::RigidTy(RigidTy::Tuple(elems)) => {
                elems.iter().all(|elem| Self::kani_mem_ty_validity_free(*elem, depth + 1))
            }
            TyKind::RigidTy(RigidTy::Array(elem, _)) => {
                Self::kani_mem_ty_validity_free(elem, depth + 1)
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => match def.kind() {
                AdtKind::Union => true,
                AdtKind::Struct => def.variants().iter().all(|variant| {
                    variant.fields().iter().all(|field| {
                        mono_ty::field_ty(field, &args)
                            .is_some_and(|t| Self::kani_mem_ty_validity_free(t, depth + 1))
                    })
                }),
                AdtKind::Enum => false,
            },
            _ => false,
        }
    }

    /// The pointee's bytes, read from the SSA register of the plain local the
    /// pointer tracks through `ref_pointees`.
    ///
    /// Only a primitive integer / `char` / `bool` local of exactly the pointee's
    /// size qualifies: its register is a flat little-endian bitvector of those
    /// bytes, so reinterpreting it as the pointee type is exact. Field, index and
    /// deref pointees, locals of other frames, aggregates (whose registers may be
    /// datatypes or payload-only flattenings) and size mismatches return `None`.
    fn kani_mem_pointee_register_value(&mut self, arg: &Operand, pointee_ty: Ty) -> Option<Expr> {
        let (Operand::Copy(place) | Operand::Move(place)) = arg else {
            return None;
        };
        let ptr_base = self.ssa_base_name(place);
        let pointee_base = self.ref_pointees.get(ptr_base.as_str()).cloned()?;
        let (fn_prefix, local_str) = pointee_base.rsplit_once("::local_")?;
        // A plain local only: `_field_`, `_idx_by_`, `_deref` suffixes do not parse.
        let local_idx: usize = local_str.parse().ok()?;
        if fn_prefix != self.ctx.current_fn_name() {
            return None;
        }
        let src_ty = self.body.locals().get(local_idx)?.ty;
        if !matches!(
            src_ty.kind(),
            TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Char | RigidTy::Bool)
        ) {
            return None;
        }
        let size = LayoutOf::new(pointee_ty).size_of()?;
        if LayoutOf::new(src_ty).size_of()? != size {
            return None;
        }
        let value = self.env_lookup(&pointee_base)?.clone();
        let value = if value.sort().is_bool() {
            Expr::ite(value, Expr::bitvec_const(1u64, 8), Expr::bitvec_const(0u64, 8))
        } else {
            value
        };
        (value.sort().bitvec_width()? as usize == size * 8).then_some(value)
    }

    /// Exact validity of a `char`, `bool` or `NonZero<int>` value given as a
    /// bitvector of the type's size; `None` for anything else.
    fn kani_mem_scalar_validity(pointee_ty: Ty, value: Expr) -> Option<Expr> {
        let width = value.sort().bitvec_width()? as usize;
        match pointee_ty.kind() {
            TyKind::RigidTy(RigidTy::Char) if width == 32 => Self::char_validity_constraint(value),
            TyKind::RigidTy(RigidTy::Bool) if width == 8 => {
                Some(value.bvule(Expr::bitvec_const(1u64, 8)))
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "NonZero" => {
                let Some(GenericArgKind::Type(inner)) = args.0.first() else {
                    return None;
                };
                if !matches!(inner.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))) {
                    return None;
                }
                // Pin the invariant to the layout rather than the name: the value
                // must be one scalar spanning the whole type whose valid range is
                // exactly `1..=MAX`, i.e. "non-zero" and nothing more.
                let shape = pointee_ty.layout().ok()?.shape();
                let ValueAbi::Scalar(Scalar::Initialized { value: prim, valid_range }) =
                    layout_value_abi!(shape)
                else {
                    return None;
                };
                let bits = prim.size(&MachineInfo::target()).bits();
                let max = if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
                if bits != width
                    || shape.size.bits() != width
                    || valid_range.start != 1
                    || valid_range.end != max
                {
                    return None;
                }
                Self::nonzero_validity_constraint(value)
            }
            _ => None,
        }
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

        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        if let Some(operand) = args.first() {
            self.guard_box_pointer_comparison(rustc_public::mir::BinOp::Eq, operand, &ptr, &zero);
        }
        self.assign_value_to_place(destination, ptr.eq(zero));
        target
    }
}
