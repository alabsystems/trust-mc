// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Helper methods called from the call-terminator dispatch spine.
//!
//! Extracted from codegen_call.rs to stay under the 500-line file limit.
//! Contains identity-call dispatchers (array IntoIter, Pin) and the
//! slice::contains pre-inline interceptor.

use rustc_public::mir::Operand;

use crate::codegen_ay::stubs::StubKind;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_ctx::diagnostics::CellCounter;
use super::dispatch_helpers::DispatchHelpers;
use tracing::warn;

/// The fail-closed record of a write through `ManuallyDrop::deref_mut` into
/// a collection whose side state the identity does not carry (a `FailClose`
/// reason: `codegen_ctx::fallback_soundness` does not bless it).
const MANUALLY_DROP_COLLECTION_WRITE: &str = "manually_drop_collection_write_unmodelled";

/// Does `rvalue` read `local` (as a whole or through a projection)?
fn rvalue_mentions_local(rvalue: &rustc_public::mir::Rvalue, local: usize) -> bool {
    use rustc_public::mir::Rvalue;
    let operand =
        |op: &Operand| matches!(op, Operand::Copy(p) | Operand::Move(p) if p.local == local);
    match rvalue {
        Rvalue::Use(op, ..)
        | Rvalue::Cast(_, op, _)
        | Rvalue::UnaryOp(_, op)
        | Rvalue::Repeat(op, _) => operand(op),
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => operand(a) || operand(b),
        Rvalue::Aggregate(_, ops) => ops.iter().any(operand),
        Rvalue::Ref(_, _, place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::Len(place)
        | Rvalue::Discriminant(place)
        | Rvalue::CopyForDeref(place) => place.local == local,
        #[allow(unreachable_patterns)]
        _ => true,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Dispatch array IntoIter identity calls: `unsize_mut`/`unsize` and
    /// `ManuallyDrop::deref_mut`/`deref`.
    ///
    /// These are transparent reference-forwarding or wrapper-peeling operations
    /// on the array iterator path. Model as identity: dest = arg0 with coercion.
    /// Part of #3711.
    pub(in crate::codegen_ay::chc) fn try_dispatch_array_iter_identity_call(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        let is_unsize = self.detect_into_iter_unsize_call(dcx.func);
        let is_deref = !is_unsize && self.detect_manually_drop_deref_call(dcx.func);
        if !is_unsize && !is_deref {
            return false;
        }

        let label =
            if is_unsize { "array_iter::unsize_mut" } else { "array_iter::manually_drop_deref" };

        // A write through `ManuallyDrop::deref_mut` into a collection whose
        // length and capacity live in per-local side state (`Vec`, `String`,
        // the maps and sets) reaches the wrapper's memory but not that state:
        // `ManuallyDrop<Vec<T>>` has none of its own. The identity then read
        // the capacity `with_capacity` set after `push` grew it, and a
        // `capacity() == 1` assertion after two pushes verified clean where
        // Kani fails (walker fail-closed review 6 round 2, finding 4); on main
        // the same writes were lost to a havocked reference and `len()` after
        // `ManuallyDrop::into_inner` was certified Genuine on a program Kani
        // proves. Such a write fails closed; a `deref_mut` whose result only
        // feeds calls that read or expose the buffer (`as_mut_ptr`, `len`,
        // `capacity`) keeps the exact identity.
        if is_deref && self.manually_drop_deref_mut_may_write_side_state(dcx) {
            self.record_sound_fallback_reason(MANUALLY_DROP_COLLECTION_WRITE);
        }

        // `ManuallyDrop::deref` returns `&self.value`, the reference it was
        // handed: the result points where the argument does, so it takes the
        // argument's reference target, and a collection op through it
        // (`Vec::capacity`) finds the wrapped collection's side state
        // (walker fail-closed review 6, finding 8).
        self.emit_identity_call_with_success(
            dcx,
            label,
            |ctx, d| {
                d.args
                    .first()
                    .and_then(|arg| ctx.translate_operand_with_modified(arg, d.modified_locals))
            },
            |ctx, d| {
                if !is_deref || !d.destination.projection.is_empty() {
                    return;
                }
                let Some(Operand::Copy(src) | Operand::Move(src)) = d.args.first() else {
                    return;
                };
                if !src.projection.is_empty() {
                    return;
                }
                match ctx.ref_resolution.ref_targets.get(&src.local).cloned() {
                    Some(target) => {
                        ctx.ref_resolution.ref_targets.insert(d.destination.local, target);
                    }
                    None => {
                        ctx.ref_resolution.ref_targets.remove(&d.destination.local);
                    }
                }
            },
        )
    }

    /// Is this a `<ManuallyDrop<T> as DerefMut>::deref_mut` of a collection
    /// `T` with side state ([`Self::detect_collection_type`]) whose result
    /// reaches anything but a side-state-pure call on the collection
    /// (`as_mut_ptr`, `as_ptr`, `as_slice`, `as_mut_slice`, `len`,
    /// `capacity`, `is_empty`)? `true` when the destination is projected or
    /// its type does not resolve.
    fn manually_drop_deref_mut_may_write_side_state(&self, dcx: &DispatchCallContext<'_>) -> bool {
        use rustc_public::mir::{StatementKind, TerminatorKind};
        use rustc_public::ty::{RigidTy, TyKind};
        if !self.resolve_callee_path(dcx.func).is_some_and(|path| path.ends_with("::deref_mut")) {
            return false;
        }
        if !dcx.destination.projection.is_empty() {
            return true;
        }
        let dest = dcx.destination.local;
        let Some(decl) = self.body.locals().get(dest) else { return true };
        let inner = match self.resolve_body_ty(decl.ty).kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => self.resolve_body_ty(inner),
            _ => return true,
        };
        if Self::detect_collection_type(inner).is_none() {
            return false;
        }
        let mentions = |place: &rustc_public::mir::Place| place.local == dest;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
                    StatementKind::Assign(lhs, rvalue) => {
                        if mentions(lhs) {
                            continue;
                        }
                        // A reborrow, a copy, a deref: a use this does not
                        // classify.
                        if rvalue_mentions_local(rvalue, dest) {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
            if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind {
                let passes = args.iter().any(
                    |arg| matches!(arg, Operand::Copy(p) | Operand::Move(p) if p.local == dest),
                );
                if !passes {
                    continue;
                }
                let pure = self.resolve_callee_path(func).is_some_and(|path| {
                    matches!(
                        path.rsplit("::").next(),
                        Some(
                            "as_mut_ptr"
                                | "as_ptr"
                                | "as_slice"
                                | "as_mut_slice"
                                | "len"
                                | "capacity"
                                | "is_empty"
                        )
                    )
                });
                if !pure {
                    return true;
                }
            }
        }
        false
    }

    /// Dispatch `Pin::new_unchecked` / `Pin::as_mut` as transparent identity calls.
    ///
    /// `new_unchecked` preserves its pointer/reference argument unchanged, while
    /// `as_mut` forwards the referent Pin value from `&mut Pin<_>`.
    pub(in crate::codegen_ay::chc) fn try_dispatch_pin_identity_call(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        let is_new_unchecked = self.detect_pin_new_unchecked_call(dcx.func);
        let is_as_mut = !is_new_unchecked && self.detect_pin_as_mut_call(dcx.func);
        if !is_new_unchecked && !is_as_mut {
            return false;
        }

        let label = if is_new_unchecked { "pin::new_unchecked" } else { "pin::as_mut" };
        self.emit_identity_call_preserving_receiver_vtable(dcx, label, |ctx, d| {
            d.args.first().and_then(|arg| {
                if is_new_unchecked {
                    ctx.translate_operand_with_modified(arg, d.modified_locals)
                } else {
                    ctx.resolve_ref_operand(arg, d.modified_locals)
                        .or_else(|| ctx.translate_operand_with_modified(arg, d.modified_locals))
                }
            })
        })
    }

    /// Pre-inline dispatch for `[T]::contains` disjunction stub.
    ///
    /// For non-`u8` element types (e.g., `[char]::contains`), the stdlib
    /// implementation is `iter().any(|y| *x == *y)` — a loop. If `fn_inline`
    /// catches this first, it inlines the loop body (producing ChunksExact
    /// iterator state), which PDR cannot solve. Intercept here and emit
    /// a finite disjunction instead.
    ///
    /// Part of #4072: Dispatch priority fix for `pub_static` harness.
    pub(in crate::codegen_ay::chc) fn try_dispatch_call_slice_contains_pre_inline(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        let Some(target) = dcx.target else { return false };
        let callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func));
        let Some(ref path) = callee_path else { return false };
        if !super::codegen_call_cmp_string::slice_contains::detect_slice_contains(path) {
            return false;
        }
        super::codegen_call_cmp_string::slice_contains::try_codegen_slice_contains(
            self, dcx, *target,
        )
    }

    /// Pre-inline dispatch for `Range`/`RangeInclusive::contains`.
    ///
    /// The MIR `FunctionInlinePass` deliberately does NOT inline these
    /// (`handler_boundaries::is_handler_backed_range_contains`) because
    /// expanding through `RangeBounds::{start,end}_bound` and `Bound<&T>` turns
    /// value comparisons into reference-address comparisons. But the CHC
    /// `range_contains` handler only ran from the tail catch-all, AFTER
    /// `fn_inline` — which claimed the call, found the `RangeBounds::contains`
    /// body over the inline block budget, and bound the result to a FRESH
    /// SYMBOLIC BOOL. `(0..=1).contains(&x)` was then unconstrained, failing
    /// even for a concrete in-range `x`.
    ///
    /// Intercept here so the preserved handler boundary actually reaches its
    /// handler. `try_codegen_range_contains` returns false when it cannot
    /// resolve the bounds, leaving the existing dispatch chain untouched.
    pub(in crate::codegen_ay::chc) fn try_dispatch_call_range_contains_pre_inline(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        let Some(target) = dcx.target else { return false };
        let callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func));
        let Some(ref path) = callee_path else { return false };
        if !super::codegen_call_cmp_string::range_contains::detect_range_contains(path) {
            return false;
        }
        super::codegen_call_cmp_string::range_contains::try_codegen_range_contains(
            self, dcx, *target, path,
        )
    }

    /// Record a diverging call (`target=None`) that was claimed by a dispatcher
    /// but did not emit a transition or error rule.
    pub(in crate::codegen_ay::chc) fn record_diverging_call_drop(
        &self,
        func: &Operand,
        bb_idx: Option<usize>,
        route: &'static str,
        stub: Option<StubKind>,
    ) {
        let callee_path = self.resolve_callee_path(func);
        // KNOWN always-diverging PANIC intrinsics (abort; assert_*_valid /
        // assert_inhabited that the MIR lowered to a guaranteed panic on this
        // monomorphized type) are GENUINE failures — the caller's error() rule is
        // exact. Do NOT taint the CTREX with diverging_call_drop so it certifies
        // as Genuine (parity for oracle=fail tests) instead of EncodingGap.
        // SOUND: error() is fail-closed regardless; this changes only attribution.
        if callee_path.as_deref().is_some_and(
            crate::codegen_ay::chc::call::codegen_call::is_known_diverging_panic_intrinsic,
        ) {
            warn!(
                route,
                bb_idx = ?bb_idx,
                callee = callee_path.as_deref().unwrap_or("<unknown>"),
                "CHC diverging PANIC intrinsic — genuine error, not diverging_call_drop tainted"
            );
            return;
        }
        self.diagnostics.diverging_call_drop.inc();
        warn!(
            route,
            bb_idx = ?bb_idx,
            stub = ?stub,
            callee = callee_path.as_deref().unwrap_or("<unknown>"),
            "CHC diverging call (target=None) claimed by dispatcher with no emitted rule"
        );
    }
}
