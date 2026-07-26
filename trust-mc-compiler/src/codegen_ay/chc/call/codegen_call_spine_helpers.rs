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

        self.emit_identity_call(dcx, label, |ctx, d| {
            d.args
                .first()
                .and_then(|arg| ctx.translate_operand_with_modified(arg, d.modified_locals))
        })
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
        if callee_path
            .as_deref()
            .is_some_and(crate::codegen_ay::chc::call::codegen_call::is_known_diverging_panic_intrinsic)
        {
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
