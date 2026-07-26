// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dispatch-chain surface for string-path primitive comparison calls.
//!
//! This keeps the ordering-sensitive `try_dispatch_call_*` wrappers and
//! `codegen_call_primitive_cmp` together while leaving fallback policy in the
//! sibling `fallback_dispatch.rs` and `tail_dispatch.rs` helpers.

use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::{
    bit_intrinsics, cmp_handlers, div_euclid, exact_div, fast_math, float_predicates, math,
    misc_intrinsics, pow, range_contains, slice_as_array, slice_contains, step_wrapping,
    wrapping_abs,
};

/// Extension trait for primitive compare calls resolved from callee-path strings.
pub(in crate::codegen_ay::chc) trait CallCmpString {
    /// Handle primitive comparison trait calls:
    /// - `Ord::cmp`
    /// - `PartialOrd::partial_cmp`
    /// - `PartialOrd::{lt, le, gt, ge}`
    ///
    /// Also handles `Step::forward_unchecked/backward_unchecked`,
    /// wrapping arithmetic (`wrapping_add/sub/mul`), and
    /// checked arithmetic (`checked_add/sub/mul`) returning `Option<T>`.
    fn codegen_call_primitive_cmp(&mut self, dcx: &DispatchCallContext<'_>);

    /// Try to dispatch pow/wrapping_pow calls (Part of #3186).
    ///
    /// Returns `true` if the call was handled. Must be called before fn_inline
    /// in the dispatch chain to prevent fn_inline from inlining the loop body.
    fn try_dispatch_call_pow(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    /// Try to dispatch div_euclid/rem_euclid calls (Part of #3186).
    ///
    /// Returns `true` if the call was handled. Must be called before fn_inline
    /// to prevent fn_inline from inlining the branching MIR body.
    fn try_dispatch_call_euclid(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    /// Try to dispatch wrapping_abs/wrapping_neg calls (Part of #3293).
    ///
    /// Returns `true` if the call was handled. Must be called before fn_inline
    /// to prevent fn_inline from inlining wrapping_abs's branching body
    /// (which calls wrapping_neg internally).
    fn try_dispatch_call_wrapping_abs(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    /// Try to dispatch overflowing arithmetic calls (Part of #3300).
    ///
    /// Returns `true` if the call was handled. Must be called before fn_inline
    /// to prevent fn_inline from inlining the body. `overflowing_add_signed`
    /// appears in MIR for `ptr.offset()` (the compiler inlines `ptr.offset()`
    /// into calls to `overflowing_add_signed` rather than lowering to `BinOp::Offset`).
    fn try_dispatch_call_overflowing_arith(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    /// Try to dispatch saturating arithmetic calls before fn_inline.
    ///
    /// Handles both integer methods and raw `core/std::intrinsics::saturating_*`
    /// compiler intrinsics, whose callee bodies are not useful to inline.
    fn try_dispatch_call_saturating_arith(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    /// Try to dispatch bit-manipulation and identity intrinsics (Part of #3323).
    ///
    /// Returns `true` if the call was handled. Must be called before fn_inline
    /// because raw bit intrinsics are compiler builtins without MIR bodies, and
    /// wrappers like `hint::black_box` should stay identity-valued.
    fn try_dispatch_call_bit_intrinsic(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    /// Try to dispatch math intrinsic calls (Part of #3373).
    ///
    /// Returns `true` if the call was handled. Catches f32/f64 math intrinsics
    /// (floor, ceil, round, trunc, sqrt, sin, cos, etc.) and constant-folds
    /// them when arguments are compile-time constants. Must be called before
    /// fn_inline because math intrinsics are compiler builtins without MIR bodies.
    fn try_dispatch_call_math_intrinsic(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    /// Try to dispatch miscellaneous compiler intrinsics (Part of #3464).
    ///
    /// Returns `true` if the call was handled. Must be called before fn_inline
    /// to prevent fn_inline from inlining `typed_swap_nonoverlapping`'s MIR body
    /// (which expands into 38+ basic blocks of byte-level operations that the
    /// CHC solver cannot handle). Also catches volatile_load/store, forget,
    /// arith_offset, and other misc intrinsics.
    fn try_dispatch_call_misc_intrinsic(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    /// Part of #4086: Pre-inline comparison dispatch for `partial_cmp`/`gt`/`ge`/`lt`/`le`/`cmp`.
    ///
    /// These methods have NO StubKind assigned, so they skip `try_dispatch_call_misc`
    /// (StubKind CMP stub). Without this, fn_inline inlines the blanket ref impl
    /// `<&A as PartialOrd<&B>>::partial_cmp` body, but nested comparison calls
    /// inside the inlined body aren't intercepted (inline_known_calls only handles
    /// `eq`/`ne`). The string-path CMP handler has proper `resolve_ref_or_const_referent`
    /// operand resolution and `compute_array_cmp_result` for Array-sorted (SIMD) operands.
    fn try_dispatch_call_cmp_pre_inline(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn try_codegen_cmp_string_primary_dispatch(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: rustc_public::mir::BasicBlockIdx,
        callee_path: &Option<String>,
    ) -> bool {
        if let Some(path) = callee_path.as_deref()
            && let Some(is_forward) = Self::step_unchecked_method(path)
            && dcx.args.len() >= 2
        {
            step_wrapping::codegen_step_unchecked(self, dcx, target, is_forward);
            return true;
        }

        let cmp_method = callee_path.as_deref().and_then(Self::primitive_cmp_method);
        if let Some(method) = cmp_method
            && dcx.args.len() >= 2
        {
            cmp_handlers::codegen_primitive_cmp(self, dcx, target, method);
            return true;
        }

        false
    }

    fn try_codegen_cmp_string_arithmetic_dispatch(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: rustc_public::mir::BasicBlockIdx,
        callee_path: &Option<String>,
    ) -> bool {
        if let Some(path) = callee_path
            && let Some((arith_op, is_unchecked)) = Self::wrapping_arithmetic_method(path)
            && dcx.args.len() >= 2
        {
            step_wrapping::codegen_wrapping_arithmetic(self, dcx, target, arith_op, is_unchecked);
            return true;
        }

        if let Some(path) = callee_path
            && let Some(arith_op) = Self::checked_arithmetic_method(path)
            && dcx.args.len() >= 2
        {
            step_wrapping::codegen_checked_arithmetic(self, dcx, target, arith_op);
            return true;
        }

        if let Some(path) = callee_path
            && let Some(arith_op) = Self::overflowing_arithmetic_method(path)
            && dcx.args.len() >= 2
        {
            step_wrapping::codegen_overflowing_arithmetic(self, dcx, target, arith_op);
            return true;
        }

        if let Some(path) = callee_path
            && let Some(arith_op) = Self::saturating_arithmetic_method(path)
            && dcx.args.len() >= 2
        {
            step_wrapping::codegen_saturating_arithmetic(self, dcx, target, arith_op);
            return true;
        }

        if let Some(path) = callee_path
            && Self::is_exact_div(path)
            && dcx.args.len() >= 2
        {
            exact_div::codegen_exact_div(self, dcx, target);
            return true;
        }

        if let Some(path) = callee_path
            && Self::is_pow_method(path)
            && dcx.args.len() >= 2
        {
            pow::codegen_pow(self, dcx, target);
            return true;
        }

        if let Some(path) = callee_path
            && let Some(op) = Self::euclid_method(path)
            && dcx.args.len() >= 2
        {
            div_euclid::codegen_euclid(self, dcx, target, op);
            return true;
        }

        false
    }

    fn try_codegen_cmp_string_intrinsic_dispatch(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: rustc_public::mir::BasicBlockIdx,
        callee_path: &Option<String>,
    ) -> bool {
        if let Some(path) = callee_path
            && let Some(kind) = bit_intrinsics::detect_bit_intrinsic(path)
        {
            bit_intrinsics::codegen_bit_intrinsic(self, dcx, target, kind);
            return true;
        }

        if let Some(path) = callee_path
            && let Some(kind) = float_predicates::detect_float_predicate(path)
        {
            float_predicates::codegen_float_predicate(self, dcx, target, kind);
            return true;
        }

        if let Some(path) = callee_path
            && fast_math::detect_fast_math_intrinsic(path)
        {
            fast_math::codegen_fast_math_intrinsic(self, dcx, target, path);
            return true;
        }

        if let Some(path) = callee_path
            && let Some(kind) = misc_intrinsics::detect_misc_intrinsic(path)
        {
            misc_intrinsics::codegen_misc_intrinsic(self, dcx, target, kind);
            return true;
        }

        if let Some(path) = callee_path
            && range_contains::detect_range_contains(path)
            && range_contains::try_codegen_range_contains(self, dcx, target, path)
        {
            return true;
        }

        if let Some(path) = callee_path
            && slice_contains::detect_slice_contains(path)
            && slice_contains::try_codegen_slice_contains(self, dcx, target)
        {
            return true;
        }

        if let Some(path) = callee_path
            && slice_as_array::detect_slice_as_array(path)
            && slice_as_array::try_codegen_slice_as_array(self, dcx, target)
        {
            return true;
        }

        false
    }
}

impl<'tcx, 'body> CallCmpString for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_pow(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let callee_path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        let Some(ref path) = callee_path else { return false };
        if !Self::is_pow_method(path) || dcx.args.len() < 2 {
            return false;
        }
        let Some(target) = dcx.target else { return false };
        pow::codegen_pow(self, dcx, *target);
        true
    }

    fn try_dispatch_call_euclid(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let callee_path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        let Some(ref path) = callee_path else { return false };
        let Some(op) = Self::euclid_method(path) else { return false };
        if dcx.args.len() < 2 {
            return false;
        }
        let Some(target) = dcx.target else { return false };
        div_euclid::codegen_euclid(self, dcx, *target, op);
        true
    }

    fn try_dispatch_call_wrapping_abs(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let callee_path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        let Some(ref path) = callee_path else { return false };
        if dcx.args.is_empty() {
            return false;
        }
        let Some(target) = dcx.target else { return false };
        if Self::is_wrapping_abs(path) {
            wrapping_abs::codegen_wrapping_abs(self, dcx, *target);
            true
        } else if Self::is_wrapping_neg(path) {
            wrapping_abs::codegen_wrapping_neg(self, dcx, *target);
            true
        } else {
            false
        }
    }

    fn try_dispatch_call_overflowing_arith(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func));
        let Some(ref path) = callee_path else { return false };
        if dcx.args.len() < 2 {
            return false;
        }
        let Some(target) = dcx.target else { return false };
        if Self::is_overflowing_add_signed(path) {
            step_wrapping::codegen_overflowing_add_signed(self, dcx, *target);
            true
        } else if let Some(arith_op) = Self::overflowing_arithmetic_method(path) {
            debug!(path, op = ?arith_op, "CHC: overflowing arithmetic intercepted before fn_inline");
            step_wrapping::codegen_overflowing_arithmetic(self, dcx, *target, arith_op);
            true
        } else {
            false
        }
    }

    fn try_dispatch_call_saturating_arith(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func));
        let Some(ref path) = callee_path else { return false };
        let Some(arith_op) = Self::saturating_arithmetic_method(path) else {
            return false;
        };
        if dcx.args.len() < 2 {
            return false;
        }
        let Some(target) = dcx.target else { return false };
        debug!(path, op = ?arith_op, "CHC: saturating arithmetic intercepted before fn_inline");
        step_wrapping::codegen_saturating_arithmetic(self, dcx, *target, arith_op);
        true
    }

    fn try_dispatch_call_bit_intrinsic(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func));
        let Some(ref path) = callee_path else { return false };
        let Some(kind) = bit_intrinsics::detect_bit_intrinsic(path) else { return false };
        let Some(target) = dcx.target else { return false };
        debug!(?kind, path, "CHC: bit intrinsic intercepted before fn_inline");
        bit_intrinsics::codegen_bit_intrinsic(self, dcx, *target, kind);
        true
    }

    fn try_dispatch_call_math_intrinsic(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let callee_path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        let Some(ref path) = callee_path else { return false };
        let Some(is_f32) = math::detect_math_intrinsic(path) else { return false };
        if dcx.args.is_empty() {
            return false;
        }
        let Some(target) = dcx.target else { return false };
        math::codegen_math_intrinsic(self, dcx, *target, path, is_f32);
        true
    }

    fn try_dispatch_call_misc_intrinsic(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func));
        let Some(ref path) = callee_path else { return false };
        let Some(kind) = misc_intrinsics::detect_misc_intrinsic(path) else { return false };
        let Some(target) = dcx.target else { return false };
        debug!(?kind, path, "CHC: misc intrinsic intercepted before fn_inline (Part of #3464)");
        misc_intrinsics::codegen_misc_intrinsic(self, dcx, *target, kind);
        true
    }

    fn try_dispatch_call_cmp_pre_inline(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };
        let callee_path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        let Some(ref path) = callee_path else { return false };
        // Only intercept comparison methods that primitive_cmp_method recognizes.
        // Exclude eq/ne — those already have StubKind and are handled by
        // try_dispatch_call_misc → codegen_call_primitive_cmp_stub.
        // Part of #4203: Include min/max/clamp — their MIR bodies contain
        // nested PartialOrd dispatches that fn_inline cannot resolve for raw
        // pointers.
        let method = Self::primitive_cmp_method(path);
        if !matches!(
            method,
            Some("partial_cmp" | "cmp" | "lt" | "le" | "gt" | "ge" | "min" | "max" | "clamp")
        ) {
            return false;
        }
        let min_args = if method == Some("clamp") { 3 } else { 2 };
        if dcx.args.len() < min_args {
            return false;
        }
        debug!(
            path,
            method = method.unwrap_or("?"),
            bb_idx = dcx.bb_idx,
            "CHC: pre-inline CMP intercept (Part of #4086)"
        );
        // SAFETY: method is guaranteed Some by the matches! guard above.
        cmp_handlers::codegen_primitive_cmp(
            self,
            dcx,
            *target,
            method.expect("invariant: method guard"),
        );
        true
    }

    fn codegen_call_primitive_cmp(&mut self, dcx: &DispatchCallContext<'_>) {
        let Some(target) = dcx.target else {
            self.record_diverging_call_drop(
                dcx.func,
                Some(dcx.bb_idx),
                "cmp_string::primitive_cmp",
                None,
            );
            return;
        };
        let target = *target;
        let callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func));

        if self.try_codegen_cmp_string_primary_dispatch(dcx, target, &callee_path)
            || self.try_codegen_cmp_string_arithmetic_dispatch(dcx, target, &callee_path)
            || self.try_codegen_cmp_string_intrinsic_dispatch(dcx, target, &callee_path)
        {
            return;
        }

        self.codegen_tail_dispatch(dcx, &callee_path, target);
    }
}
