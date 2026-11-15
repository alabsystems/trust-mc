// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Comparisons the encoding-level fast paths must not decide.
//!
//! The CHC lane's comparison handlers (the primitive `PartialEq` and order
//! stubs, the array, slice and `Vec` equalities, the datatype fast path of
//! the inline walker) compare the two values' encodings, and for a sequence
//! the encodings of its elements. That is Rust's comparison only when it
//! compares bits (`shared::compare_loops::comparison_is_faithful`): a float
//! element compared by its bits made `[0.0f32] == [-0.0f32]` and
//! `Some(0.0f32) == Some(-0.0)` fail with certified counterexamples and
//! `[f32::NAN] == [f32::NAN]` verify clean, a reference element compared by
//! its address made `[&x] == [&y]` with `x == y` fail certified, a
//! hand-written `PartialEq` was replaced by bit equality, and a float array's
//! order by its bits ordered `-1.0` above `1.0` (walker fail-closed review,
//! round 3 of the repair after the merge with main;
//! `value_eq_semantics_dual.rs`).
//!
//! Such a comparison is dispatched here, ahead of every handler: `==` is
//! built exactly where the values can be read
//! ([`compare_loops::rust_value_eq`], element by element for a slice or a
//! `Vec`); otherwise the callee's own body is walked (the inline walker's
//! fast paths refuse it the same way), and failing that the result is left
//! unconstrained.

use ay_bindings::Expr;
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_fallback_emit::{emit_sound_fallback_goto, try_emit_precise_call_result};
use super::codegen_call_fn_inline::CallDispatchFnInline;
use crate::codegen_ay::shared::compare_loops::{self, ComparisonCall};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Dispatch a comparison call the fast paths must not decide (see the
    /// module docs); `false` for every other call.
    pub(in crate::codegen_ay::chc) fn try_dispatch_call_unfaithful_comparison(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        let Some(target) = *dcx.target else { return false };
        if dcx.args.len() < 2 {
            return false;
        }
        let Some(path) = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func))
        else {
            return false;
        };
        let Some(kind) = compare_loops::comparison_call(&path) else { return false };
        if matches!(kind, ComparisonCall::Eq { .. })
            && self.has_heterogeneous_sequence_elements(dcx.func, self.body.locals())
        {
            // Neither encoding equality nor exact_value_eq's single element
            // type represents a heterogeneous PartialEq implementation.
            self.record_sound_fallback_reason("heterogeneous_sequence_comparison");
            emit_sound_fallback_goto(
                self,
                dcx.from_app,
                target,
                dcx.modified_locals,
                &[dcx.destination.local],
                dcx.stmt_constraints,
            );
            return true;
        }
        let Ok(arg_ty) = dcx.args[0].ty(self.body.locals()) else { return false };
        let compared = self.resolve_body_ty(arg_ty);
        if super::inline_array_semantic_eq::try_codegen_array_semantic_eq(self, dcx, target, &path)
        {
            return true;
        }
        if compare_loops::comparison_is_faithful(kind, compared) {
            return false;
        }
        let dest_local = dcx.destination.local;
        debug!(
            fn_name = %self.fn_name,
            path = path.as_str(),
            ?compared,
            "CHC: comparison whose result is not its encodings' comparison"
        );
        if let ComparisonCall::Eq { negated } = kind
            && let Some(eq) = self.exact_value_eq(dcx, compare_loops::peel_refs(compared))
        {
            let result = if negated { eq.not() } else { eq };
            debug!(fn_name = %self.fn_name, %result, "CHC: comparison decided exactly");
            try_emit_precise_call_result(
                self,
                Some(result),
                dest_local,
                dcx.from_app,
                target,
                dcx.modified_locals,
                dcx.stmt_constraints,
                [],
                "unfaithful_comparison::exact_eq",
            );
            return true;
        }
        if self.try_dispatch_call_fn_inline(dcx) {
            return true;
        }
        self.record_sound_fallback_reason("comparison_not_encoding_faithful");
        emit_sound_fallback_goto(
            self,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dest_local],
            dcx.stmt_constraints,
        );
        true
    }

    /// Rust's `==` on the two values a comparison call compares, `compared`
    /// being their type behind its references, read from the values: element
    /// by element for a slice, a `str` or a `Vec`, else the two referents
    /// through [`compare_loops::rust_value_eq`].
    fn exact_value_eq(&mut self, dcx: &DispatchCallContext<'_>, compared: Ty) -> Option<Expr> {
        let modified_locals = dcx.modified_locals;
        let is_vec = matches!(
            compared.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _))
                if rustc_public::CrateDef::name(&def).ends_with("vec::Vec")
        );
        let is_slice = matches!(compared.kind(), TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str));
        // A `Vec` compared whole is left to its body: the lane states its
        // element equality with a quantifier (see below).
        if is_vec {
            return None;
        }
        if is_slice {
            let elem = compare_loops::compared_elem_ty(compared)?;
            let elem_eq = move |x: Expr, y: Expr| compare_loops::rust_value_eq(elem, &x, &y);
            // The length, when both sides' is a known constant: lengths that
            // differ decide `==` alone, and an equal one is expanded element
            // by element. With no constant length the equality would be a
            // quantifier over the element comparison, which ay `d80d17a90`
            // was measured to decide wrongly with a certified counterexample
            // (`!(vec![1.0f32][..] == vec![2.0f32][..])` failed Genuine):
            // that comparison is not built.
            let lhs_len = self.resolve_const_slice_eq_len(dcx.args, 0, modified_locals);
            let rhs_len = self.resolve_const_slice_eq_len(dcx.args, 1, modified_locals);
            let const_len = match (lhs_len, rhs_len) {
                (Some(l), Some(r)) if l != r => return Some(Expr::bool_const(false)),
                (Some(l), Some(_)) => usize::try_from(l).ok(),
                _ => None,
            };
            let lhs = self.resolve_slice_backing(&dcx.args[0], modified_locals)?;
            let rhs = self.resolve_slice_backing(&dcx.args[1], modified_locals)?;
            if *lhs.data.as_expr().sort() != *rhs.data.as_expr().sort() {
                return None;
            }
            return Self::slice_eq_formula_with(&lhs, &rhs, &elem_eq, const_len, false);
        }
        let lhs = self
            .resolve_ref_or_const_referent_tagged(&dcx.args[0], modified_locals)
            .and_then(|referent| self.slice_eq_referent_datum(referent))?;
        let rhs = self
            .resolve_ref_or_const_referent_tagged(&dcx.args[1], modified_locals)
            .and_then(|referent| self.slice_eq_referent_datum(referent))?;
        compare_loops::rust_value_eq(compared, &lhs, &rhs)
    }
}
