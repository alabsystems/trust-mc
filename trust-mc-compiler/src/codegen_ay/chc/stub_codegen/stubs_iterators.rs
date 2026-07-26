// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC stub implementations for iterator intrinsics (checked_add_unsigned, unwrap_unchecked).
//!
//! Converted from include!() to proper module per #2595.
//! Vec and HashMap iterator stubs split to stubs_iterators_vec.rs and
//! stubs_iterators_hashmap.rs per #2246.
//! Split from stubs_impl.rs per #1880 for reviewability.

use std::collections::HashSet;
use std::sync::atomic::Ordering;

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::warn;

use super::codegen_ctx::diagnostics::GLOBAL_COUNTERS;
use super::stubs::StubKind;
use super::stubs_option_helpers::OptionHelpers;
use super::{ChcCtx, StubTranslateArgs};

/// Get the current CHC iterator unsoundness skip count (#1929).
/// Delegates to GLOBAL_COUNTERS (Part of #2906).
pub(in crate::codegen_ay) fn get_chc_iterator_unsound_skip_count() -> usize {
    GLOBAL_COUNTERS.iterator_unsound_skip.load(Ordering::Relaxed)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // =========================================================================
    // Iterator intrinsic stub interception (Part of #1712)
    // =========================================================================

    /// Accepted iterator intrinsic stub variants.
    const ITERATOR_INTRINSIC_STUBS: &'static [StubKind] =
        &[StubKind::CheckedAddUnsigned, StubKind::OptionUnwrapUnchecked];

    /// Detects if a function call is an iterator intrinsic that needs stubbing.
    ///
    /// Part of #1712: Range iterator intrinsics for CHC mode.
    /// These are used by Range iterators (for i in 0..10) which desugar to iterator calls.
    pub(in crate::codegen_ay::chc) fn detect_iterator_intrinsic_stub(
        &self,
        func: &Operand,
    ) -> Option<StubKind> {
        self.detect_stub_filtered(func, Self::ITERATOR_INTRINSIC_STUBS, "iterator_intrinsic")
    }

    /// Translates an iterator intrinsic call to CHC expressions.
    ///
    /// Part of #1712: Range iterator intrinsics for CHC mode.
    ///
    /// # Arguments
    /// * `stub` - The intrinsic stub kind
    /// * `args` - The call arguments
    /// * `modified_locals` - Set of locals modified in current block
    /// * `dest_local` - Destination local for the result
    ///
    /// # Contracts
    ///
    /// REQUIRES: `stub` is an iterator intrinsic StubKind (CheckedAddUnsigned, OptionUnwrapUnchecked).
    /// REQUIRES: `args` contains operands matching the stub's arity (2 for CheckedAddUnsigned, 1 for OptionUnwrapUnchecked).
    /// REQUIRES: `modified_locals` tracks locals modified in the current statement.
    /// ENSURES: Returns Some(expr) with valid SMT expression for supported operations.
    /// ENSURES: Returns None if arguments are insufficient or translation fails.
    /// ENSURES: CheckedAddUnsigned returns bitvector addition (may overflow in bounded model).
    /// ENSURES: OptionUnwrapUnchecked returns the unwrapped value.
    ///
    /// # Returns
    /// Expression representing the result, or None if translation failed.
    ///
    /// D3 table-driven dispatch (Part of #2304).
    pub(in crate::codegen_ay::chc) fn translate_iterator_intrinsic_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        dest_local: Option<usize>,
    ) -> Option<Expr> {
        let ctx = StubTranslateArgs { args, modified_locals, dest_local };
        stub_dispatch!(self, stub, &ctx, "translate_iterator_intrinsic_call",
            StubKind::CheckedAddUnsigned   => translate_checked_add_unsigned,
            StubKind::OptionUnwrapUnchecked => translate_option_unwrap_unchecked,
        )
    }

    // ===== Iterator intrinsic handlers (D3 table-driven, Part of #2304) =====

    /// i32::checked_add_unsigned(self, rhs: u32) -> Option<i32>.
    /// Model as: Some(self + rhs) where rhs is zero-extended to match self width.
    fn translate_checked_add_unsigned(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        if ctx.args.len() < 2 {
            warn!("translate_checked_add_unsigned: requires 2 args, got {}", ctx.args.len());
            return None;
        }

        let lhs = self.translate_operand_with_modified(&ctx.args[0], ctx.modified_locals)?;
        let rhs = self.translate_operand_with_modified(&ctx.args[1], ctx.modified_locals)?;

        // Part of #2007: coerce widths defensively in case operands differ
        let result = if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
            let (lhs, rhs) = Self::coerce_arithmetic_operands(lhs, rhs, false);
            lhs.bvadd(rhs)
        } else if lhs.sort().is_int() && rhs.sort().is_int() {
            lhs.int_add(rhs)
        } else {
            // Fail-closed fallback: non-bitvec/int operands collapse to zero.
            let lhs_bv = if lhs.sort().is_bitvec() { lhs } else { Expr::bitvec_const(0u64, 32) };
            let rhs_bv = if rhs.sort().is_bitvec() { rhs } else { Expr::bitvec_const(0u64, 32) };
            lhs_bv.bvadd(rhs_bv)
        };

        // Part of #1739: when destination Option<T> is flattened to
        // (is_some, payload), return the raw payload value here.
        if let Some(dest) = ctx.dest_local
            && self.flatten.flattened_tuple_locals.contains(&dest)
        {
            return Some(result);
        }

        // Non-flattened Option destination: wrap as Datatype Some(payload).
        let dest_vec_idx = ctx.dest_local.and_then(|dest| self.try_state_idx_for_local(dest));
        let option_sort = dest_vec_idx
            .and_then(|idx| self.state_var_mgr.output_state_vars.get(idx))
            .map(|(_, sort)| sort.clone())?;
        self.make_some_expr_for_option(result, &option_sort)
    }

    /// Option<T>::unwrap_unchecked(self) -> T.
    /// Model as: extract the value from Option, assuming it's Some.
    fn translate_option_unwrap_unchecked(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<Expr> {
        if ctx.args.is_empty() {
            warn!("translate_option_unwrap_unchecked: requires at least 1 arg");
            return None;
        }

        // Part of #1739: flattened Option local bare reads return None from
        // translate_operand_with_modified; recover via direct fld1 payload.
        if let Some(payload) =
            self.resolve_flattened_enum_payload(&ctx.args[0], ctx.modified_locals)
        {
            return Some(payload);
        }

        // Non-flattened Option value.
        self.translate_operand_with_modified(&ctx.args[0], ctx.modified_locals)
            .and_then(|option_expr| self.option_unwrap_value_on_some_path(option_expr))
    }
}
