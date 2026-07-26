// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! UB check intrinsic dispatch: alignment, overlap, language UB.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::extract_method_name;
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// UB check intrinsics: alignment, overlap, language UB.
    pub(in crate::codegen_ay::statement) fn dispatch_ub_checks(
        &mut self,
        fn_name: &str,
        _args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let method = extract_method_name(fn_name)?;

        // Rust nightly 2025-12-03+ shortened the names (dropped `_and_not_null`).
        // Part of #3665: raw pointer cast path triggers maybe_is_aligned.
        if method == "maybe_is_aligned_and_not_null"
            || method == "is_aligned_and_not_null"
            || method == "maybe_is_aligned"
            || method == "is_aligned"
        {
            debug!("AY codegen: handling ub_checks alignment check (returning true)");
            let true_expr = Expr::bool_const(true);
            self.assign_value_to_place(destination, true_expr);
            return target;
        }
        if method == "maybe_is_nonoverlapping" || method == "is_nonoverlapping" {
            debug!("AY codegen: handling ub_checks overlap check (returning true)");
            let true_expr = Expr::bool_const(true);
            self.assign_value_to_place(destination, true_expr);
            return target;
        }
        if method == "check_language_ub" {
            debug!("AY codegen: handling ub_checks language UB check (skip)");
            return target;
        }
        None
    }
}
