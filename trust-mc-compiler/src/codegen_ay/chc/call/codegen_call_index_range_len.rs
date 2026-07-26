// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `<IndexRange as ExactSizeIterator>::len` call handler for CHC encoding.
//!
//! IndexRange is an internal iterator type used by slice indexing in the standard
//! library. Its ExactSizeIterator::len() must be modeled precisely to avoid
//! unconstrained returns that cause spurious CTREX in code using slice iteration.
//!
//! Split from the `codegen_call_dispatch_misc` module per file size limit.

use rustc_public::mir::BasicBlockIdx;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;

/// Extension trait for IndexRange ExactSizeIterator::len call handling.
pub(in crate::codegen_ay::chc) trait CallIndexRangeLen {
    fn try_codegen_index_range_exact_size_len(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: BasicBlockIdx,
    ) -> bool;
}

impl<'tcx, 'body> CallIndexRangeLen for ChcCtx<'tcx, 'body> {
    fn try_codegen_index_range_exact_size_len(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: BasicBlockIdx,
    ) -> bool {
        let func = dcx.func;
        let args = dcx.args;
        let destination = dcx.destination;
        let from_app = dcx.from_app;
        let stmt_constraints = dcx.stmt_constraints;
        let modified_locals = dcx.modified_locals;
        let is_index_range_len = self.resolve_callee_path(func).as_deref().is_some_and(|path| {
            path.contains("index_range::IndexRange")
                && path.contains("ExactSizeIterator")
                && path.ends_with("::len")
        });
        if !is_index_range_len {
            return false;
        }
        let Some(len_expr) = self.index_range_len_expr(args, modified_locals) else {
            return false;
        };

        let dest_local = destination.local;
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return false;
        };

        let mut extra_constraints = Vec::new();
        self.push_coerced_eq_constraint(
            &mut extra_constraints,
            &dest_var,
            len_expr,
            dest_var.sort(),
            dest_local,
            "codegen_call_dispatch_misc::IndexRangeExactSizeLen",
        );
        let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            from_app,
            target,
            &new_output_args,
            stmt_constraints,
            extra_constraints,
        );
        true
    }
}
