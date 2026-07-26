// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared destination emission for Option/Result call stubs.

use ay_bindings::Expr;

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::{
    CallCoerce, emit_sound_fallback_goto, emit_sound_fallback_goto_extra,
};
use super::codegen_rules::CodegenRules;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn emit_stub_call_result_with_extra(
        &mut self,
        result_expr: Option<Expr>,
        cx: &ChcCallContext<'_>,
        mut extra_constraints: Vec<Expr>,
    ) {
        let dest_local: usize = cx.destination.local;
        if let Some(result_expr) = result_expr {
            // Part of #3182: check for flattened destination first.
            if let Some(mut flat_constraints) =
                self.build_flattened_destination_constraints(dest_local, result_expr.clone())
            {
                flat_constraints.append(&mut extra_constraints);
                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    flat_constraints,
                );
                return;
            }
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                // Part of #2486: avoid stmt_constraints.to_vec() via make + extra.
                if let Some(eq_constraint) = self.make_coerced_eq_constraint(
                    &dest_var,
                    result_expr,
                    dest_var.sort(),
                    dest_local,
                    "emit_stub_call_result",
                ) {
                    extra_constraints.insert(0, eq_constraint);
                    let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                    self.emit_goto_rule_extra(
                        cx.from_app,
                        cx.target,
                        &new_output_args,
                        cx.stmt_constraints,
                        extra_constraints,
                    );
                    return;
                }
            }
            if !extra_constraints.is_empty() {
                emit_sound_fallback_goto_extra(
                    self,
                    cx.from_app,
                    cx.target,
                    cx.modified_locals,
                    &[dest_local],
                    cx.stmt_constraints,
                    extra_constraints,
                );
            } else {
                emit_sound_fallback_goto(
                    self,
                    cx.from_app,
                    cx.target,
                    cx.modified_locals,
                    &[dest_local],
                    cx.stmt_constraints,
                );
            }
            return;
        }
        emit_sound_fallback_goto(
            self,
            cx.from_app,
            cx.target,
            cx.modified_locals,
            &[dest_local],
            cx.stmt_constraints,
        );
    }
}
