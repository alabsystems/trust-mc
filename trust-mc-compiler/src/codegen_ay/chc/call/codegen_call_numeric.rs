// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BigInt and BigRational call handling.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::{Expr, SortInner};
use rustc_public::mir::Operand;
use tracing::{debug, error, warn};

use crate::codegen_ay::stubs::StubKind;

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::{
    CallCoerce, emit_sound_fallback_goto, emit_sound_fallback_goto_extra,
};
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_rules::CodegenRules;
use super::stubs_option_helpers::OptionHelpers;

/// Extension trait for BigInt/BigRational call handling on `ChcCtx`.
///
/// Pre-route handlers (Sign::mul, from_biguint, set_zero) are in
/// `codegen_call_bigint_preroute.rs` — they use path-based detection
/// that bypasses the method table.
pub(in crate::codegen_ay::chc) trait CallNumeric {
    fn codegen_call_bigint(&mut self, func: &Operand, cx: &ChcCallContext<'_>);

    fn codegen_call_bigrational(&mut self, cx: &ChcCallContext<'_>);
}

impl<'tcx, 'body> CallNumeric for ChcCtx<'tcx, 'body> {
    /// Handle BigInt stub calls (Part of #734).
    fn codegen_call_bigint(&mut self, func: &Operand, cx: &ChcCallContext<'_>) {
        let callee_path = self.resolve_callee_path(func);
        let is_biguint = callee_path.as_ref().is_some_and(|path| path.contains("BigUint"))
            || cx.args.iter().any(|arg| {
                if let Ok(arg_ty) = arg.ty(self.body.locals()) {
                    Self::type_name_contains_biguint(&arg_ty)
                } else {
                    false
                }
            });
        let dest_local: usize = cx.destination.local;
        debug!("bigint_stub_path stub={:?} has_target=true dest={}", cx.stub, dest_local);

        // Part of #2486: compute optional BigUint non-negativity guard without
        // cloning the entire stmt_constraints vector. Passed to emit_goto_rule_extra.
        let biguint_guard: Option<Expr> = if is_biguint
            && matches!(cx.stub, StubKind::BigIntIsZero)
            && let Some(first_arg) = cx.args.first()
            && let Some(arg) = self.get_bigint_arg(first_arg, cx.modified_locals)
        {
            Some(arg.int_ge(Expr::int_const(0)))
        } else {
            None
        };

        // Compound assignments write to args[0] location, not destination
        let is_compound_assign = matches!(
            cx.stub,
            StubKind::BigIntMulAssign | StubKind::BigIntAddAssign | StubKind::BigIntSubAssign
        );

        if is_compound_assign && !cx.args.is_empty() {
            self.codegen_bigint_compound_assign(cx, biguint_guard);
        } else if let Some(result_expr) =
            self.translate_bigint_call(cx.stub, cx.args, cx.modified_locals)
        {
            self.codegen_bigint_regular(result_expr, cx.stub, cx, biguint_guard);
        } else {
            // Could not translate BigInt call - EXPLICIT_FAIL (#1989)
            let count = self.diagnostics.bigint_unsound_skip.inc_get();
            error!(
                stub = ?cx.stub,
                "UNSOUND: Could not translate BigInt call (hit #{}) - forcing verification failure",
                count
            );
            let new_output_args =
                self.build_output_args(cx.modified_locals, &[cx.destination.local]);
            self.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                biguint_guard,
            );
            self.record_sound_fallback_reason("bigint_call_untranslated");
        }
    }

    /// Handle BigRational stub calls (Part of #911).
    fn codegen_call_bigrational(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        debug!("bigrational_stub_path stub={:?} has_target=true dest={}", cx.stub, dest_local);

        let is_compound_assign = matches!(
            cx.stub,
            StubKind::BigRationalAddAssign
                | StubKind::BigRationalSubAssign
                | StubKind::BigRationalMulAssign
                | StubKind::BigRationalDivAssign
        );

        if is_compound_assign && !cx.args.is_empty() {
            self.codegen_bigrational_compound_assign(cx);
        } else if let Some(result_expr) =
            self.translate_bigrational_call(cx.stub, cx.args, cx.modified_locals)
        {
            self.codegen_bigrational_regular(result_expr, cx);
        } else {
            // Could not translate BigRational call - emit plain goto
            emit_sound_fallback_goto(
                self,
                cx.from_app,
                cx.target,
                cx.modified_locals,
                &[cx.destination.local],
                cx.stmt_constraints,
            );
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle BigInt compound assignment (write to args[0] location).
    fn codegen_bigint_compound_assign(
        &mut self,
        cx: &ChcCallContext<'_>,
        biguint_guard: Option<Expr>,
    ) {
        if let Some(result_expr) = self.translate_bigint_call(cx.stub, cx.args, cx.modified_locals)
        {
            // Get the local from args[0] (the &mut BigInt reference)
            // Resolve through bigint_ref_targets to get actual BigInt local (#734)
            if let Operand::Copy(place) | Operand::Move(place) = &cx.args[0] {
                let ref_local: usize = place.local;
                let target_local = self
                    .ref_resolution
                    .bigint_ref_targets
                    .get(&ref_local)
                    .copied()
                    .unwrap_or(ref_local);
                debug!(
                    ref_local,
                    target_local,
                    resolved = ref_local != target_local,
                    "CHC: compound assignment BigInt reference resolution"
                );
                if let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(target_local).cloned()
                {
                    let dest_var = Expr::var(&*out_name, out_sort.clone());
                    let eq = self.make_coerced_eq_constraint(
                        &dest_var,
                        result_expr,
                        &out_sort,
                        target_local,
                        "codegen_bigint_compound_assign",
                    );
                    let new_output_args =
                        self.build_output_args(cx.modified_locals, &[target_local]);
                    self.emit_goto_rule_extra(
                        cx.from_app,
                        cx.target,
                        &new_output_args,
                        cx.stmt_constraints,
                        biguint_guard.into_iter().chain(eq),
                    );
                } else {
                    emit_sound_fallback_goto_extra(
                        self,
                        cx.from_app,
                        cx.target,
                        cx.modified_locals,
                        &[target_local],
                        cx.stmt_constraints,
                        biguint_guard,
                    );
                }
            } else {
                // SOUND AUDIT (#3369): args[0] not Copy/Move — compound assignment
                // target unknown, &[] extra_dests means target retains identity
                // (under-approx). Reclassified from record_sound_fallback.
                self.record_fallback();
                let new_output_args = self.build_output_args(cx.modified_locals, &[]);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    biguint_guard,
                );
            }
        } else {
            // SOUND AUDIT (#3369): translate_bigint_call failed — compound assignment
            // target unknown, &[] extra_dests means target retains identity
            // (under-approx). Reclassified from record_sound_fallback.
            self.record_fallback();
            let new_output_args = self.build_output_args(cx.modified_locals, &[]);
            self.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                biguint_guard,
            );
        }
    }

    /// Handle regular BigInt operations (write result to destination).
    fn codegen_bigint_regular(
        &mut self,
        result_expr: Expr,
        stub: StubKind,
        cx: &ChcCallContext<'_>,
        biguint_guard: Option<Expr>,
    ) {
        if self.try_emit_bigint_partial_cmp_flattened_destination(
            result_expr.clone(),
            cx,
            biguint_guard.clone(),
        ) {
            return;
        }
        let dest_local: usize = cx.destination.local;
        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            let out_sort = dest_var.sort();
            // Fix #769: Handle sort conversion for comparison results
            let final_result = if result_expr.sort() == out_sort {
                Some(result_expr.clone())
            } else if result_expr.sort().is_int() && out_sort.is_datatype() {
                self.wrap_ordering_int_in_option(result_expr.clone(), out_sort)
            } else if result_expr.sort().is_int() {
                if let SortInner::BitVec(bv) = out_sort.inner() {
                    if bv.width == 8 || bv.width == 32 {
                        // Part of #1229: Accept both widths for Ordering
                        Some(self.convert_ordering_int_to_bv(result_expr.clone(), bv.width))
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else if result_expr.sort().is_bool() && out_sort.is_bool() {
                Some(result_expr.clone())
            } else {
                None
            };

            if let Some(converted_result) = final_result {
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    converted_result,
                    out_sort,
                    dest_local,
                    "codegen_bigint_regular",
                );
                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    biguint_guard.into_iter().chain(eq),
                );
            } else {
                // Sort mismatch could not be resolved - EXPLICIT_FAIL (#1989)
                let count = self.diagnostics.bigint_unsound_skip.inc_get();
                error!(
                    result_sort = ?result_expr.sort(),
                    dest_sort = ?out_sort,
                    "UNSOUND: BigInt stub {:?} sort mismatch (hit #{}) - forcing verification failure",
                    stub,
                    count,
                );
                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    biguint_guard,
                );
                self.record_sound_fallback_reason("bigint_sort_mismatch");
            }
        } else {
            // No output var for destination — sound over-approx, leave unconstrained.
            let count = self.diagnostics.bigint_unsound_skip.inc_get();
            error!(
                dest_local = dest_local,
                "UNSOUND: BigInt stub has no output var for destination (hit #{}) - sound over-approx",
                count
            );
            let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                biguint_guard,
            );
            self.record_sound_fallback_reason("bigint_no_output_var");
        }
    }

    /// Handle BigRational compound assignment (write to args[0] location).
    fn codegen_bigrational_compound_assign(&mut self, cx: &ChcCallContext<'_>) {
        if let Some(result_expr) =
            self.translate_bigrational_call(cx.stub, cx.args, cx.modified_locals)
        {
            if let Operand::Copy(place) | Operand::Move(place) = &cx.args[0] {
                let ref_local: usize = place.local;
                let target_local = self
                    .ref_resolution
                    .ref_targets
                    .get(&ref_local)
                    .map_or(ref_local, |rt| rt.local);

                if let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(target_local).cloned()
                {
                    let dest_var = Expr::var(&*out_name, out_sort.clone());
                    let eq = self.make_coerced_eq_constraint(
                        &dest_var,
                        result_expr,
                        &out_sort,
                        target_local,
                        "codegen_bigrational_compound_assign",
                    );
                    let new_output_args =
                        self.build_output_args(cx.modified_locals, &[target_local]);
                    self.emit_goto_rule_extra(
                        cx.from_app,
                        cx.target,
                        &new_output_args,
                        cx.stmt_constraints,
                        eq,
                    );
                } else {
                    emit_sound_fallback_goto(
                        self,
                        cx.from_app,
                        cx.target,
                        cx.modified_locals,
                        &[target_local],
                        cx.stmt_constraints,
                    );
                }
            } else {
                // SOUND AUDIT (#3369): args[0] not Copy/Move — compound assignment
                // target unknown, &[] extra_dests means target retains identity
                // (under-approx). Reclassified from record_sound_fallback.
                self.record_fallback();
                let new_output_args = self.build_output_args(cx.modified_locals, &[]);
                self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            }
        } else {
            // SOUND AUDIT (#3369): translate_bigrational_call failed — compound assignment
            // target unknown, &[] extra_dests means target retains identity
            // (under-approx). Reclassified from record_sound_fallback.
            self.record_fallback();
            let new_output_args = self.build_output_args(cx.modified_locals, &[]);
            self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
        }
    }

    /// Handle regular BigRational operations (write result to destination).
    fn codegen_bigrational_regular(&mut self, result_expr: Expr, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            let out_sort = dest_var.sort();
            // Handle sort conversion: BigRational comparisons return Bool
            let final_result = if result_expr.sort() == out_sort {
                result_expr
            } else if result_expr.sort().is_bool() && out_sort.is_bitvec() {
                let bits =
                    out_sort.bitvec_width().expect("bitvec destination sort must report width");
                Expr::ite(
                    result_expr,
                    Expr::bitvec_const(1u64, bits),
                    Expr::bitvec_const(0u64, bits),
                )
            } else {
                warn!(
                    fn_name = %self.fn_name,
                    result_sort = ?result_expr.sort(),
                    dest_sort = ?out_sort,
                    dest_local,
                    "CHC: bigrational_regular sort mismatch — result is not Bool→BV convertible; \
                     passing through to make_coerced_eq_constraint which may drop"
                );
                result_expr
            };
            let eq = self.make_coerced_eq_constraint(
                &dest_var,
                final_result,
                out_sort,
                dest_local,
                "codegen_bigrational_regular",
            );
            let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                eq,
            );
        } else {
            // resolve_destination failed — bigrational result unconstrained (Part of #3123).
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
}
