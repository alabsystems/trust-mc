// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tail dispatch for `codegen_call_primitive_cmp`: handlers that fire after all
//! submodule-delegated dispatchers (intrinsics, comparison, arithmetic, etc.).
//!
//! Contains: formatting error-block, range constructors, NonNull::from passthrough,
//! pointer-wrapper constructors/deref, is_power_of_two, known-stdlib unconstrained,
//! Drop::drop call-terminators, and the unhandled catch-all.
//!
//! Extracted from `mod.rs` per #3254 packet 3.

use ay_bindings::Expr;
use rustc_public::mir::BasicBlockIdx;
use tracing::debug;

use super::super::super::codegen_expr_array_eq::{build_spec_array_eq, recover_spec_array_eq_len};
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_call_misc::CallMisc;
use super::super::codegen_ctx::diagnostics::CellCounter;
use super::super::codegen_rules::CodegenRules;
use super::super::{ChcCtx, RelationApp, Rule, RuleBody, chc_debug_enabled};
use super::fallback_dispatch::TailFallbackOutcome;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle all call paths that remain after submodule-delegated dispatchers.
    ///
    /// This is the terminal handler in `codegen_call_primitive_cmp`: every call
    /// that reaches here was NOT claimed by step_wrapping, cmp_handlers,
    /// exact_div, pow, div_euclid, bit_intrinsics, float_predicates, fast_math,
    /// misc_intrinsics, range_contains, slice_contains, or slice_as_array.
    ///
    /// The handler chain within is ordered by specificity (most specific first):
    /// 1. Formatting path error-block
    /// 2. Range/RangeInclusive constructors
    /// 3. NonNull::from passthrough
    /// 4. Pointer-wrapper constructor/deref (Rc, Arc)
    /// 5. is_power_of_two
    /// 6. Known stdlib unconstrained (delegates to shared fallback helper)
    /// 7. Drop::drop call-terminators
    /// 8. Unhandled catch-all (delegates to shared fallback helper)
    pub(in crate::codegen_ay::chc) fn codegen_tail_dispatch(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        callee_path: &Option<String>,
        target: BasicBlockIdx,
    ) {
        let bb_idx = dcx.bb_idx;
        let args = dcx.args;
        let from_app = dcx.from_app;
        let stmt_constraints = dcx.stmt_constraints;
        let modified_locals = dcx.modified_locals;
        let dest_local: usize = dcx.destination.local;

        // Error-blocking for formatting/debug paths (Part of #3323, Strategy 1).
        if let Some(path) = callee_path
            && Self::is_formatting_path(path)
        {
            self.diagnostics.error_blocked_fmt.inc();
            debug!("fmt path error-blocked: {} (bb{}->bb{})", path, bb_idx, target);
            let error_app = RelationApp::new("error", Vec::new());
            let body = RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, []);
            self.vc.add_rule(Rule::new(body, error_app));
            return;
        }

        // Range/RangeInclusive constructor handling (Part of #3470).
        if let Some(path) = callee_path
            && Self::is_range_constructor(path)
            && args.len() >= 2
        {
            debug!("range constructor detected: {} (bb{}->bb{})", path, bb_idx, target);
            if let Some(constraints) =
                self.try_constrain_range_constructor(dest_local, args, modified_locals, path)
            {
                let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    from_app,
                    target,
                    &new_output_args,
                    stmt_constraints,
                    constraints,
                );
                debug!("range constructor encoded: {} (bb{}->bb{})", path, bb_idx, target);
                return;
            }
        }

        // NonNull::from passthrough (Part of #3589).
        if let Some(path) = callee_path
            && (path.contains("NonNull") && path.contains("From") && path.contains("from"))
            && !args.is_empty()
        {
            if self.try_codegen_nonnull_from(dcx, callee_path, target, dest_local) {
                return;
            }
        }

        // Pointer-wrapper constructor/deref (Part of #3589).
        if let Some(path) = callee_path {
            if Self::is_shared_pointer_wrapper_constructor_path(path) {
                self.codegen_pointer_wrapper_from_inner_in(dcx);
                return;
            }
            if Self::is_pointer_wrapper_deref_path(path) {
                self.codegen_pointer_wrapper_deref_call(dcx);
                return;
            }
        }

        // is_power_of_two (Part of #3638).
        if let Some(path) = callee_path
            && path.contains("is_power_of_two")
            && !args.is_empty()
        {
            if self.try_codegen_is_power_of_two(dcx, target, dest_local) {
                return;
            }
        }

        // Known stdlib unconstrained (Part of #3323 Phase 3, #3395, #3589).
        if let Some(path) = callee_path
            && Self::is_known_stdlib_unconstrained(path)
        {
            self.codegen_known_stdlib_unconstrained(dcx, path, target, dest_local);
            return;
        }

        // Drop::drop call-terminators (Part of #3795).
        if let Some(path) = callee_path
            && path.contains("Drop>::drop")
        {
            debug!(
                "Drop::drop call-terminator modeled as goto: {} (bb{}->bb{})",
                path, bb_idx, target
            );
            let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
            self.emit_goto_rule(from_app, target, &new_output_args, stmt_constraints);
            return;
        }

        // SpecArrayEq::spec_eq — element-wise array equality (Part of #3875).
        // The inline body has a loop (slice comparison) that the walker can't
        // handle. Resolve the reference args to their referent arrays and
        // route them through the shared finite-array equality helper.
        if let Some(path) = callee_path
            && path.contains("SpecArrayEq")
            && path.contains("spec_eq")
            && args.len() == 2
        {
            if self.try_codegen_spec_array_eq(dcx, path, target, dest_local) {
                return;
            }
        }

        // Unhandled call — sound over-approximation (#3099, #3395, #3589).
        self.codegen_unhandled_call(dcx, callee_path, target, dest_local);
    }

    /// NonNull::from passthrough: pointer identity preservation (Part of #3589).
    fn try_codegen_nonnull_from(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        callee_path: &Option<String>,
        target: BasicBlockIdx,
        dest_local: usize,
    ) -> bool {
        let args = dcx.args;
        let modified_locals = dcx.modified_locals;
        let Some(arg0) = args.first() else { return false };
        let Some(arg_expr) = self.translate_operand_with_modified(arg0, modified_locals) else {
            return false;
        };
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return false;
        };
        let constraint = self.make_coerced_eq_constraint(
            &dest_var,
            arg_expr,
            dest_var.sort(),
            dest_local,
            "nonnull_from_passthrough",
        );
        // Propagate allocation identity through NonNull::from.
        let src_local = match arg0 {
            rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p)
                if p.projection.is_empty() =>
            {
                Some(p.local)
            }
            _ => None,
        };
        if let Some(obj_id) = src_local
            .and_then(|sl| self.known_alloc_ids.get(&sl).copied())
            .or_else(|| src_local.and_then(|sl| self.trace_deref_store_alloc_id(sl)))
        {
            self.known_alloc_ids.insert(dest_local, obj_id);
        } else {
            self.known_alloc_ids.remove(&dest_local);
        }
        let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            constraint,
        );
        if let Some(path) = callee_path {
            debug!("NonNull::from passthrough: {} (bb{}->bb{})", path, dcx.bb_idx, target);
        }
        true
    }

    /// is_power_of_two: `n != 0 && (n & (n - 1)) == 0` (Part of #3638).
    fn try_codegen_is_power_of_two(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: BasicBlockIdx,
        dest_local: usize,
    ) -> bool {
        let modified_locals = dcx.modified_locals;
        let Some(n_expr) = self.translate_operand_with_modified(&dcx.args[0], modified_locals)
        else {
            return false;
        };
        if !n_expr.sort().is_bitvec() {
            return false;
        }
        let Some(width) = n_expr.sort().bitvec_width() else { return false };
        let zero = Expr::bitvec_const(0u64, width);
        let one = Expr::bitvec_const(1u64, width);
        let nonzero = n_expr.clone().ne(zero.clone());
        let n_minus_1 = n_expr.clone().bvsub(one);
        let and_check = n_expr.bvand(n_minus_1).eq(zero);
        let bool_result = nonzero.and(and_check);
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else { return false };
        let out_sort = dest_var.sort();
        let converted = if out_sort.is_bool() {
            bool_result
        } else if let Some(w) = out_sort.bitvec_width() {
            Expr::ite(bool_result, Expr::bitvec_const(1u64, w), Expr::bitvec_const(0u64, w))
        } else {
            bool_result
        };
        let eq_constraint = self.make_coerced_eq_constraint(
            &dest_var,
            converted,
            out_sort,
            dest_local,
            "is_power_of_two",
        );
        let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            eq_constraint,
        );
        debug!("is_power_of_two encoded: (bb{}->bb{})", dcx.bb_idx, target);
        true
    }

    /// SpecArrayEq::spec_eq: resolve reference args and compare arrays (Part of #3875).
    fn try_codegen_spec_array_eq(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        callee_path: &str,
        target: BasicBlockIdx,
        dest_local: usize,
    ) -> bool {
        let modified_locals = dcx.modified_locals;
        let bool_eq = if let Some(eq) = self.fixed_unit_array_eq_expr_from_args(dcx.args) {
            eq
        } else {
            let lhs_expr = self.resolve_ref_or_const_referent(&dcx.args[0], modified_locals);
            let rhs_expr = self.resolve_ref_or_const_referent(&dcx.args[1], modified_locals);
            let (Some(lhs), Some(rhs)) = (lhs_expr, rhs_expr) else { return false };
            let len =
                recover_spec_array_eq_len(Some(callee_path), dcx.args.first(), self.body.locals());
            let Some(bool_eq) = build_spec_array_eq(&lhs, &rhs, len) else {
                return false;
            };
            bool_eq
        };
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else { return false };
        let out_sort = dest_var.sort();
        let converted = if out_sort.is_bool() {
            bool_eq
        } else if let Some(w) = out_sort.bitvec_width() {
            Expr::ite(bool_eq, Expr::bitvec_const(1u64, w), Expr::bitvec_const(0u64, w))
        } else {
            bool_eq
        };
        let eq_constraint = self.make_coerced_eq_constraint(
            &dest_var,
            converted,
            out_sort,
            dest_local,
            "spec_array_eq",
        );
        let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            eq_constraint,
        );
        debug!("SpecArrayEq::spec_eq encoded: (bb{}->bb{})", dcx.bb_idx, target);
        true
    }

    /// Known stdlib unconstrained handler (Part of #3323 Phase 3, #3142).
    ///
    /// Delegates to the shared receiver-sensitive fallback helper in
    /// `fallback_dispatch.rs`. Only path-specific counters and logging remain here.
    fn codegen_known_stdlib_unconstrained(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        path: &str,
        target: BasicBlockIdx,
        dest_local: usize,
    ) {
        let bb_idx = dcx.bb_idx;

        // Drop::drop on stdlib types: clean goto, no fallback (Part of #3561).
        if path.contains("Drop>::drop") {
            debug!(
                "Drop::drop via known_stdlib path modeled as goto: {} (bb{}->bb{})",
                path, bb_idx, target
            );
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            self.emit_goto_rule(dcx.from_app, target, &new_output_args, dcx.stmt_constraints);
            return;
        }
        debug!("known stdlib unconstrained: {} (bb{}->bb{})", path, bb_idx, target);
        self.diagnostics.known_stdlib_unconstrained.inc();
        self.resolve_tail_fallback(
            dcx.func,
            dcx.args,
            dcx.from_app,
            dcx.stmt_constraints,
            dcx.modified_locals,
            target,
            dest_local,
        );
    }

    /// Unhandled call catch-all — delegates to shared receiver-sensitive
    /// fallback helper (#3099, #3142). Only path-specific counters and
    /// logging remain here.
    fn codegen_unhandled_call(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        callee_path: &Option<String>,
        target: BasicBlockIdx,
        dest_local: usize,
    ) {
        let bb_idx = dcx.bb_idx;
        let outcome = self.resolve_tail_fallback(
            dcx.func,
            dcx.args,
            dcx.from_app,
            dcx.stmt_constraints,
            dcx.modified_locals,
            target,
            dest_local,
        );
        match outcome {
            TailFallbackOutcome::Inferable => {
                if chc_debug_enabled()
                    && let Some(path) = callee_path
                {
                    debug!("inferable call {} (bb{}->bb{})", path, bb_idx, target);
                }
            }
            TailFallbackOutcome::DemotedMutReceiver => {
                self.diagnostics.unhandled_call.inc();
                debug!(
                    fn_name = %self.fn_name,
                    ?callee_path,
                    bb_idx,
                    "DEMOTED:UNHANDLED mutable-receiver call"
                );
            }
            TailFallbackOutcome::SoundFallback => {
                self.diagnostics.unhandled_call.inc();
                debug!(
                    fn_name = %self.fn_name,
                    ?callee_path,
                    bb_idx,
                    "SOUND:UNHANDLED immutable-receiver call"
                );
            }
        }
    }
}
