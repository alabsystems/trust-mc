// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Over-approximation call dispatch helpers for CHC call terminators.
//!
//! Dispatches kani::mem helpers, UB/panic checks, and formatting stubs
//! with sound over-approximation semantics.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::Expr;

use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;
use super::{ChcCtx, Rule, RuleBody};
use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;
use crate::codegen_ay::stubs::StubKind;
use tracing::debug;
use trust_mc_core::violation::PropertyKind;

/// Extension trait for over-approximation dispatch in call-terminator codegen.
pub(in crate::codegen_ay::chc) trait CallDispatchOverapprox {
    fn try_dispatch_call_overapprox(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchOverapprox for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_overapprox(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let (bb_idx, func, destination, target, from_app, stmt_constraints, modified_locals) = (
            dcx.bb_idx,
            dcx.func,
            dcx.destination,
            dcx.target,
            dcx.from_app,
            dcx.stmt_constraints,
            dcx.modified_locals,
        );
        let stub = match self.detect_stub(func) {
            Some(s) => s,
            None => return false,
        };

        if stub.is_kani_mem() {
            let dest_local: usize = destination.local;
            // Part of #3768: graceful fallback instead of panic on unregistered locals
            let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
                debug!(dest_local, "CHC: kani_mem dest not in state map — sound over-approx");
                self.record_sound_fallback_reason("state_idx_missing_kani_mem_dest");
                if let Some(target) = target {
                    emit_sound_fallback_goto(
                        self,
                        from_app,
                        *target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                }
                return true;
            };
            if let Some(target) = target {
                if matches!(stub, StubKind::KaniMemCanDereference | StubKind::KaniMemCanWrite) {
                    let (result_expr, overapproximated) =
                        self.compute_kani_mem_predicate(func, dcx.args, modified_locals, true);
                    if overapproximated {
                        self.diagnostics.kani_mem_overapprox.inc();
                    }
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
                    let dest_var = Expr::var(
                        &*self.state_var_mgr.output_state_vars[dest_vec_idx].0,
                        out_sort.clone(),
                    );
                    let eq = self.make_coerced_eq_constraint(
                        &dest_var,
                        result_expr,
                        &out_sort,
                        dest_local,
                        "codegen_call_terminator::kani_mem_can_deref_or_write_align",
                    );
                    self.emit_goto_rule_extra(
                        from_app,
                        *target,
                        &new_output_args,
                        stmt_constraints,
                        eq,
                    );
                } else if matches!(
                    stub,
                    StubKind::KaniMemCanReadUnaligned | StubKind::KaniMemIsInbounds
                ) {
                    let (result_expr, overapproximated) =
                        self.compute_kani_mem_predicate(func, dcx.args, modified_locals, false);
                    if overapproximated {
                        self.diagnostics.kani_mem_overapprox.inc();
                    }
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
                    let dest_var = Expr::var(
                        &*self.state_var_mgr.output_state_vars[dest_vec_idx].0,
                        out_sort.clone(),
                    );
                    let label = if matches!(stub, StubKind::KaniMemIsInbounds) {
                        "codegen_call_terminator::kani_mem_is_inbounds"
                    } else {
                        "codegen_call_terminator::kani_mem_can_read_unaligned"
                    };
                    let eq = self.make_coerced_eq_constraint(
                        &dest_var,
                        result_expr,
                        &out_sort,
                        dest_local,
                        label,
                    );
                    self.emit_goto_rule_extra(
                        from_app,
                        *target,
                        &new_output_args,
                        stmt_constraints,
                        eq,
                    );
                } else if matches!(stub, StubKind::KaniMemIsPtrAligned) {
                    let (result_expr, overapproximated) =
                        self.compute_ptr_alignment_check(func, dcx.args, modified_locals);
                    if overapproximated {
                        self.diagnostics.kani_mem_overapprox.inc();
                    }
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
                    let dest_var = Expr::var(
                        &*self.state_var_mgr.output_state_vars[dest_vec_idx].0,
                        out_sort.clone(),
                    );
                    let eq = self.make_coerced_eq_constraint(
                        &dest_var,
                        result_expr,
                        &out_sort,
                        dest_local,
                        "codegen_call_terminator::kani_mem_is_ptr_aligned",
                    );
                    self.emit_goto_rule_extra(
                        from_app,
                        *target,
                        &new_output_args,
                        stmt_constraints,
                        eq,
                    );
                } else if matches!(stub, StubKind::KaniMemSameAllocation) {
                    // Part of #4249: Direct same_allocation encoding.
                    // Compares obj_id portions (upper 32 bits) of both pointer args
                    // and checks that the shared obj_id is valid.
                    // Encoding: extract(63,32,p1) == extract(63,32,p2) && obj_valid[extract(63,32,p1)]
                    let (result_expr, overapproximated) =
                        self.compute_same_allocation(dcx.args, modified_locals);
                    if overapproximated {
                        self.diagnostics.kani_mem_overapprox.inc();
                    }
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
                    let dest_var = Expr::var(
                        &*self.state_var_mgr.output_state_vars[dest_vec_idx].0,
                        out_sort.clone(),
                    );
                    let eq = self.make_coerced_eq_constraint(
                        &dest_var,
                        result_expr,
                        &out_sort,
                        dest_local,
                        "codegen_call_terminator::kani_mem_same_allocation",
                    );
                    self.emit_goto_rule_extra(
                        from_app,
                        *target,
                        &new_output_args,
                        stmt_constraints,
                        eq,
                    );
                } else if stub.is_kani_mem_assume_true() {
                    self.diagnostics.kani_mem_overapprox.inc();
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
                    let dest_var = Expr::var(
                        &*self.state_var_mgr.output_state_vars[dest_vec_idx].0,
                        out_sort.clone(),
                    );
                    let eq = self.make_coerced_eq_constraint(
                        &dest_var,
                        Expr::bool_const(true),
                        &out_sort,
                        dest_local,
                        "codegen_call_terminator::kani_mem_stub_true",
                    );
                    self.emit_goto_rule_extra(
                        from_app,
                        *target,
                        &new_output_args,
                        stmt_constraints,
                        eq,
                    );
                } else if stub.is_kani_mem_noop() {
                    self.diagnostics.kani_mem_overapprox.inc();
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
                } else {
                    unreachable!(
                        "kani::mem overapprox dispatch invariant violated: {stub:?} \
                         classified as kani_mem but no sub-branch matched"
                    );
                }
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "overapprox::kani_mem",
                    Some(stub),
                );
            }
            return true;
        }

        if stub.is_ub_panic() {
            if stub.is_panic_error() {
                // BSEM-18: per-property head for this panic path.
                let error_app = self.register_error_head(PropertyKind::Panic, bb_idx, None);
                let body =
                    RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, []);
                self.vc.add_rule(Rule::new(body, error_app));
                debug!("PanicError in bb{} — error() rule emitted", bb_idx);
            } else if stub.is_panic_unreachable() {
                debug!("PanicUnreachable in bb{} — no successor emitted", bb_idx);
            } else if let Some(target) = target {
                let dest_local: usize = destination.local;
                // Part of #3768: graceful fallback instead of panic
                let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
                    debug!(dest_local, "CHC: ub_panic dest not in state map — sound over-approx");
                    self.record_sound_fallback_reason("state_idx_missing_ub_panic_dest");
                    emit_sound_fallback_goto(
                        self,
                        from_app,
                        *target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                    return true;
                };
                if stub.is_ub_check_assume_true() {
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
                    let dest_var = Expr::var(
                        &*self.state_var_mgr.output_state_vars[dest_vec_idx].0,
                        out_sort.clone(),
                    );
                    let eq = self.make_coerced_eq_constraint(
                        &dest_var,
                        Expr::bool_const(true),
                        &out_sort,
                        dest_local,
                        "codegen_call_terminator::ub_panic_stub_true",
                    );
                    self.emit_goto_rule_extra(
                        from_app,
                        *target,
                        &new_output_args,
                        stmt_constraints,
                        eq,
                    );
                } else if stub.is_ub_check_noop() {
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
                } else {
                    unreachable!(
                        "ub/panic overapprox dispatch invariant violated: {stub:?} \
                         classified as ub_panic but no sub-branch matched"
                    );
                }
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "overapprox::ub_panic",
                    Some(stub),
                );
            }
            return true;
        }

        if stub.is_fmt() {
            // fmt construction (`Arguments::new` / `new_display` / `from_str`) is
            // INFALLIBLE and value-returning — it builds a formatter struct and
            // never panics. The old unconditional Panic head turned every
            // println!/format! into a spurious FAILURE (Print/side_effects.rs).
            // Emit a side-effects-only no-op for the value-returning case; the
            // havoced dest only flows into _print/write_fmt, which are already
            // `is_formatting_path` no-ops. Genuine panics still route through
            // `is_ub_panic` / `is_panic_error`, so no panic detection is lost —
            // but this removes an error net, so gate the full missed-bug wall.
            // Keep the Panic head only for the (unexpected) diverging case.
            if let Some(target) = target {
                let dest_local: usize = destination.local;
                if self.try_state_idx_for_local(dest_local).is_some() {
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
                } else {
                    emit_sound_fallback_goto(
                        self,
                        from_app,
                        *target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                }
                return true;
            }
            self.diagnostics.error_blocked_fmt.inc();
            debug!("fmt stub error-blocked (diverging): {:?} in bb{}", stub, bb_idx);
            // BSEM-18: per-property head for this error-blocked fmt path.
            let error_app = self.register_error_head(PropertyKind::Panic, bb_idx, None);
            let body = RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, []);
            self.vc.add_rule(Rule::new(body, error_app));
            return true;
        }

        if stub.is_range_bounds_contains() {
            // Part of #3930: let the later cmp-string dispatcher claim
            // RangeBounds::contains so char::any() keeps its Unicode guard
            // instead of forcing a conservative `true` result here.
            return false;
        }

        false
    }
}
