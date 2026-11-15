// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Iterator adapter call handling (map/filter/fold/sum/collect/flatten/range-into-iter/range-next).
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//! Split into sub-modules per #4129 (500 LOC threshold).
//!
//! Sub-modules:
//! - `constructor`: IterMap/IterFilter/IterFilterMap adapter construction
//! - `zip`: IterZip adapter construction and sidecar propagation
//! - `collect`: IterCollect dispatch and Vec constraint threading
//! - `epilogue`: shared result constraint emission and goto rule
//! - `helpers`: utility builders (advance, rebuild, symbolic, option payloads)
//! - `next`: next-variant and range dispatch arm helpers
//! - `collect_data`: IterCollect data constraint builders for transform chains
//! - `concrete_eval`: concrete BV evaluation and MIR string extraction
//! - `range`: range-specific helpers (advance, flattened fields, signedness)
//! - `reduce`: IterFold/IterSum reduction dispatch
//! - `size_hint`: authenticated native lower and upper bounds

mod collect;
mod collect_data;
mod concrete_eval;
mod constructor;
mod epilogue;
mod fold_precise;
mod helpers;
mod next;
mod range;
mod reduce;
mod size_hint;
mod zip;

use ay_bindings::Expr;
pub(in crate::codegen_ay::chc) use range::unanimous_borrowed_local;
pub(in crate::codegen_ay::chc) use reduce::closure_arg_may_carry_obligation;
pub(in crate::codegen_ay::chc) use reduce::closure_ty_may_carry_obligation;
#[cfg(test)]
pub(in crate::codegen_ay::chc) use reduce::saturating_add;
use rustc_public::mir::Operand;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use std::sync::atomic::Ordering;

use crate::codegen_ay::iter_closure_obligation::{
    UNMODELED_CLOSURE_MESSAGE, ty_may_run_obligated_closure,
};
use crate::codegen_ay::stubs::StubKind;
use trust_mc_core::violation::PropertyKind;

use super::ChcCtx;
use super::chc_call_context::{ChcCallContext, DispatchCallContext};
use super::codegen_call_coerce::CallCoerce;
use super::codegen_ctx::diagnostics::CellCounter;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use super::codegen_ctx::diagnostics::GLOBAL_COUNTERS;
use super::codegen_rules::CodegenRules;
use tracing::debug;

// Telemetry counters consolidated into GLOBAL_COUNTERS (Part of #2906).
// Production callers use self.diagnostics.range_spec_next_* instead.

/// Snapshot of RangeSpecNext path-selection counters.
#[cfg(all(test, feature = "compiler-corpus-tests"))]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(in crate::codegen_ay::chc) struct RangeSpecNextPathCounts {
    pub datatype: usize,
    pub flattened: usize,
    pub fail_closed: usize,
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
#[must_use]
pub(in crate::codegen_ay::chc) fn get_range_spec_next_path_counts() -> RangeSpecNextPathCounts {
    RangeSpecNextPathCounts {
        datatype: GLOBAL_COUNTERS.range_spec_next_datatype_path.load(Ordering::Relaxed) as usize,
        flattened: GLOBAL_COUNTERS.range_spec_next_flattened_path.load(Ordering::Relaxed) as usize,
        fail_closed: GLOBAL_COUNTERS.range_spec_next_fail_closed_path.load(Ordering::Relaxed)
            as usize,
    }
}

/// Extension trait for iterator adapter call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallIteratorAdapter {
    /// `func` is the call's own callee operand (`None` only in unit tests that
    /// have no call): an `Iterator::sum` is classified from it, never by its
    /// destination place, which two sums can share.
    fn codegen_call_iterator_adapter(&mut self, cx: &ChcCallContext<'_>, func: Option<&Operand>);
}

impl ChcCtx<'_, '_> {
    /// Resolve identity before printed-name categories: an adapter can mention
    /// Vec in its generic arguments and otherwise stop at Vec's exclusive route.
    pub(in crate::codegen_ay::chc) fn try_codegen_native_iterator_size_hint(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        if !self.native_iterator_size_hint_call(dcx.func) {
            return false;
        }
        let Some(target) = *dcx.target else { return false };
        let cx = ChcCallContext {
            stub: StubKind::IterSizeHint,
            args: dcx.args,
            destination: dcx.destination,
            target,
            from_app: dcx.from_app,
            stmt_constraints: dcx.stmt_constraints,
            modified_locals: dcx.modified_locals,
        };
        self.codegen_call_iterator_adapter(&cx, Some(dcx.func));
        true
    }

    /// Does this call run closures its stub does not encode, and may one of
    /// them carry an obligation (`iter_closure_obligation`)?
    ///
    /// The `next()` stubs of std's adapters and the `fold`, `sum` and
    /// `collect` stubs never run the closures of their receiver's adapter
    /// chain (a `Filter`'s predicate, a `Map`'s function): the stubs of
    /// constructors (`map`, `filter`, ...) and of `size_hint` run none.
    fn adapter_call_may_run_obligated_closure(&self, stub: StubKind, args: &[Operand]) -> bool {
        let runs_receiver_closures = matches!(
            stub,
            StubKind::MapNext
                | StubKind::FilterNext
                | StubKind::FilterMapNext
                | StubKind::FlattenNext
                | StubKind::ChainNext
                | StubKind::ZipNext
                | StubKind::IterFold
                | StubKind::IterSum
                | StubKind::IterCollect
        );
        if !runs_receiver_closures {
            return false;
        }
        let Some(receiver) = args.first() else {
            return false;
        };
        let Ok(ty) = receiver.ty(self.body.locals()) else {
            return true;
        };
        ty_may_run_obligated_closure(self.tcx, self.resolve_body_ty(ty))
    }

    /// The conservative error rule for a closure the call runs and the stub
    /// does not encode: a freed flag alone, reachable whenever the call is,
    /// never certified Genuine (see `reduce::ReducePanicObligation`).
    fn emit_unmodeled_closure_rule(&mut self, cx: &ChcCallContext<'_>) {
        let flag = self.iter_conservative_flag(
            crate::codegen_ay::chc::codegen_ctx::sound_havoc::ITER_ADAPTER_CLOSURE_UNMODELED,
        );
        self.emit_error_rule_for_condition_with_kind(
            cx.from_app,
            flag.not(),
            cx.stmt_constraints,
            cx.target,
            PropertyKind::Panic,
            Some(UNMODELED_CLOSURE_MESSAGE.to_string()),
        );
    }

    /// The error rules of a sum's panic obligation
    /// ([`reduce::ReducePanicObligation`]): for an integer sum one for the
    /// replayed steps and one for the elements the replay did not check, both
    /// "attempt to add with overflow"; for a `Sum` impl the stub does not
    /// model, or a float sum's NaN check, one conservative rule. The
    /// rule body is the call's pre-state, its statement constraints and the
    /// replay's defining equalities (`acc_k = ...`), which the violation
    /// predicates read.
    fn emit_sum_panic_rules(
        &mut self,
        cx: &ChcCallContext<'_>,
        obligation: reduce::ReducePanicObligation,
        replay_constraints: &[Expr],
    ) {
        let mut body: Vec<Expr> =
            Vec::with_capacity(cx.stmt_constraints.len() + replay_constraints.len());
        body.extend(cx.stmt_constraints.iter().cloned());
        body.extend(replay_constraints.iter().cloned());
        let violations = obligation.exact.into_iter().chain(std::iter::once(obligation.unchecked));
        for violation in violations {
            self.emit_error_rule_for_condition_with_kind(
                cx.from_app,
                violation.not(),
                &body,
                cx.target,
                obligation.kind,
                Some(obligation.message.to_string()),
            );
        }
    }
}

impl<'tcx, 'body> CallIteratorAdapter for ChcCtx<'tcx, 'body> {
    /// Handle iterator adapter stubs in CHC mode (Part of #1751).
    ///
    /// This is intentionally shape-focused:
    /// - `MapNext` / `FilterNext` / `FlattenNext`: preserve Option exhaustion shape.
    /// - `RangeSpecNext`: preserve range progression (`start < end`, `start += 1`).
    /// - `IterFold` / `IterSum`: preserve empty-iterator identities.
    /// - Other adapters: symbolic over-approximation with explicit destination update.
    fn codegen_call_iterator_adapter(&mut self, cx: &ChcCallContext<'_>, func: Option<&Operand>) {
        let stub = cx.stub;
        let args = cx.args;
        let destination = cx.destination;
        let modified_locals = cx.modified_locals;

        // Before any early return: the closures run whatever happens to the
        // destination (AY alignment round 8, review round 5, finding 1).
        if self.adapter_call_may_run_obligated_closure(stub, args) {
            self.emit_unmodeled_closure_rule(cx);
        }

        let dest_local: usize = destination.local;
        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
            debug!(dest_local, "CHC: iterator_adapter dest not in state map — sound over-approx");
            self.record_sound_fallback_reason("state_idx_missing_iterator_adapter_dest");
            let mut fallback_dests = vec![dest_local];
            if let Some((_, Some(iter_local))) =
                self.iterator_receiver_expr_and_local(args, modified_locals)
                && !fallback_dests.contains(&iter_local)
            {
                fallback_dests.push(iter_local);
            }
            let output_args = self.build_output_args(modified_locals, &fallback_dests);
            self.emit_goto_rule(cx.from_app, cx.target, &output_args, cx.stmt_constraints);
            return;
        };

        debug!("iterator_adapter_stub stub={:?} dest={} args={}", stub, dest_local, args.len());
        debug!(?stub, dest_local, dest_vec_idx, "iterator_adapter dispatch (#4112)");

        // Part of #2486: collect extras instead of stmt_constraints.to_vec().
        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();
        let mut result_expr: Option<Expr> = None;
        let mut flattened_result_fields: Option<Vec<Option<Expr>>> = None;
        let mut iter_update: Option<(usize, Expr)> = None;
        let mut iter_flattened_update: Option<(usize, Expr, Expr)> = None;

        match stub {
            StubKind::MapNext
            | StubKind::FilterNext
            | StubKind::FilterMapNext
            | StubKind::FlattenNext
            | StubKind::ChainNext
            | StubKind::ZipNext => {
                let (res, flat, upd, adapter_extra) = self.codegen_adapter_next_arm(
                    stub,
                    args,
                    modified_locals,
                    dest_local,
                    dest_vec_idx,
                );
                result_expr = res;
                flattened_result_fields = flat;
                iter_update = upd;
                extra_constraints.extend(adapter_extra);
            }
            StubKind::RangeIntoIter => {
                let (res, flat) =
                    self.codegen_range_into_iter_arm(args, modified_locals, dest_local);
                result_expr = res;
                flattened_result_fields = flat;
            }
            StubKind::RangeSpecNext => {
                let (res, flat, upd, flat_upd, range_extra) = self.codegen_range_spec_next_arm(
                    args,
                    modified_locals,
                    dest_local,
                    dest_vec_idx,
                );
                result_expr = res;
                flattened_result_fields = flat;
                iter_update = upd;
                iter_flattened_update = flat_upd;
                extra_constraints.extend(range_extra);
            }
            StubKind::IterFold | StubKind::IterSum => {
                let mut panic_obligation = None;
                let mut reduce_checks = Vec::new();
                let (res, flat) = self.codegen_reduce_arm(
                    stub,
                    func,
                    args,
                    modified_locals,
                    destination,
                    dest_vec_idx,
                    &mut extra_constraints,
                    &mut panic_obligation,
                    &mut reduce_checks,
                );
                result_expr = res;
                flattened_result_fields = flat;
                if let Some(obligation) = panic_obligation {
                    self.emit_sum_panic_rules(cx, obligation, &extra_constraints);
                }
                // The reduction's step obligations read the chain's bound
                // accumulators: their error rules carry its constraints.
                if !reduce_checks.is_empty() {
                    let mut body: Vec<Expr> = cx.stmt_constraints.to_vec();
                    body.extend(extra_constraints.iter().cloned());
                    self.emit_deferred_inline_checks_at(
                        cx.from_app,
                        &body,
                        cx.target,
                        reduce_checks,
                    );
                }
            }
            StubKind::IterMap
            | StubKind::IterFilter
            | StubKind::IterFilterMap
            | StubKind::IterFlatten => {
                result_expr = self.codegen_iter_constructor(cx, stub, dest_local, dest_vec_idx);
            }
            StubKind::IterZip => {
                result_expr = self.codegen_iter_zip(cx, dest_local, dest_vec_idx);
            }
            StubKind::IterCollect => {
                result_expr = self.codegen_iter_collect(
                    cx,
                    dest_local,
                    dest_vec_idx,
                    &mut flattened_result_fields,
                    &mut extra_constraints,
                    &mut extra_dests,
                );
            }
            StubKind::IterSizeHint => {
                // Delegated to size_hint.rs — Part of #3348: precise size_hint stub.
                self.codegen_iter_size_hint(
                    func,
                    args,
                    modified_locals,
                    dest_local,
                    dest_vec_idx,
                    &mut result_expr,
                    &mut flattened_result_fields,
                );
                // Falls through to symbolic fallback if precise result couldn't be built
            }
            _other => {} // partial dispatch: StubKind
        }

        if matches!(stub, StubKind::RangeSpecNext)
            && result_expr.is_none()
            && flattened_result_fields.is_none()
        {
            self.diagnostics.range_spec_next_fail_closed_path.inc();
            self.emit_untranslatable_assert_rule(
                cx.from_app,
                cx.stmt_constraints,
                cx.target,
                "RangeSpecNext translation failed",
            );
            return;
        }
        self.emit_adapter_epilogue(
            cx,
            dest_local,
            dest_vec_idx,
            result_expr,
            flattened_result_fields,
            iter_update,
            iter_flattened_update,
            extra_constraints,
            extra_dests,
        );
    }
}
