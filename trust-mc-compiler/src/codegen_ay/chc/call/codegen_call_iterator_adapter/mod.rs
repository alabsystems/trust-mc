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
//! - `size_hint`: IterSizeHint dispatch (remaining, Some(remaining))

mod collect;
mod collect_data;
mod concrete_eval;
mod constructor;
mod epilogue;
mod helpers;
mod next;
mod range;
mod reduce;
mod size_hint;
mod zip;

use ay_bindings::Expr;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use std::sync::atomic::Ordering;

use crate::codegen_ay::stubs::StubKind;

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
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
    fn codegen_call_iterator_adapter(&mut self, cx: &ChcCallContext<'_>);
}

impl<'tcx, 'body> CallIteratorAdapter for ChcCtx<'tcx, 'body> {
    /// Handle iterator adapter stubs in CHC mode (Part of #1751).
    ///
    /// This is intentionally shape-focused:
    /// - `MapNext` / `FilterNext` / `FlattenNext`: preserve Option exhaustion shape.
    /// - `RangeSpecNext`: preserve range progression (`start < end`, `start += 1`).
    /// - `IterFold` / `IterSum`: preserve empty-iterator identities.
    /// - Other adapters: symbolic over-approximation with explicit destination update.
    fn codegen_call_iterator_adapter(&mut self, cx: &ChcCallContext<'_>) {
        let stub = cx.stub;
        let args = cx.args;
        let destination = cx.destination;
        let modified_locals = cx.modified_locals;

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
                let (res, flat) =
                    self.codegen_reduce_arm(stub, args, modified_locals, dest_local, dest_vec_idx);
                result_expr = res;
                flattened_result_fields = flat;
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
