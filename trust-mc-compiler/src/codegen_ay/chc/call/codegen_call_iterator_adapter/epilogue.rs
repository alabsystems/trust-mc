// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared adapter epilogue: result constraint emission and goto rule.
//!
//! Extracted from `codegen_call_iterator_adapter` per #4129 (500 LOC threshold).

use ay_bindings::Expr;
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto_extra};
use super::super::codegen_rules::CodegenRules;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Emit result constraints and the terminating goto rule for adapter dispatch.
    pub(in crate::codegen_ay::chc) fn emit_adapter_epilogue(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        dest_vec_idx: usize,
        mut result_expr: Option<Expr>,
        flattened_result_fields: Option<Vec<Option<Expr>>>,
        iter_update: Option<(usize, Expr)>,
        iter_flattened_update: Option<(usize, Expr, Expr)>,
        mut extra_constraints: Vec<Expr>,
        mut extra_dests: Vec<usize>,
    ) {
        // Fallback for adapter families we still over-approximate:
        // assign a symbolic destination instead of preserving the input value.
        if result_expr.is_none()
            && flattened_result_fields.is_none()
            && let Some((_, out_sort)) =
                self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
        {
            // Part of #3189: When the adapter struct is opaque (BV64) but sidecar
            // data (adapter_source_data with concrete_elems, or adapter_remaining_len)
            // was successfully propagated, the semantic information IS preserved
            // for downstream IterCollect. The iterator struct representation is
            // symbolic, but the data flows through the sidecar maps — not a
            // genuine translation drop.
            let has_sidecar_data = self
                .collections
                .adapter_source_data
                .get(&dest_local)
                .is_some_and(|src| src.concrete_elems.is_some() || !src.data_arrays.is_empty())
                || self.collections.adapter_remaining_len.contains_key(&dest_local);
            if !has_sidecar_data {
                self.record_sound_fallback_reason("iter_adapter_no_sidecar");
            }
            result_expr = Some(self.fresh_adapter_symbol("iter_adapter_result", out_sort));
        }

        if let Some((iter_local, iter_start, iter_end)) = iter_flattened_update {
            self.collections.adapter_at_start.remove(&iter_local);
            let mut iter_values = vec![Some(iter_start), Some(iter_end)];
            for field_idx in 2..self.flattened_field_count(iter_local) {
                iter_values.push(self.flattened_local_field_expr(
                    iter_local,
                    field_idx,
                    cx.modified_locals,
                ));
            }
            if self.constrain_flattened_fields_for_call(
                iter_local,
                &iter_values,
                &mut extra_constraints,
            ) {
                extra_dests.push(iter_local);
            } else {
                self.record_sound_fallback_reason("flattened_fields_unconstrained");
            }
        } else if let Some((iter_local, new_iter)) = iter_update {
            self.collections.adapter_at_start.remove(&iter_local);
            debug!(
                "[4112-DIAG] epilogue: iter_update local={iter_local} sort={:?}",
                new_iter.sort()
            );
            let resolve_test = self.resolve_destination(iter_local);
            debug!(
                "[4112-DIAG] epilogue: resolve_destination({iter_local}) = {:?}",
                resolve_test.as_ref().map(|(idx, v)| (idx, v.sort()))
            );
            let proj_test = self.collections.projection_locals.get(&iter_local);
            debug!("[4112-DIAG] epilogue: projection_locals[{iter_local}] = {proj_test:?}");
            debug!(iter_local, new_iter_sort = ?new_iter.sort(), "epilogue: iter_update (#4112)");
            // Part of #2874 Step 3: When the iterator local is a projected
            // collection/iterator, decompose the updated Datatype value back
            // into flattened field expressions. Writing a whole Datatype to a
            // scalar output slot causes a sort mismatch.
            if let Some(kind) = self.collections.projection_locals.get(&iter_local).copied()
                && let Some(field_values) =
                    self.decompose_projected_iterator_to_fields(&new_iter, kind)
            {
                if !self.constrain_flattened_fields_for_call(
                    iter_local,
                    &field_values,
                    &mut extra_constraints,
                ) {
                    self.record_sound_fallback_reason("flattened_fields_unconstrained");
                }
                debug!(
                    iter_local,
                    ?kind,
                    num_fields = field_values.len(),
                    "iterator_adapter: decomposed projected iterator update to flattened fields (#2874)"
                );
            } else if let Some((_, iter_var)) = self.resolve_destination(iter_local) {
                debug!(iter_local, iter_var_sort = ?iter_var.sort(), "epilogue: resolve_destination (#4112)");
                self.push_coerced_eq_constraint(
                    &mut extra_constraints,
                    &iter_var,
                    new_iter,
                    iter_var.sort(),
                    iter_local,
                    "codegen_call_iterator_adapter::iter_update",
                );
            }
            // Keep soundness when we cannot encode iterator state update.
            extra_dests.push(iter_local);
        }

        extra_dests.push(dest_local);
        if let Some(ref field_values) = flattened_result_fields {
            debug!(
                dest_local,
                count = field_values.len(),
                "epilogue: flattened_result_fields (#4112)"
            );
        }
        if let Some(field_values) = flattened_result_fields {
            if self.constrain_flattened_fields_for_call(
                dest_local,
                &field_values,
                &mut extra_constraints,
            ) {
                extra_dests.push(dest_local);
            } else {
                self.record_sound_fallback_reason("flattened_fields_unconstrained");
            }
        } else if let Some(result) = result_expr
            && let Some((_, dest_var)) = self.resolve_destination(dest_local)
        {
            self.push_coerced_eq_constraint(
                &mut extra_constraints,
                &dest_var,
                result,
                dest_var.sort(),
                dest_local,
                "codegen_call_iterator_adapter",
            );
        } else {
            // Coercion/modeling failed — destination is unconstrained.
            emit_sound_fallback_goto_extra(
                self,
                cx.from_app,
                cx.target,
                cx.modified_locals,
                &extra_dests,
                cx.stmt_constraints,
                extra_constraints,
            );
            return;
        }

        // Part of #4112: Ensure iterator and destination state variables are live
        // at the target block. Stub-intercepted calls produce constraints referencing
        // state variables that the static liveness analysis may have pruned from the
        // target block's relation (the MIR call goes through a reference, not a direct
        // local use). Without this, the constraint is emitted but silently dropped
        // during project_full_output_to_block.
        for &local in &extra_dests {
            self.ensure_local_live_at_block(local, cx.target);
        }

        let new_output_args = self.build_output_args(cx.modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            extra_constraints,
        );
    }
}
