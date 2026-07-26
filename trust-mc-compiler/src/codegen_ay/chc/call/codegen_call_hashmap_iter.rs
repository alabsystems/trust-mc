// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Collection iterator call handling (HashMap, HashSet).
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//! Part of #3057: shared handler for HashMap and HashSet iterators.

use ay_bindings::Expr;
use rustc_public::mir::Operand;

use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;
use super::{ChcCtx, chc_debug_enabled};
use crate::codegen_ay::chc::CollectionCallResult;
use tracing::debug;

/// Extension trait for collection iterator call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallHashmapIter {
    fn codegen_call_hashmap_iter(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_hashset_iter(&mut self, cx: &ChcCallContext<'_>);
}

impl<'tcx, 'body> CallHashmapIter for ChcCtx<'tcx, 'body> {
    /// Handle HashMap iterator stub calls (Part of #1812).
    fn codegen_call_hashmap_iter(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        debug!("hashmap_iter_stub stub={:?} dest={}", cx.stub, dest_local);
        if let Some(Operand::Copy(place) | Operand::Move(place)) = cx.args.first()
            && place.projection.is_empty()
        {
            let ref_local = place.local;
            let iter_local =
                self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local);
            if self.try_state_idx_for_local(iter_local).is_none() {
                debug!(
                    iter_local,
                    "CHC: hashmap_iter receiver not in state map — sound over-approx"
                );
                self.record_sound_fallback_reason("state_idx_missing_hashmap_iter");
                emit_sound_fallback_goto(
                    self,
                    cx.from_app,
                    cx.target,
                    cx.modified_locals,
                    &[dest_local],
                    cx.stmt_constraints,
                );
                return;
            }
        }
        if let Some(result) =
            self.translate_hashmap_iter_call(cx.stub, cx.args, cx.modified_locals, Some(dest_local))
        {
            self.apply_collection_iter_result(cx, result);
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
    }

    /// Handle HashSet iterator stub calls (Part of #3057).
    ///
    /// Routes HashSet iterator operations through the same projection-aware
    /// result application as HashMap iterators. Without this, HashSet iterator
    /// struct results are incorrectly treated as Option types in the generic
    /// apply_collection_result handler, causing sort mismatches that produce
    /// UNKNOWN verdicts for all HashSet iteration harnesses.
    fn codegen_call_hashset_iter(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        debug!("hashset_iter_stub stub={:?} dest={}", cx.stub, dest_local);
        if let Some(result) =
            self.translate_hashset_call(cx.stub, cx.args, cx.modified_locals, Some(dest_local))
        {
            self.apply_collection_iter_result(cx, result);
        } else {
            self.emit_untranslatable_assert_rule(
                cx.from_app,
                cx.stmt_constraints,
                cx.target,
                "HashSet iter stub translation failed",
            );
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Shared result application for collection iterator calls (Part of #3057).
    ///
    /// Handles projection-aware decomposition for both HashMap and HashSet
    /// iterator stubs. This is the logic that was previously only in
    /// `codegen_call_hashmap_iter` — extracting it lets HashSet iterators
    /// reuse the same flattened-field handling that avoids DT+BV sort mismatches.
    fn apply_collection_iter_result(
        &mut self,
        cx: &ChcCallContext<'_>,
        result: CollectionCallResult,
    ) {
        if result.force_error {
            self.emit_untranslatable_assert_rule(
                cx.from_app,
                cx.stmt_constraints,
                cx.target,
                "Collection iter stub requested fail-closed error",
            );
            return;
        }

        let dest_local: usize = cx.destination.local;
        let map_update = result.map_update;
        let translated_result = result.result;
        let result_is_some = result.result_is_some;
        let result_fields = result.result_fields;
        let translated_constraints = result.constraints;
        // Part of #2486: collect extras instead of stmt_constraints.to_vec().
        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();

        if let Some(new_iter) = map_update
            && !cx.args.is_empty()
            && let Operand::Copy(place) | Operand::Move(place) = &cx.args[0]
        {
            let ref_local: usize = place.local;
            let iter_local =
                self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local);
            if let Some(iter_vec_idx) = self.try_state_idx_for_local(iter_local) {
                // Part of #2874 Step 3: When the iter local is projected,
                // decompose the updated Datatype back into flattened fields.
                if let Some(kind) = self.collections.projection_locals.get(&iter_local).copied()
                    && let Some(field_values) =
                        self.decompose_projected_iterator_to_fields(&new_iter, kind)
                {
                    if self.constrain_flattened_fields_for_call(
                        iter_local,
                        &field_values,
                        &mut extra_constraints,
                    ) {
                        extra_dests.push(iter_local);
                    } else {
                        self.record_sound_fallback_reason("flattened_fields_unconstrained");
                    }
                    debug!(
                        iter_local,
                        ?kind,
                        num_fields = field_values.len(),
                        "hashmap_iter: decomposed projected iterator update (#2874)"
                    );
                } else if let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(iter_vec_idx).cloned()
                {
                    // Non-projected (Datatype) path: single constraint.
                    // Part of #2244: use declared out_sort and coerce_eq_constraint
                    let iter_var = Expr::var(&*out_name, out_sort.clone());
                    if let Some(eq) = self.make_coerced_eq_constraint(
                        &iter_var,
                        new_iter,
                        &out_sort,
                        iter_local,
                        "codegen_call_hashmap_iter::iter_update",
                    ) {
                        extra_constraints.push(eq);
                    }
                    extra_dests.push(iter_local);
                } else if chc_debug_enabled() {
                    debug!(
                        "HashMap iter state update skipped - no output_state_var for local {}",
                        iter_local
                    );
                }
            } else {
                debug!(iter_local, "CHC: hashmap_iter iter not in state map — sound over-approx");
                self.record_sound_fallback_reason("state_idx_missing_hashmap_iter");
                if !extra_dests.contains(&dest_local) {
                    extra_dests.push(dest_local);
                }
            }
        }

        if let Some(result_expr) = translated_result {
            // Part of #3057: DT-free — when result_is_some is provided and
            // destination is flattened, write (is_some, fields...) directly
            // without constructing any Option Datatype. This eliminates DT+BV
            // theory combination from iterator next() CHC constraints.
            if let Some(is_some_expr) = result_is_some
                && self.flatten.flattened_tuple_locals.contains(&dest_local)
            {
                let mut field_values: Vec<Option<Expr>> = vec![Some(is_some_expr)];

                // Part of #3057: use result_fields directly when available.
                // This avoids constructing intermediate tuple Datatype that
                // triggers ay#1766 (DT+BV theory combination).
                if let Some(fields) = result_fields {
                    for field in fields {
                        field_values.push(Some(field));
                    }
                } else {
                    // Fallback: decompose DT tuple into fields.
                    let result_sort = result_expr.sort();
                    if let Some(dt) = result_sort.datatype_sort() {
                        if let Some(ctor) = dt.constructors.first() {
                            for field in &ctor.fields {
                                field_values.push(Some(result_expr.clone().field_select(
                                    &dt.name,
                                    &field.name,
                                    field.sort.clone(),
                                )));
                            }
                        }
                    }
                }
                // If inner type is scalar (not a struct), use as single value.
                if field_values.len() == 1 {
                    field_values.push(Some(result_expr));
                }

                while field_values.len() < self.flattened_field_count(dest_local) {
                    field_values.push(None);
                }
                self.constrain_flattened_fields_for_call(
                    dest_local,
                    &field_values,
                    &mut extra_constraints,
                );
                extra_dests.push(dest_local);
                debug!(
                    dest_local,
                    num_fields = field_values.len(),
                    "hashmap_iter: DT-free flattened fields (#3057)"
                );
            }
            // Part of #3057: into_iter() returns an iterator struct to a projected
            // destination. Decompose into flattened fields instead of direct assign.
            else if let Some(kind) = self.collections.projection_locals.get(&dest_local).copied()
                && result_expr.sort().is_datatype()
                && let Some(field_values) =
                    self.decompose_projected_iterator_to_fields(&result_expr, kind)
            {
                self.constrain_flattened_fields_for_call(
                    dest_local,
                    &field_values,
                    &mut extra_constraints,
                );
                extra_dests.push(dest_local);
                debug!(
                    dest_local,
                    ?kind,
                    num_fields = field_values.len(),
                    "collection_iter: decomposed projected into_iter result (#3057)"
                );
            } else if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                if let Some(eq) = self.make_coerced_eq_constraint(
                    &dest_var,
                    result_expr,
                    dest_var.sort(),
                    dest_local,
                    "apply_collection_iter_result",
                ) {
                    extra_constraints.push(eq);
                }
                extra_dests.push(dest_local);
            } else if chc_debug_enabled() {
                debug!(
                    "Collection iter result storage skipped - no output_state_var for dest {}",
                    dest_local
                );
            }
        }

        extra_constraints.extend(translated_constraints);

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
