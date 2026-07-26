// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Collection call handling: HashMap, HashSet, BTreeSet, and iterator intrinsics.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//! Part of #2381: Migrated to ChcCallContext to eliminate too_many_arguments.
//! Part of #2304 S3a: Deduplicated dispatch via `apply_collection_result`.

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

use crate::args::ChcTrackLevel;
use crate::codegen_ay::chc::CollectionCallResult;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::ptr_sort;

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;
use super::stubs_option_helpers::OptionHelpers;
use super::{UnknownProjectionPolicy, collect_field_projections};
use tracing::debug;

/// Extension trait for collection call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallCollections {
    fn codegen_call_hashmap(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_btreeset(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_hashset(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_iterator_intrinsic(&mut self, cx: &ChcCallContext<'_>);
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve args[0] through ref_targets to find the underlying collection local.
    pub(in crate::codegen_ay::chc) fn resolve_collection_local(
        &self,
        args: &[Operand],
    ) -> Option<usize> {
        if let Some(Operand::Copy(place) | Operand::Move(place)) = args.first() {
            let ref_local: usize = place.local;
            Some(self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local))
        } else {
            None
        }
    }

    /// Resolve args[0] through ref_targets and return any field projections.
    ///
    /// When a collection is accessed through a struct field (e.g., `self.indices`),
    /// ref_targets carries projections describing the path from struct to collection.
    /// Part of #3348: needed by VecPush to handle struct-embedded Vecs.
    pub(in crate::codegen_ay::chc) fn resolve_collection_field_projections(
        &self,
        args: &[Operand],
    ) -> Vec<rustc_public::mir::ProjectionElem> {
        if let Some(Operand::Copy(place) | Operand::Move(place)) = args.first() {
            let ref_local: usize = place.local;
            self.ref_resolution
                .ref_targets
                .get(&ref_local)
                .map(|rt| rt.projections.clone())
                .unwrap_or_default()
        } else {
            vec![]
        }
    }

    /// Compute the flat state var index for a struct-embedded collection field.
    ///
    /// Part of #3348: When a collection (HashMap/BTreeMap) is a field of a
    /// flattened struct, this computes the state_var index for the collection's
    /// Array by summing leaf counts of preceding fields.
    ///
    /// Returns the absolute state var index (base + flat_offset).
    fn struct_field_flat_offset(
        &self,
        struct_local: usize,
        field_projs: &[rustc_public::mir::ProjectionElem],
    ) -> Option<usize> {
        use super::codegen_decl_flatten::collect_leaf_sorts;
        use super::codegen_types::CodegenTypes;

        let converted = collect_field_projections(field_projs, UnknownProjectionPolicy::Skip);
        if converted.len() != 1 {
            return None;
        }
        let target_field_idx = converted[0].field_idx;

        let local_ty = self.body.locals().get(struct_local).map(|l| l.ty)?;
        let struct_sort = Self::translate_ty(local_ty)?;
        let dt = struct_sort.datatype_sort()?;
        let cons = dt.constructors.first()?;
        if target_field_idx >= cons.fields.len() {
            return None;
        }

        let struct_base = self.try_state_idx_for_local(struct_local)?;
        let mut flat_offset = 0;
        for f in &cons.fields[..target_field_idx] {
            flat_offset += collect_leaf_sorts(&f.sort, 0).len();
        }
        Some(struct_base + flat_offset)
    }

    /// Get the current length expression for a collection.
    ///
    /// In CHC, each basic block is a separate Horn clause rule. The length
    /// value at block entry always comes from the predecessor relation's input
    /// variable (not the output `__out` variable from a prior block). Always
    /// return the input variable here.
    /// Part of #1739: fixes circular constraints from cross-block is_len_modified.
    pub(in crate::codegen_ay::chc) fn collection_current_len(&self, len_var_name: &str) -> Expr {
        Expr::var(len_var_name, ptr_sort())
    }

    /// Set a collection's tracked length to `new_len`, emitting constraint
    /// and marking modified. Returns true if length var was found.
    pub(in crate::codegen_ay::chc) fn collection_len_set(
        &mut self,
        len_var_name: &str,
        new_len: Expr,
        acc: &mut CallAccumulator<'_>,
    ) -> bool {
        let len_out_name = crate::codegen_ay::names::out_name(len_var_name);
        if let Some(len_idx) = self.output_state_var_index_by_name(&len_out_name) {
            let len_var = Expr::var(&len_out_name, ptr_sort());
            acc.constraints.push(len_var.eq(new_len));
            acc.dests.push(len_idx);
            self.mark_collection_len_modified(len_var_name);
            true
        } else {
            false
        }
    }

    /// Get the current capacity expression for a Vec (pre- or post-modification).
    /// Part of #2877: Vec capacity state variable tracking.
    /// Part of #1739: always use input variable (same rationale as collection_current_len).
    pub(in crate::codegen_ay::chc) fn collection_current_cap(&self, cap_var_name: &str) -> Expr {
        Expr::var(cap_var_name, ptr_sort())
    }

    /// Set a Vec's tracked capacity to `new_cap`, emitting constraint
    /// and marking modified. Returns true if capacity var was found.
    /// Part of #2877.
    pub(in crate::codegen_ay::chc) fn collection_cap_set(
        &mut self,
        cap_var_name: &str,
        new_cap: Expr,
        acc: &mut CallAccumulator<'_>,
    ) -> bool {
        let cap_out_name = crate::codegen_ay::names::out_name(cap_var_name);
        if let Some(cap_idx) = self.output_state_var_index_by_name(&cap_out_name) {
            let cap_var = Expr::var(&cap_out_name, ptr_sort());
            acc.constraints.push(cap_var.eq(new_cap));
            acc.dests.push(cap_idx);
            self.mark_collection_cap_modified(cap_var_name);
            true
        } else {
            false
        }
    }

    /// Set a HashMap's tracked presence-array to `new_present`, emitting constraint
    /// and marking modified. Returns true if present var was found.
    /// Part of #3057: DT-free parallel-array encoding.
    pub(in crate::codegen_ay::chc) fn collection_present_set(
        &mut self,
        present_var_name: &str,
        new_present: Expr,
        acc: &mut CallAccumulator<'_>,
    ) -> bool {
        let present_out_name = crate::codegen_ay::names::out_name(present_var_name);
        if let Some(present_idx) = self.output_state_var_index_by_name(&present_out_name) {
            let present_sort = new_present.sort().clone();
            let present_var = Expr::var(&present_out_name, present_sort);
            acc.constraints.push(present_var.eq(new_present));
            acc.dests.push(present_idx);
            self.mark_collection_present_modified(present_var_name);
            true
        } else {
            false
        }
    }

    /// Process a `CollectionCallResult`: map_update, len_update, result, constraints.
    ///
    /// Shared pipeline for all collection types (Part of #2304 S3a). The only
    /// per-type difference is whether `result` handling needs flattened-Option
    /// decomposition (HashMap returns `Option<V>`; sets return `Bool`). This is
    /// gated on `result_expr.sort().is_datatype()`, which naturally skips it for
    /// Bool results.
    fn apply_collection_result(
        &mut self,
        cx: &ChcCallContext<'_>,
        result: CollectionCallResult,
        caller_label: &'static str,
    ) {
        if result.force_error {
            self.emit_untranslatable_assert_rule(
                cx.from_app,
                cx.stmt_constraints,
                cx.target,
                "Collection stub requested fail-closed error",
            );
            return;
        }

        let dest_local: usize = cx.destination.local;
        let mut dest_vec_idx = self.try_state_idx_for_local(dest_local);

        // Part of #4099: Late-binding fallback for collection call destinations
        // missing from local_to_state_idx. When FunctionInlinePass renumbers MIR
        // locals, the destination index may not match the declaration-phase mapping.
        // Attempt name-based lookup and repair the mapping so the result is written
        // to the correct state var instead of being silently dropped.
        if dest_vec_idx.is_none() {
            let canonical_name =
                crate::codegen_ay::names::state_var_name(&self.fn_name, dest_local);
            if let Some(idx) = self.state_var_index_by_name(&canonical_name) {
                debug!(dest_local, idx, "CHC: collections dest late-bound via name lookup (#4099)");
                self.state_var_mgr.local_to_state_idx.insert(dest_local, idx);
                dest_vec_idx = Some(idx);
            } else {
                debug!(dest_local, "CHC: collections dest not in state map — sound over-approx");
                self.record_sound_fallback_reason("state_idx_missing_collections_dest");
            }
        }
        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();

        // Step 1: map_update — resolve ref_targets, push coerced eq constraint.
        if let Some(new_collection) = result.map_update
            && let Some(collection_local) = self.resolve_collection_local(cx.args)
        {
            let field_projs = self.resolve_collection_field_projections(cx.args);
            if let Some(idx) = self.try_state_idx_for_local(collection_local) {
                if let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(idx).cloned()
                {
                    let var = Expr::var(&*out_name, out_sort.clone());

                    // Part of #3348: Struct-embedded map update.
                    // When the collection is accessed through a struct field projection,
                    // the state var is a Datatype (not Array). Navigate projections to
                    // find the collection field, update it, then reconstruct the struct.
                    if !field_projs.is_empty() && out_sort.datatype_name().is_some() {
                        let converted =
                            collect_field_projections(&field_projs, UnknownProjectionPolicy::Skip);
                        if !converted.is_empty() {
                            let (in_name, in_sort) = self
                                .state_var_mgr
                                .state_vars
                                .get(idx)
                                .cloned()
                                .unwrap_or_else(|| (out_name.clone(), out_sort.clone()));
                            let struct_in = Expr::var(&*in_name, in_sort);
                            if let Some(new_struct) = Self::apply_projection_update(
                                &struct_in,
                                &converted,
                                new_collection,
                            ) {
                                extra_constraints.push(var.eq(new_struct));
                                self.mark_state_var_modified(idx);
                                debug!(
                                    collection_local,
                                    "CHC: struct-embedded map_update via Datatype projection update (#3348)"
                                );
                            }
                        }
                    }
                    // Part of #3348: Struct-embedded flattened map update.
                    // When the struct is flattened, compute the flat leaf offset and
                    // directly constrain the Array state var at that offset.
                    else if !field_projs.is_empty() && !out_sort.is_array() {
                        if let Some(flat_idx) =
                            self.struct_field_flat_offset(collection_local, &field_projs)
                        {
                            if let Some((flat_out_name, flat_out_sort)) =
                                self.state_var_mgr.output_state_vars.get(flat_idx).cloned()
                            {
                                let flat_var = Expr::var(&*flat_out_name, flat_out_sort.clone());
                                self.push_coerced_eq_constraint(
                                    &mut extra_constraints,
                                    &flat_var,
                                    new_collection,
                                    &flat_out_sort,
                                    collection_local,
                                    caller_label,
                                );
                                self.mark_state_var_modified(flat_idx);
                                debug!(
                                    collection_local,
                                    flat_idx,
                                    "CHC: struct-embedded map_update via flattened offset (#3348)"
                                );
                            }
                        }
                    }
                    // Direct collection state var (not struct-embedded).
                    else {
                        self.push_coerced_eq_constraint(
                            &mut extra_constraints,
                            &var,
                            new_collection,
                            &out_sort,
                            collection_local,
                            caller_label,
                        );
                        // Part of #3348: Use mark_state_var_modified instead of
                        // extra_dests.push(idx). `idx` is a vec_idx from
                        // state_idx_for_local, but build_output_args treats
                        // extra_dests entries as MIR local indices via
                        // try_state_idx_for_local. This mismatch caused the
                        // collection data array to be silently skipped, so
                        // the transition rule passed the pre-update input var
                        // to the successor block instead of the post-update
                        // output var, making the store constraint dead code.
                        self.mark_state_var_modified(idx);
                    }
                }
            } else {
                debug!(
                    collection_local,
                    "CHC: collection_local not in state map — skip map_update"
                );
                self.record_sound_fallback_reason("state_idx_missing_collection_local");
            }
        }

        // Part of #3348: Extract resolved and raw locals from args[0] for
        // multi-level auxiliary var resolution. `resolved_cl` follows ref_targets;
        // `raw_cl` is the direct operand local (may be a &mut Collection with its
        // own registered auxiliary vars via detect_collection_type's Ref unwrap).
        let (resolved_cl, raw_cl) =
            if let Some(Operand::Copy(place) | Operand::Move(place)) = cx.args.first() {
                let raw = place.local;
                let resolved = self.ref_resolution.ref_targets.get(&raw).map_or(raw, |rt| rt.local);
                (Some(resolved), Some(raw))
            } else {
                (None, None)
            };

        // Step 2: len_update — shared across all collection types (Part of #1814).
        // Part of #3348: When aux_targets_dest, target destination (clone/new).
        // Otherwise use source with multi-level fallback (insert/remove).
        if let Some(len_update_expr) = result.len_update {
            let len_var_name = if result.aux_targets_dest {
                self.collections.len_state.get_len_var(dest_local).cloned()
            } else {
                resolved_cl
                    .and_then(|cl| self.collections.len_state.get_len_var(cl).cloned())
                    .or_else(|| {
                        raw_cl.and_then(|l| self.collections.len_state.get_len_var(l).cloned())
                    })
                    .or_else(|| self.collections.len_state.get_len_var(dest_local).cloned())
            };
            if let Some(len_var_name) = len_var_name {
                self.collection_len_set(
                    &len_var_name,
                    len_update_expr,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
        }

        // Step 2.5: present_update — HashMap DT-free encoding (Part of #3057).
        // Part of #3348: When aux_targets_dest, target destination (clone/new).
        // Otherwise use multi-level fallback mirroring get_hashmap_present_arg:
        // resolved_cl → raw_cl → dest_local.
        if let Some(present_update_expr) = result.present_update {
            let present_var_name = if result.aux_targets_dest {
                self.collections.len_state.get_present_var(dest_local).cloned()
            } else {
                resolved_cl
                    .and_then(|cl| self.collections.len_state.get_present_var(cl).cloned())
                    .or_else(|| {
                        raw_cl.and_then(|l| self.collections.len_state.get_present_var(l).cloned())
                    })
                    .or_else(|| self.collections.len_state.get_present_var(dest_local).cloned())
            };
            if let Some(present_var_name) = present_var_name {
                self.collection_present_set(
                    &present_var_name,
                    present_update_expr,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
        }

        // Step 3: result — store to destination (with flattened-Option handling).
        if let Some(result_expr) = result.result {
            if dest_vec_idx.is_none() {
                debug!(
                    dest_local,
                    "CHC: collections result dest not in state map — skipping precise result"
                );
            } else if let Some(dest_vec_idx) = dest_vec_idx {
                // Part of #3057: DT-free flattened Option result. When `result_is_some`
                // is provided, write (fld0=is_some, fld1=result) directly, bypassing
                // DT Option decomposition. This avoids constructing any Datatype expr.
                if let Some(is_some_expr) = result.result_is_some
                    && self.flatten.flattened_tuple_locals.contains(&dest_local)
                {
                    let mut field_values = vec![Some(is_some_expr), Some(result_expr)];

                    // Part of #3270: Value-to-reference promotion for Option<&V>.
                    // Collection stubs return raw V; promote to virtual &V pointer.
                    let fld1_idx = dest_vec_idx + 1;
                    self.promote_value_to_ref(
                        dest_local,
                        fld1_idx,
                        &mut field_values,
                        &mut extra_constraints,
                    );

                    while field_values.len() < self.flattened_field_count(dest_local) {
                        field_values.push(None);
                    }
                    self.constrain_flattened_fields_for_call(
                        dest_local,
                        &field_values,
                        &mut extra_constraints,
                    );
                    extra_dests.push(dest_local);
                }
                // Part of #2380: flattened Option<T> destinations use scalar fld0/fld1 slots.
                else if self.flatten.flattened_tuple_locals.contains(&dest_local)
                    && result_expr.sort().is_datatype()
                {
                    let mut field_values = vec![
                        Some(self.option_is_some(result_expr.clone())),
                        self.option_unwrap_value_on_some_path(result_expr),
                    ];
                    while field_values.len() < self.flattened_field_count(dest_local) {
                        field_values.push(None);
                    }
                    self.constrain_flattened_fields_for_call(
                        dest_local,
                        &field_values,
                        &mut extra_constraints,
                    );
                    extra_dests.push(dest_local);
                } else if let Some((out_name, _out_sort)) =
                    self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
                {
                    let actual_sort = result_expr.sort().clone();
                    let dest_var = Expr::var(&*out_name, actual_sort.clone());
                    self.push_coerced_eq_constraint(
                        &mut extra_constraints,
                        &dest_var,
                        result_expr,
                        &actual_sort,
                        dest_local,
                        caller_label,
                    );
                    extra_dests.push(dest_local);

                    // Part of #1812: Update state variable sorts to match stub result.
                    if self.state_var_mgr.state_vars.get(dest_vec_idx).is_some() {
                        self.state_var_mgr.state_vars[dest_vec_idx].1 = actual_sort.clone();
                    }
                    self.state_var_mgr.output_state_vars[dest_vec_idx] = (out_name, actual_sort);
                }
            }
        }

        // Step 4: soundness constraints from stub result (Part of #1813).
        extra_constraints.extend(result.constraints);

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

impl<'tcx, 'body> CallCollections for ChcCtx<'tcx, 'body> {
    /// Handle HashMap stub calls (Part of #788 Phase 5).
    fn codegen_call_hashmap(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        if let Some(result) =
            self.translate_hashmap_call(cx.stub, cx.args, cx.modified_locals, Some(dest_local))
        {
            self.apply_collection_result(cx, result, "codegen_call_hashmap");
        } else {
            self.emit_untranslatable_assert_rule(
                cx.from_app,
                cx.stmt_constraints,
                cx.target,
                "HashMap stub translation failed",
            );
        }
    }

    /// Handle BTreeSet stub calls (Part of #1659).
    fn codegen_call_btreeset(&mut self, cx: &ChcCallContext<'_>) {
        debug!("btreeset_stub {:?} detected", cx.stub);
        let dest_local: usize = cx.destination.local;
        if let Some(result) =
            self.translate_btreeset_call(cx.stub, cx.args, cx.modified_locals, Some(dest_local))
        {
            self.apply_collection_result(cx, result, "codegen_call_btreeset");
        } else {
            self.emit_untranslatable_assert_rule(
                cx.from_app,
                cx.stmt_constraints,
                cx.target,
                "BTreeSet stub translation failed",
            );
        }
    }

    /// Handle HashSet stub calls (Part of #1751).
    fn codegen_call_hashset(&mut self, cx: &ChcCallContext<'_>) {
        debug!("hashset_stub {:?} detected", cx.stub);
        let dest_local: usize = cx.destination.local;
        if let Some(result) =
            self.translate_hashset_call(cx.stub, cx.args, cx.modified_locals, Some(dest_local))
        {
            self.apply_collection_result(cx, result, "codegen_call_hashset");
        } else {
            self.emit_untranslatable_assert_rule(
                cx.from_app,
                cx.stmt_constraints,
                cx.target,
                "HashSet stub translation failed",
            );
        }
    }

    /// Handle iterator intrinsic stubs (Part of #1712).
    fn codegen_call_iterator_intrinsic(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        debug!("iterator_intrinsic stub={:?} has_target=true dest={}", cx.stub, dest_local);
        // Part of #3914 / #4163: unwrap_unchecked shares the same payload seam
        // as unwrap/expect, so preserve the full ref metadata bundle here too.
        if matches!(cx.stub, StubKind::OptionUnwrapUnchecked) && !cx.args.is_empty() {
            super::codegen_call_option_result::propagate_unwrapped_ref_metadata_from_operand(
                self,
                &cx.args[0],
                dest_local,
            );
        }
        if let Some(result_expr) = self.translate_iterator_intrinsic_call(
            cx.stub,
            cx.args,
            cx.modified_locals,
            Some(dest_local),
        ) {
            if self.flatten.flattened_tuple_locals.contains(&dest_local) {
                if !matches!(cx.stub, StubKind::CheckedAddUnsigned) {
                    // Flattened tuple non-CheckedAddUnsigned — unsupported (Part of #3123).
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

                // Part of #1739: CheckedAddUnsigned for flattened Option<T> writes
                // two scalar fields: fld0=is_some(true), fld1=payload(bvadd result).
                let mut extra_constraints: Vec<Expr> = Vec::new();
                self.constrain_flattened_fields_for_call(
                    dest_local,
                    &[Some(Expr::bool_const(true)), Some(result_expr)],
                    &mut extra_constraints,
                );
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

            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    result_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_iterator_intrinsic",
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
                // resolve_destination failed — iterator result unconstrained (Part of #3123).
                emit_sound_fallback_goto(
                    self,
                    cx.from_app,
                    cx.target,
                    cx.modified_locals,
                    &[dest_local],
                    cx.stmt_constraints,
                );
            }
        } else {
            self.emit_untranslatable_assert_rule(
                cx.from_app,
                cx.stmt_constraints,
                cx.target,
                "Iterator intrinsic stub translation failed",
            );
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #3270: Promote raw V in Option fld1 to virtual &V pointer,
    /// storing to typed memory so inlined PartialEq can read through mem_ref_<T>.
    fn promote_value_to_ref(
        &mut self,
        dest_local: usize,
        fld1_idx: usize,
        field_values: &mut [Option<Expr>],
        extra_constraints: &mut Vec<Expr>,
    ) {
        if self.track_level < ChcTrackLevel::Mem {
            return;
        }
        let Some(ref value_expr) = field_values[1] else { return };
        let fld1_is_ptr = self
            .state_var_mgr
            .output_state_vars
            .get(fld1_idx)
            .map_or(false, |(_, s)| *s == ptr_sort());
        if !fld1_is_ptr || *value_expr.sort() == ptr_sort() {
            return;
        }
        let dest_ty = self.body.locals()[dest_local].ty;
        let Some((pointee_ty, ref_ty)) = extract_option_ref_types(dest_ty) else { return };
        let Some(obj_id) = self.heap_state.next_alloc_id() else { return };

        let obj_id_expr = Expr::bitvec_const(obj_id as i128, 32);
        let addr = obj_id_expr.clone().concat(Expr::bitvec_const(0, 32));

        if !self.int_lift {
            let obj_valid = self.current_obj_valid_array();
            extra_constraints.push(obj_valid.select(obj_id_expr).eq(Expr::bool_const(true)));
            // Part of #3436: track that this block reads heap metadata.
            self.mark_heap_metadata_read();
        }

        if let Some(c) = self.build_memory_store(addr.clone(), value_expr.clone(), pointee_ty) {
            extra_constraints.push(c);
        }
        extra_constraints.append(&mut self.heap_state.pending_updates);
        extra_constraints.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
        self.heap_state.pending_checks.clear();
        // Part of #3348: Register pre-promotion raw value for Option::copied().
        // When copied() is called on this local, it can use the raw value directly
        // instead of dereferencing through typed memory.
        self.ref_resolution.promoted_raw_values.insert(dest_local, value_expr.clone());

        field_values[1] = Some(addr.clone());

        if let Some(dest_addr) = self.get_or_create_local_address(dest_local) {
            if let Some(c) = self.build_memory_store(dest_addr, addr, ref_ty) {
                extra_constraints.push(c);
            }
            extra_constraints.append(&mut self.heap_state.pending_updates);
            extra_constraints.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
            self.heap_state.pending_checks.clear();
        }
        debug!(fn_name = %self.fn_name, dest_local, obj_id, "value-to-ref promotion (#3270)");
    }
}

/// Extract `(V, &V)` from `Option<&V>`, or `None` if not a ref-Option. Part of #3270.
fn extract_option_ref_types(
    ty: rustc_public::ty::Ty,
) -> Option<(rustc_public::ty::Ty, rustc_public::ty::Ty)> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Option" => {
            let inner_ty = match args.0.first() {
                Some(GenericArgKind::Type(ty)) => *ty,
                _ => return None,
            };
            match inner_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some((pointee, inner_ty)),
                _ => None,
            }
        }
        _ => None,
    }
}
