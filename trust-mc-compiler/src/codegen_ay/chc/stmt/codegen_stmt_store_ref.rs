// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Reg-level deref store via ref_targets for CHC block statement encoding.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//!
//! Contains:
//! - `handle_deref_store_via_ref_targets`: `*ref = value` at Reg level via ref_targets (#1957)
//! - `handle_deref_store_array_via_ref_targets`: array element case for ref_target stores

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use tracing::{debug, warn};

use super::codegen_call_coerce::coerce_eq_constraint;
use super::codegen_ctx::diagnostics::CellCounter;
use super::stmt_accumulator::StmtAccumulator;
use super::{ChcCtx, FieldProjection, UnknownProjectionPolicy, collect_field_projections};

/// Extension trait for ref_target-based deref store handlers.
pub(crate) trait StmtStoreRef {
    /// Handles Deref store at Reg level via ref_targets (#1957).
    fn handle_deref_store_via_ref_targets(
        &mut self,
        lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool;

    /// Handles array element store via ref_targets (#1957).
    fn handle_deref_store_array_via_ref_targets(
        &mut self,
        rhs_expr: Expr,
        ref_local: usize,
        ref_target: &super::RefTarget,
        index_proj: &ProjectionElem,
        field_projs: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool;

    /// Handles array element store through arg-ref pointee (#2750).
    fn handle_deref_store_array_arg_ref(
        &mut self,
        rhs_expr: Expr,
        local_idx: usize,
        pointee_vec_idx: usize,
        index_proj: &ProjectionElem,
        field_projs: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool;
}

impl<'tcx, 'body> StmtStoreRef for ChcCtx<'tcx, 'body> {
    fn handle_deref_store_via_ref_targets(
        &mut self,
        lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        if lhs.projection.is_empty() || !matches!(lhs.projection[0], ProjectionElem::Deref) {
            return false;
        }
        // FC-06: register-promoted deref stores bypass build_memory_store, so
        // the modifies frame-condition check must fire here as well.
        self.modifies_frame_ref_store_check(lhs, &acc.modified);
        // Part of #3348: Handle deref store through IndexMut-returned &mut T.
        if let Some(cmr) = self.ref_resolution.collection_mut_refs.get(&local_idx).cloned() {
            return self.handle_collection_mut_ref_store(rhs_expr, &cmr, acc);
        }

        // Part of #2496: Handle deref store through argument reference locals.
        if let Some(&pointee_vec_idx) = self.ref_resolution.ref_arg_pointee_idx.get(&local_idx) {
            let track_key = usize::MAX - pointee_vec_idx; // synthetic key (#2496)
            let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(pointee_vec_idx)
            else {
                warn!(
                    ?local_idx,
                    pointee_vec_idx,
                    "CHC: dropped arg-ref deref store — missing pointee output state var (#2496)"
                );
                self.diagnostics.store_dropped_transition.inc();
                self.mark_state_var_modified(pointee_vec_idx); // #3138
                return true;
            };
            let mut pointee_field_projs = Vec::new();
            let mut index_proj_found = None;
            let mut pending_cons_idx = None;
            for (i, proj) in lhs.projection[1..].iter().enumerate() {
                match proj {
                    ProjectionElem::Downcast(variant_idx) if index_proj_found.is_none() => {
                        pending_cons_idx =
                            Some(crate::rustc_public_bridge::IndexedVal::to_index(variant_idx));
                    }
                    ProjectionElem::Field(idx, ty) if index_proj_found.is_none() => {
                        pointee_field_projs.push(FieldProjection {
                            field_idx: *idx,
                            cons_idx: pending_cons_idx.take(),
                            field_ty: Some(*ty),
                        });
                    }
                    ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                        index_proj_found = Some((i, proj.clone()));
                        break;
                    }
                    _ => return false, // external enum: ProjectionElem
                }
            }
            // Part of #2750: Route array element stores through arg-ref pointee.
            if let Some((_idx_offset, index_proj)) = index_proj_found {
                // Part of #3816: aggregate pointee — select field, store, update.
                if !pointee_field_projs.is_empty() {
                    return self.handle_aggregate_field_array_store_arg_ref_impl(
                        rhs_expr,
                        local_idx,
                        pointee_vec_idx,
                        track_key,
                        &index_proj,
                        &pointee_field_projs,
                        acc,
                    );
                }
                let post_idx_fp = collect_field_projections(
                    &lhs.projection[1 + _idx_offset + 1..],
                    UnknownProjectionPolicy::Break,
                );
                return self.handle_deref_store_array_arg_ref(
                    rhs_expr,
                    local_idx,
                    pointee_vec_idx,
                    &index_proj,
                    &post_idx_fp,
                    acc,
                );
            }
            let out_var = Expr::var(&**out_name, out_sort.clone());
            if pointee_field_projs.is_empty() {
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, rhs_expr.clone(), out_sort, false)
                {
                    acc.replace_constraint(track_key, constraint);
                    self.encode.local_expr_env.insert(track_key, rhs_expr);
                    self.mark_state_var_modified(pointee_vec_idx);
                    debug!(
                        local_idx,
                        pointee_vec_idx, "CHC: scalar Deref store via arg-ref (#2496)"
                    );
                    return true;
                }
                warn!(
                    ?local_idx,
                    pointee_vec_idx,
                    "CHC: arg-ref scalar deref store sort mismatch — constraint dropped"
                );
                self.diagnostics.store_dropped_transition.inc();
                self.mark_state_var_modified(pointee_vec_idx); // #3138
                return true;
            }

            let root_in = if let Some(env_expr) = self.encode.local_expr_env.get(&track_key) {
                env_expr.clone()
            } else if self.encode.modified_state_indices.contains(&pointee_vec_idx) {
                Expr::var(&**out_name, out_sort.clone())
            } else if let Some((in_name, in_sort)) =
                self.state_var_mgr.state_vars.get(pointee_vec_idx)
            {
                Expr::var(&**in_name, in_sort.clone())
            } else {
                warn!(
                    ?local_idx,
                    pointee_vec_idx,
                    "CHC: dropped arg-ref field deref store — missing pointee input state var"
                );
                self.diagnostics.store_dropped_transition.inc();
                self.mark_state_var_modified(pointee_vec_idx); // #3138
                return true;
            };

            if let Some(updated) =
                ChcCtx::apply_projection_update(&root_in, &pointee_field_projs, rhs_expr)
            {
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, updated.clone(), out_sort, false)
                {
                    acc.replace_constraint(track_key, constraint);
                    self.encode.local_expr_env.insert(track_key, updated);
                    self.mark_state_var_modified(pointee_vec_idx);
                } else {
                    warn!(?local_idx, pointee_vec_idx, "CHC: arg-ref field store sort mismatch");
                    self.diagnostics.store_dropped_transition.inc();
                    self.mark_state_var_modified(pointee_vec_idx); // #3138
                }
                debug!(local_idx, pointee_vec_idx, "CHC: field Deref store via arg-ref (#2496)");
                return true;
            }
            // Part of #3144: apply_projection_update returned None — drop store.
            warn!(?local_idx, pointee_vec_idx, "CHC: arg-ref projection_update failed — dropped");
            self.diagnostics.store_dropped_transition.inc();
            self.mark_state_var_modified(pointee_vec_idx); // #3138
            return true;
        }

        // Part of #428: Handle deref store through static pointer locals.
        if let Some(&static_vec_idx) = self.ref_resolution.static_ref_to_state_idx.get(&local_idx) {
            let track_key = usize::MAX - static_vec_idx;
            let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(static_vec_idx)
            else {
                warn!(
                    ?local_idx,
                    static_vec_idx,
                    "CHC: dropped static deref store — missing output state var (#428)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark static modified-unconstrained (universally quantified)
                self.mark_state_var_modified(static_vec_idx);
                return true;
            };

            // Simple scalar store: *static_ptr = value
            if lhs.projection.len() == 1 {
                let out_var = Expr::var(&**out_name, out_sort.clone());
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, rhs_expr.clone(), out_sort, false)
                {
                    acc.replace_constraint(track_key, constraint);
                    self.encode.local_expr_env.insert(track_key, rhs_expr);
                    self.mark_state_var_modified(static_vec_idx);
                    acc.modified.insert(track_key);
                    debug!(
                        local_idx,
                        static_vec_idx,
                        "CHC: emitted Reg-level scalar Deref store via static ref (#428)"
                    );
                    return true;
                }
                warn!(
                    ?local_idx,
                    static_vec_idx,
                    "CHC: static scalar deref store sort mismatch — constraint dropped (#428)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark static modified-unconstrained (universally quantified)
                self.mark_state_var_modified(static_vec_idx);
                return true;
            }

            // Field store through static: *static_ptr.field = value
            // Not yet needed for COUNTER += 1 pattern but handled for completeness.
            debug!(
                ?local_idx,
                static_vec_idx,
                num_projs = lhs.projection.len(),
                "CHC: static deref store with field projections — not yet handled (#428)"
            );
            return false;
        }

        let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx).cloned() else {
            return false;
        };

        let index_proj = ref_target
            .projections
            .iter()
            .find(|p| matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }));

        // Part of #3041/#3223: Collect Field projections after the first Index/ConstantIndex.
        let after_index_start = ref_target
            .projections
            .iter()
            .position(|p| {
                matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
            })
            .map(|i| i + 1)
            .unwrap_or(ref_target.projections.len());
        let field_projs = collect_field_projections(
            &ref_target.projections[after_index_start..],
            UnknownProjectionPolicy::Skip,
        );

        if let Some(index_proj) = index_proj {
            if let Some(&pointee_vec_idx) =
                self.ref_resolution.ref_arg_pointee_idx.get(&ref_target.local)
            {
                // Derived refs rooted in argument refs must update the pointee
                // array state var, not the pointer-typed argument slot (#3586).
                return self.handle_deref_store_array_arg_ref(
                    rhs_expr,
                    local_idx,
                    pointee_vec_idx,
                    index_proj,
                    &field_projs,
                    acc,
                );
            }
            // Part of #3816: pre-Index fields → aggregate root.
            let index_position = after_index_start.saturating_sub(1);
            let pre_idx = collect_field_projections(
                &ref_target.projections[..index_position],
                UnknownProjectionPolicy::Skip,
            );
            if !pre_idx.is_empty() {
                if let Some(r) = self.handle_lhs_index_through_ref_target_projs(
                    &rhs_expr,
                    local_idx,
                    &ref_target,
                    index_proj,
                    acc,
                ) {
                    return r;
                }
                warn!(
                    ref_local = local_idx,
                    n = pre_idx.len(),
                    "CHC: aggregate-root ref_target array store fell through (#3816)"
                );
            }
            return self.handle_deref_store_array_via_ref_targets(
                rhs_expr,
                local_idx,
                &ref_target,
                index_proj,
                &field_projs,
                acc,
            );
        }
        // Part of #3041: Category D — route Deref+Index stores through ref_target projs.
        if let Some(h) = lhs.projection[1..]
            .iter()
            .find(|p| matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }))
            .and_then(|idx| {
                self.handle_lhs_index_through_ref_target_projs(
                    &rhs_expr,
                    local_idx,
                    &ref_target,
                    idx,
                    acc,
                )
            })
        {
            return h;
        }

        let target_local = ref_target.local;
        // Part of #3768: graceful fallback instead of panic
        let Some(target_vec_idx) = self.try_state_idx_for_local(target_local) else {
            warn!(
                ?target_local,
                ?local_idx,
                "CHC: deref store target not in state map — sound fallback"
            );
            self.record_sound_fallback_reason("state_idx_missing_deref_store_target");
            return false;
        };

        // Part of #3041/#3223: Track Downcast projections as cons_idx on subsequent Field.
        let mut combined_field_projs =
            collect_field_projections(&ref_target.projections, UnknownProjectionPolicy::Skip);
        combined_field_projs.extend(collect_field_projections(
            &lhs.projection[1..],
            UnknownProjectionPolicy::Break,
        ));

        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(target_vec_idx)
        else {
            warn!(
                ?target_local,
                ?local_idx,
                "CHC: dropped Deref store via ref_targets — missing output state var (Part of #2236)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return true;
        };
        let out_var = Expr::var(&**out_name, out_sort.clone());

        if combined_field_projs.is_empty() {
            if let Some(constraint) =
                coerce_eq_constraint(&out_var, rhs_expr.clone(), out_sort, false)
            {
                acc.replace_constraint(target_local, constraint);
                self.encode.local_expr_env.insert(target_local, rhs_expr);
                acc.modified.insert(target_local);
                debug!(
                    target_local,
                    ref_local = local_idx,
                    "CHC: emitted Reg-level scalar Deref store via ref_targets"
                );
                return true;
            }
            warn!(
                target_local,
                ref_local = local_idx,
                "CHC: ref_targets scalar deref store sort mismatch — constraint dropped"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return true;
        }

        let root_in = if acc.modified.contains(&target_local) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&target_local) {
                env_expr.clone()
            } else {
                Expr::var(&**out_name, out_sort.clone())
            }
        } else {
            self.state_var_mgr.state_vars.get(target_vec_idx).map_or_else(
                || Expr::var(&**out_name, out_sort.clone()),
                |(n, s)| Expr::var(&**n, s.clone()),
            )
        };

        if let Some(updated) =
            ChcCtx::apply_projection_update(&root_in, &combined_field_projs, rhs_expr)
        {
            if let Some(constraint) =
                coerce_eq_constraint(&out_var, updated.clone(), &out_sort, false)
            {
                acc.replace_constraint(target_local, constraint);
                self.encode.local_expr_env.insert(target_local, updated);
                acc.modified.insert(target_local);
            } else {
                warn!(
                    target_local,
                    ref_local = local_idx,
                    num_field_projs = combined_field_projs.len(),
                    "CHC: deref field store sort mismatch — constraint dropped"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark target modified-unconstrained (universally quantified)
                acc.modified.insert(target_local);
            }
            debug!(
                target_local,
                ref_local = local_idx,
                num_field_projs = combined_field_projs.len(),
                "CHC: emitted Reg-level field Deref store via ref_targets"
            );
            return true;
        }
        // Part of #3148: Return false so the #2967 flattened-ref_target fallback
        // in encode_projection_assignment can handle this store.
        debug!(
            target_local,
            ref_local = local_idx,
            num_field_projs = combined_field_projs.len(),
            "CHC: apply_projection_update failed for Deref field store — deferring to fallback"
        );
        false
    }

    fn handle_deref_store_array_via_ref_targets(
        &mut self,
        rhs_expr: Expr,
        ref_local: usize,
        ref_target: &super::RefTarget,
        index_proj: &ProjectionElem,
        field_projs: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        self.handle_deref_store_array_via_ref_targets_impl(
            rhs_expr,
            ref_local,
            ref_target,
            index_proj,
            field_projs,
            acc,
        )
    }

    fn handle_deref_store_array_arg_ref(
        &mut self,
        rhs_expr: Expr,
        local_idx: usize,
        pointee_vec_idx: usize,
        index_proj: &ProjectionElem,
        field_projs: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        self.handle_deref_store_array_arg_ref_impl(
            rhs_expr,
            local_idx,
            pointee_vec_idx,
            index_proj,
            field_projs,
            acc,
        )
    }
}

// handle_collection_mut_ref_store is in codegen_stmt_store_ref_collection.rs
// (extracted per #3348, file size limit).
