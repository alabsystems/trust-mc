// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Compound array store handlers through arg-ref and ref_target projections.
//!
//! Extracted from `codegen_stmt_store_ref_array.rs` per #4130 to keep files
//! under 500 lines.

use ay_bindings::Expr;
use rustc_public::mir::ProjectionElem;
use tracing::{debug, warn};

use super::codegen_call_coerce::coerce_eq_constraint;
use super::codegen_ctx::diagnostics::CellCounter;
use super::stmt_accumulator::StmtAccumulator;
use super::{
    ChcCtx, FieldProjection, POINTER_WIDTH, UnknownProjectionPolicy, collect_field_projections,
    constant_index_offset,
};
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #3816: Array store into a field of an arg-ref aggregate pointee.
    ///
    /// Pattern: `(*_arg).field[idx] = val` where `_arg: &mut Aggregate` and the
    /// pointee state var represents the whole Aggregate. Selects the array field,
    /// stores the value, then updates the aggregate via `apply_projection_update`.
    pub(in crate::codegen_ay::chc) fn handle_aggregate_field_array_store_arg_ref_impl(
        &mut self,
        rhs_expr: Expr,
        local_idx: usize,
        pointee_vec_idx: usize,
        track_key: usize,
        index_proj: &ProjectionElem,
        field_projs: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(pointee_vec_idx)
        else {
            warn!(
                local_idx,
                pointee_vec_idx,
                "CHC: dropped aggregate field array store — missing output (#3816)"
            );
            self.diagnostics.store_dropped_transition.inc();
            self.mark_state_var_modified(pointee_vec_idx);
            return true;
        };
        let out_name = out_name.clone();
        let out_sort = out_sort.clone();

        let container_in = if self.encode.modified_state_indices.contains(&pointee_vec_idx) {
            if let Some(env) = self.encode.local_expr_env.get(&track_key) {
                env.clone()
            } else {
                Expr::var(&*out_name, out_sort.clone())
            }
        } else if let Some((n, s)) = self.state_var_mgr.state_vars.get(pointee_vec_idx) {
            Expr::var(&**n, s.clone())
        } else {
            warn!(
                local_idx,
                pointee_vec_idx, "CHC: dropped aggregate field array store — missing input (#3816)"
            );
            self.diagnostics.store_dropped_transition.inc();
            self.mark_state_var_modified(pointee_vec_idx);
            return true;
        };

        // Navigate through field projections to extract the array. `container_in`
        // is the aggregate's state variable — the local's contents, a value — and
        // each selected field of a value is again a value.
        let mut array_in = crate::codegen_ay::provenance::Val::of_value(container_in.clone());
        for fp in field_projs {
            let Some(selected) = Self::datatype_field_select(&array_in, fp.field_idx, fp.cons_idx)
            else {
                warn!(
                    local_idx,
                    pointee_vec_idx,
                    "CHC: aggregate field array store — field select failed (#3816)"
                );
                self.diagnostics.store_dropped_transition.inc();
                self.mark_state_var_modified(pointee_vec_idx);
                return true;
            };
            array_in = selected;
        }

        let Some(index_expr) = Self::resolve_index_expr(self, index_proj, acc) else {
            warn!(
                local_idx,
                pointee_vec_idx, "CHC: aggregate field array store — index resolve failed (#3816)"
            );
            self.diagnostics.store_dropped_transition.inc();
            self.mark_state_var_modified(pointee_vec_idx);
            return true;
        };

        let array_in = array_in.into_expr();
        let coerced_rhs =
            Self::coerce_store_value(array_in.sort(), rhs_expr, false, &self.diagnostics);
        let new_array = array_in.store(index_expr, coerced_rhs);

        let Some(updated) = Self::apply_projection_update(&container_in, field_projs, new_array)
        else {
            warn!(
                local_idx,
                pointee_vec_idx,
                "CHC: aggregate field array store — projection update failed (#3816)"
            );
            self.diagnostics.store_dropped_transition.inc();
            self.mark_state_var_modified(pointee_vec_idx);
            return true;
        };

        let container_out = Expr::var(&*out_name, out_sort.clone());
        if let Some(c) = coerce_eq_constraint(&container_out, updated.clone(), &out_sort, false) {
            acc.replace_constraint(track_key, c);
            self.encode.local_expr_env.insert(track_key, updated);
            self.mark_state_var_modified(pointee_vec_idx);
            debug!(
                local_idx,
                pointee_vec_idx,
                n = field_projs.len(),
                "CHC: emitted aggregate field array store via arg-ref (#3816)"
            );
            return true;
        }
        warn!(
            local_idx,
            pointee_vec_idx, "CHC: aggregate field array store — sort mismatch (#3816)"
        );
        self.diagnostics.store_dropped_transition.inc();
        self.mark_state_var_modified(pointee_vec_idx);
        true
    }

    /// Part of #3041: Category D — compound array store through ref_target projections.
    ///
    /// Pattern: `(*_ref)[idx] = val` where `_ref = &container[Downcast(v)][Field(f)]`
    /// and the Index projection is in `lhs.projection[1..]` (not ref_target.projections).
    ///
    /// Returns `Some(true)` if handled, `None` if this handler cannot resolve it.
    pub(in crate::codegen_ay::chc) fn handle_lhs_index_through_ref_target_projs(
        &mut self,
        rhs_expr: &Expr,
        ref_local: usize,
        ref_target: &super::RefTarget,
        lhs_index: &ProjectionElem,
        acc: &mut StmtAccumulator<'_>,
    ) -> Option<bool> {
        let target_local = ref_target.local;
        // Part of #3768: graceful fallback instead of panic
        let target_vec_idx = self.try_state_idx_for_local(target_local)?;

        // Part of #3223: Build FieldProjection list from ref_target projections.
        let ref_field_projs =
            collect_field_projections(&ref_target.projections, UnknownProjectionPolicy::Skip);
        if ref_field_projs.is_empty() {
            return Some(self.handle_deref_store_array_via_ref_targets_impl(
                rhs_expr.clone(),
                ref_local,
                ref_target,
                lhs_index,
                &[],
                acc,
            ));
        }

        // Part of #3041/#3215: Handle BV-flattened enum locals.
        // For flattened multi-ctor enums, state vars are decomposed into
        // consecutive scalars (fld0=tag, fld1..=payload). Resolve Downcast+Field
        // through EnumBvLayout to find the correct payload slot, then perform
        // the array element store directly on that slot.
        if self.flatten.flattened_tuple_locals.contains(&target_local) && ref_field_projs.len() == 1
        {
            let fp = &ref_field_projs[0];
            // Resolve the flattened slot index (same logic as encode_flattened_field_projection).
            let fld = if let Some(cons_idx) = fp.cons_idx {
                if let Some(layout) = self.flatten.enum_bv_layouts.get(&target_local)
                    && cons_idx < layout.ctor_field_slot.len()
                    && fp.field_idx < layout.ctor_field_slot[cons_idx].len()
                {
                    let Some(payload_slot) = layout.payload_slot(cons_idx, fp.field_idx) else {
                        warn!(
                            target_local,
                            cons_idx,
                            field_idx = fp.field_idx,
                            "CHC: flattened-enum array store targeted omitted payload slot"
                        );
                        return None;
                    };
                    1 + payload_slot
                } else {
                    // Part of #3041: Single-variant enum, no discriminant — payload IS fld0
                    let n_fields = self.flattened_field_count(target_local);
                    if n_fields == 1 { 0 } else { 1 }
                }
            } else {
                fp.field_idx
            };

            let field_count = self.flattened_field_count(target_local);
            if fld >= field_count {
                warn!(
                    target_local,
                    fld,
                    field_count,
                    "CHC: flattened-enum array store — fld >= field_count, returning None"
                );
                return None;
            }

            // Read the current array value from the correct flattened slot.
            let Some(array_in) = self.flattened_local_field_expr(target_local, fld, &acc.modified)
            else {
                warn!(
                    target_local,
                    fld,
                    "CHC: flattened-enum array store — flattened_local_field_expr returned None"
                );
                return None;
            };

            // Resolve the index expression.
            let Some(index_expr) = Self::resolve_index_expr(self, lhs_index, acc) else {
                warn!(
                    target_local,
                    fld,
                    ?lhs_index,
                    "CHC: flattened-enum array store — resolve_index_expr returned None"
                );
                return None;
            };

            // Perform the array element store.
            let coerced_rhs = Self::coerce_store_value(
                array_in.sort(),
                rhs_expr.clone(),
                false,
                &self.diagnostics,
            );
            let new_array = array_in.store(index_expr, coerced_rhs);

            // Write the updated array back to the flattened slot, preserving
            // all other slots (discriminant tag and other payload fields).
            let mut values = Vec::with_capacity(field_count);
            for field_idx in 0..field_count {
                if field_idx == fld {
                    values.push(Some(new_array.clone()));
                } else {
                    values.push(self.flattened_local_field_expr(
                        target_local,
                        field_idx,
                        &acc.modified,
                    ));
                }
            }

            if self.constrain_flattened_fields(target_local, &values, acc) {
                debug!(
                    target_local,
                    ref_local,
                    fld,
                    "CHC: emitted flattened-enum array store through ref_target (#3041/#3215)"
                );
                return Some(true);
            }
            warn!(
                target_local,
                ref_local, fld, "CHC: flattened-enum array store via ref_target — constrain failed"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return Some(true);
        }

        // Get the container's current expression.
        let container_in = if acc.modified.contains(&target_local) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&target_local) {
                env_expr.clone()
            } else {
                let (name, sort) = self.state_var_mgr.output_state_vars.get(target_vec_idx)?;
                Expr::var(&**name, sort.clone())
            }
        } else {
            let (name, sort) = self.state_var_mgr.state_vars.get(target_vec_idx)?;
            Expr::var(&**name, sort.clone())
        };

        // Extract the array from the container through ref_target field projections.
        // Same provenance as above: state variable in, field values out.
        let mut array_in = crate::codegen_ay::provenance::Val::of_value(container_in.clone());
        for fp in &ref_field_projs {
            array_in = Self::datatype_field_select(&array_in, fp.field_idx, fp.cons_idx)?;
        }
        let array_in = array_in.into_expr();

        // Resolve the index expression.
        let index_expr = Self::resolve_index_expr(self, lhs_index, acc)?;

        let coerced_rhs =
            Self::coerce_store_value(array_in.sort(), rhs_expr.clone(), false, &self.diagnostics);
        let new_array = array_in.store(index_expr, coerced_rhs);

        let updated_container =
            Self::apply_projection_update(&container_in, &ref_field_projs, new_array)?;

        let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(target_vec_idx)?;
        let container_out = Expr::var(&**out_name, out_sort.clone());
        if let Some(c) = coerce_eq_constraint(&container_out, updated_container, out_sort, false) {
            acc.replace_constraint(target_local, c);
            acc.modified.insert(target_local);
            debug!(
                target_local,
                ref_local,
                num_ref_projs = ref_field_projs.len(),
                "CHC: emitted Reg-level array store through ref_target projections (#3041)"
            );
            Some(true)
        } else {
            warn!(
                target_local,
                ref_local,
                "CHC: Deref+Index store through ref_target — sort mismatch in container update"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            Some(true)
        }
    }

    /// Resolve an Index or ConstantIndex projection to an expression.
    ///
    /// Shared helper for array store paths. Part of #3041.
    pub(in crate::codegen_ay::chc) fn resolve_index_expr(
        &self,
        lhs_index: &ProjectionElem,
        acc: &StmtAccumulator<'_>,
    ) -> Option<Expr> {
        let raw = match lhs_index {
            ProjectionElem::Index(index_local) => {
                self.resolve_local_expr(*index_local, &acc.modified)
            }
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                let actual_index = constant_index_offset(*offset, *min_length, *from_end);
                Some(Expr::bitvec_const(actual_index as u128, POINTER_WIDTH))
            }
            _ => None,
        }?;
        Some(coerce_bitvec_width_safe(raw, POINTER_WIDTH, SignExtension::ZeroExtend))
    }
}
