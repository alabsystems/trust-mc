// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Flattened field projection and datatype field update helpers.
//!
//! Extracted from `codegen_stmt_assign_projection.rs` per #4130 to keep files under 500 lines.
//! Contains: encode_flattened_field_projection, encode_flattened_field_slot,
//! encode_flattened_field_span, encode_datatype_field_update.

use rustc_public::mir::Place;
use tracing::{debug, warn};
use ay_bindings::Expr;

use super::codegen_call_coerce::coerce_eq_constraint;
use super::codegen_decl_flatten::compute_nested_flat_span;
use super::codegen_types::CodegenTypes;
use super::stmt_accumulator::StmtAccumulator;
use super::{ChcCtx, FieldProjection};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Encode a flattened tuple/enum field projection assignment.
    ///
    /// Computes the target slot from the field projection metadata, then
    /// delegates to `encode_flattened_field_slot` for the actual write.
    ///
    /// Part of #3561: consolidated with encode_flattened_field_slot to
    /// eliminate duplicate OOB and constrain-failed fallback sites.
    pub(in crate::codegen_ay::chc) fn encode_flattened_field_projection(
        &mut self,
        rhs_expr: Expr,
        local_idx: usize,
        fp: &FieldProjection,
        acc: &mut StmtAccumulator<'_>,
    ) {
        if let Some(cons_idx) = fp.cons_idx {
            // Part of #3215: BV-flattened multi-ctor enum write path.
            let fld = if let Some(layout) = self.flatten.enum_bv_layouts.get(&local_idx)
                && cons_idx < layout.ctor_field_slot.len()
                && fp.field_idx < layout.ctor_field_slot[cons_idx].len()
            {
                let Some(payload_slot) = layout.payload_slot(cons_idx, fp.field_idx) else {
                    debug!(
                        local_idx,
                        cons_idx,
                        field_idx = fp.field_idx,
                        "encode_flattened_field_projection: omitted flattened enum payload write is a no-op"
                    );
                    return;
                };
                1 + payload_slot
            } else {
                // Part of #3041: Single-variant enum, no discriminant — payload IS fld0
                let n_fields = self.flattened_field_count(local_idx);
                if n_fields == 1 { 0 } else { 1 }
            };
            self.encode_flattened_field_slot(rhs_expr, local_idx, fld, acc);
            return;
        }

        if let Some(local_decl) = self.body.locals().get(local_idx)
            && let Some(sort) = Self::translate_ty(local_decl.ty)
            && let Some((leaf_slot, leaf_count)) = compute_nested_flat_span(&sort, &[fp.field_idx])
        {
            // Part of #3814: top-level non-leaf fields on recursively flattened
            // locals (for example `LinearExpr.constant: Rational`) must rewrite
            // the entire leaf span, not just the first slot.
            if leaf_count == 1 {
                self.encode_flattened_field_slot(rhs_expr, local_idx, leaf_slot, acc);
            } else {
                self.encode_flattened_field_span(rhs_expr, local_idx, leaf_slot, leaf_count, acc);
            }
            return;
        }

        // Sort lookup unavailable; direct mapping (flat tuple).
        self.encode_flattened_field_slot(rhs_expr, local_idx, fp.field_idx, acc);
    }

    /// Encode a nested field projection assignment on a recursively flattened local.
    ///
    /// Takes a pre-computed leaf slot index (from `compute_nested_flat_slot`) and
    /// constrains that slot while preserving all other flattened fields.
    ///
    /// Part of #2989: Fix multi-level MIR projection on recursively flattened locals.
    pub(in crate::codegen_ay::chc) fn encode_flattened_field_slot(
        &mut self,
        rhs_expr: Expr,
        local_idx: usize,
        target_slot: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        let field_count = self.flattened_field_count(local_idx);
        if target_slot >= field_count {
            warn!(
                local_idx,
                target_slot,
                field_count,
                "CHC: nested flattened field slot out of bounds — sound fallback"
            );
            self.projection_sound_fallback(local_idx, "proj_flattened_oob", acc);
            return;
        }

        let mut values = Vec::with_capacity(field_count);
        for field_idx in 0..field_count {
            if field_idx == target_slot {
                values.push(Some(rhs_expr.clone()));
            } else {
                values.push(self.flattened_local_field_expr(local_idx, field_idx, acc.modified));
            }
        }

        if self.constrain_flattened_fields(local_idx, &values, acc) {
            debug!(local_idx, target_slot, "CHC: nested flattened field slot assignment");
        } else {
            warn!(
                local_idx,
                target_slot, "CHC: constrain_flattened_fields failed — sound fallback"
            );
            self.projection_sound_fallback(local_idx, "proj_constrain_failed", acc);
        }
    }

    pub(in crate::codegen_ay::chc) fn encode_flattened_field_span(
        &mut self,
        rhs_expr: Expr,
        local_idx: usize,
        start_slot: usize,
        leaf_count: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        let field_count = self.flattened_field_count(local_idx);
        if start_slot.checked_add(leaf_count).is_none_or(|end| end > field_count) {
            warn!(
                local_idx,
                start_slot,
                leaf_count,
                field_count,
                "CHC: nested flattened field span out of bounds — sound fallback"
            );
            self.projection_sound_fallback(local_idx, "proj_flattened_oob", acc);
            return;
        }

        let mut replacement_leaves = Vec::with_capacity(leaf_count);
        super::codegen_stmt_flatten::collect_leaf_exprs(&rhs_expr, &mut replacement_leaves);
        if replacement_leaves.len() != leaf_count {
            warn!(
                local_idx,
                start_slot,
                leaf_count,
                actual_leaf_count = replacement_leaves.len(),
                "CHC: flattened field replacement leaf-count mismatch — sound fallback"
            );
            self.projection_sound_fallback(local_idx, "proj_flattened_leaf_mismatch", acc);
            return;
        }

        let mut values = Vec::with_capacity(field_count);
        for field_idx in 0..field_count {
            if (start_slot..start_slot + leaf_count).contains(&field_idx) {
                values.push(replacement_leaves[field_idx - start_slot].clone());
            } else {
                values.push(self.flattened_local_field_expr(local_idx, field_idx, acc.modified));
            }
        }

        if self.constrain_flattened_fields(local_idx, &values, acc) {
            debug!(
                local_idx,
                start_slot, leaf_count, "CHC: nested flattened field span assignment"
            );
        } else {
            warn!(
                local_idx,
                start_slot,
                leaf_count,
                "CHC: constrain_flattened_fields failed for leaf span — sound fallback"
            );
            self.projection_sound_fallback(local_idx, "proj_constrain_failed", acc);
        }
    }

    /// Encode a regular datatype field update via functional update.
    ///
    /// Resolves the root expression, applies `apply_projection_update`, and
    /// constrains the output variable with sort-safe equality.
    pub(in crate::codegen_ay::chc) fn encode_datatype_field_update(
        &mut self,
        _lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        field_projections: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) {
        // Get the root expression, using expr env or OUTPUT for modified locals
        // Fix #2055: Check local_expr_env first
        // Fix #2238: Use local_to_state_idx mapping for correct vector index
        // Part of #3768: graceful fallback instead of panic
        let Some(proj_vec_idx) = self.try_state_idx_for_local(local_idx) else {
            self.projection_sound_fallback(local_idx, "state_idx_missing_dt_field_update", acc);
            return;
        };
        let root_in = if acc.modified.contains(&local_idx) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&local_idx) {
                env_expr.clone()
            } else {
                let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(proj_vec_idx)
                else {
                    warn!(
                        local_idx,
                        proj_vec_idx,
                        "CHC: datatype field update missing output state var — recording fallback"
                    );
                    // Local is already in `modified` (branch condition above);
                    // helper re-insert is a no-op.
                    self.projection_sound_fallback(local_idx, "proj_missing_state_var", acc);
                    return;
                };
                Expr::var(&**out_name, out_sort.clone())
            }
        } else {
            let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(proj_vec_idx) else {
                warn!(
                    local_idx,
                    proj_vec_idx,
                    "CHC: datatype field update missing input state var — recording fallback"
                );
                self.projection_sound_fallback(local_idx, "proj_missing_state_var", acc);
                return;
            };
            Expr::var(&**in_name, in_sort.clone())
        };

        let updated = if root_in.sort().is_bitvec() {
            let local_ty = self.body.locals()[local_idx].ty;
            Self::bv_projection_update(&root_in, local_ty, field_projections, rhs_expr.clone())
                .or_else(|| Self::apply_projection_update(&root_in, field_projections, rhs_expr))
        } else {
            Self::apply_projection_update(&root_in, field_projections, rhs_expr)
        };

        if let Some(updated_expr) = updated {
            // Get output variable for the root local
            if let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(proj_vec_idx)
            {
                let out_var = Expr::var(&**out_name, out_sort.clone());
                // Part of #2244: use coerce_eq_constraint for sort-safe
                // equality. Datatype field updates may produce a different
                // sort than the declared output variable.
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, updated_expr.clone(), out_sort, false)
                {
                    // Fix #2055: Record updated whole value in expression env
                    self.encode.local_expr_env.insert(local_idx, updated_expr);
                    // Fix #2055: Replace previous constraint for same local
                    acc.replace_constraint(local_idx, constraint);
                    acc.modified.insert(local_idx);
                } else {
                    warn!(
                        local_idx,
                        ?proj_vec_idx,
                        "CHC: datatype field update sort mismatch — constraint dropped"
                    );
                    self.projection_sound_fallback(local_idx, "proj_sort_mismatch", acc);
                }
            } else {
                warn!(
                    local_idx,
                    proj_vec_idx,
                    output_state_len = self.state_var_mgr.output_state_vars.len(),
                    "CHC: projection output slot missing — constraint dropped"
                );
                self.projection_sound_fallback(local_idx, "proj_missing_state_var", acc);
            }
        } else {
            warn!(
                local_idx,
                projection_depth = field_projections.len(),
                "CHC: apply_projection_update failed — constraint dropped"
            );
            self.projection_sound_fallback(local_idx, "proj_update_failed", acc);
        }
    }
}
