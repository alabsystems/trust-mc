// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Field-level projection assignment encoding for flattened and indexed fields.
//!
//! Extracted from `codegen_stmt_assign_projection.rs` per #4130 to keep files
//! under 500 lines. Contains: handle_field_index_store, encode_flattened_field_projection,
//! encode_flattened_field_slot, encode_flattened_field_span.

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use tracing::{debug, warn};

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::codegen_call_coerce::coerce_eq_constraint;
use super::codegen_decl_flatten::compute_nested_flat_slot;
use super::codegen_stmt_projection::constant_index_offset;
use super::codegen_types::CodegenTypes;
use super::stmt_accumulator::StmtAccumulator;
use super::{ChcCtx, FieldProjection, UnknownProjectionPolicy, collect_field_projections};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle `_N.field_chain[idx] = rhs` projection assignments.
    ///
    /// Splits the projection into leading Field/Downcast projections and a
    /// trailing Index/ConstantIndex. Performs:
    /// 1. Field selection to reach the array
    /// 2. Z3 array store at the index
    /// 3. Functional field update back to the root
    ///
    /// Part of #3561: Closes the Field->Index projection gap.
    pub(super) fn handle_field_index_store(
        &mut self,
        lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let proj = lhs.projection.as_slice();

        // Find the Index/ConstantIndex position — must have Field before it.
        let index_pos = proj.iter().position(|p| {
            matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
        });
        let Some(index_pos) = index_pos else { return false };
        if index_pos == 0 {
            return false; // No Field prefix — handle_array_element_store covers this.
        }

        // Split: field_prefix = proj[..index_pos], index_proj = proj[index_pos]
        let field_prefix = &proj[..index_pos];
        let index_proj = &proj[index_pos];

        // Trailing projections after Index (e.g., _N.data[i].field) — not yet supported.
        if index_pos + 1 < proj.len() {
            debug!("handle_field_index_store: trailing projections after Index not supported");
            return false;
        }

        // Part of #3766: Handle leading Deref by resolving through ref_targets.
        // Pattern: (*ref).field[i] = rhs — the Deref means the base local is a
        // reference; resolve through ref_targets to find the actual struct local,
        // then use [Field, Index] on that target.
        let (effective_prefix, store_local, ref_target_projs) =
            if matches!(field_prefix.first(), Some(ProjectionElem::Deref)) {
                if let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx) {
                    (&field_prefix[1..], ref_target.local, ref_target.projections.clone())
                } else {
                    return false;
                }
            } else {
                (field_prefix, local_idx, Vec::new())
            };

        // Collect field projections from the (possibly Deref-stripped) prefix.
        let mut field_projs = collect_field_projections(
            effective_prefix,
            UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
        );
        if field_projs.is_empty() {
            return false;
        }

        // The lhs fields after the Deref are relative to the REFERENT, which is
        // `ref_target.projections` inside `store_local`. Applying them to
        // `store_local` itself wrote another field: with `let r = &mut o.inner;
        // r.arr[1] = v`, `arr` was taken as `o`'s own field and the store landed
        // on `o.pre` (a false proof of `o.inner.arr[1] == 0` and a Genuine
        // counterexample for its safe twin).
        let composed = !ref_target_projs.is_empty();
        if composed {
            if ref_target_projs
                .iter()
                .any(|p| !matches!(p, ProjectionElem::Field(..) | ProjectionElem::Downcast(_)))
            {
                return false;
            }
            let mut full =
                collect_field_projections(&ref_target_projs, UnknownProjectionPolicy::Skip);
            full.append(&mut field_projs);
            field_projs = full;
            // An enum payload in the composed path: the enum-layout handlers
            // after this one resolve a Downcast ref_target.
            if field_projs.iter().any(|fp| fp.cons_idx.is_some()) {
                return false;
            }
        }

        // A nested path into a flattened owner (`o.inner.arr[i]`, or a composed
        // one): the array's slot is placed exactly or the owner fails closed.
        // The root-expression path below reads slot 0 as if it were the whole
        // owner, and the handlers after this one wrote slot 0 as the array
        // (`let r = &mut o; r.inner.arr[i] = v` stored into `o.pre`).
        if self.flatten.flattened_tuple_locals.contains(&store_local)
            && field_projs.len() > 1
            && field_projs.iter().all(|fp| fp.cons_idx.is_none())
        {
            return match self.faithful_nested_flat_slot(store_local, &field_projs) {
                Ok(fld) => {
                    if self.store_into_flattened_array_slot(
                        store_local,
                        fld,
                        index_proj,
                        rhs_expr,
                        acc,
                    ) {
                        true
                    } else {
                        warn!(store_local, fld, "CHC: nested Field+Index store not encodable");
                        self.havoc_local_fail_closed(
                            store_local,
                            "flat_field_index_store_unresolved",
                            acc,
                        );
                        true
                    }
                }
                Err(why) => {
                    warn!(store_local, why, "CHC: nested Field+Index store has no faithful slot");
                    self.havoc_local_fail_closed(
                        store_local,
                        "flat_field_index_store_unresolved",
                        acc,
                    );
                    true
                }
            };
        }

        if self.flatten.flattened_tuple_locals.contains(&store_local) && field_projs.len() == 1 {
            let fp = &field_projs[0];
            let fld = if let Some(cons_idx) = fp.cons_idx {
                if let Some(layout) = self.flatten.enum_bv_layouts.get(&store_local)
                    && cons_idx < layout.ctor_field_slot.len()
                    && fp.field_idx < layout.ctor_field_slot[cons_idx].len()
                {
                    let Some(payload_slot) = layout.payload_slot(cons_idx, fp.field_idx) else {
                        debug!(
                            store_local,
                            cons_idx,
                            field_idx = fp.field_idx,
                            "handle_field_index_store: omitted flattened enum payload has no slot"
                        );
                        return false;
                    };
                    1 + payload_slot
                } else {
                    let n_fields = self.flattened_field_count(store_local);
                    if n_fields == 1 { 0 } else { 1 }
                }
            } else {
                // The field's leaf slot through the checked path (C5b); there
                // is no raw-index fallback, which named another leaf's slot
                // whenever the sort walk disagreed with the type.
                match self.flat_slot_for(store_local, std::slice::from_ref(fp)) {
                    Ok(slot) => slot,
                    Err(why) => {
                        warn!(store_local, why, "CHC: Field+Index store has no faithful slot");
                        self.havoc_local_fail_closed(
                            store_local,
                            "flat_field_index_store_unresolved",
                            acc,
                        );
                        return true;
                    }
                }
            };

            return self.store_into_flattened_array_slot(
                store_local,
                fld,
                index_proj,
                rhs_expr,
                acc,
            );
        }

        // Get current root expression for non-flattened locals.
        // Part of #3768: graceful fallback instead of panic
        let Some(vec_idx) = self.try_state_idx_for_local(store_local) else {
            return false;
        };
        let root_expr = if acc.modified.contains(&store_local) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&store_local) {
                env_expr.clone()
            } else {
                let Some((name, sort)) = self.state_var_mgr.output_state_vars.get(vec_idx) else {
                    return false;
                };
                Expr::var(&**name, sort.clone())
            }
        } else {
            let Some((name, sort)) = self.state_var_mgr.state_vars.get(vec_idx) else {
                return false;
            };
            Expr::var(&**name, sort.clone())
        };

        // Step 1: Select field chain to reach the array.
        let Some(array_expr) = Self::apply_field_selections(root_expr.clone(), &field_projs) else {
            return false;
        };

        // Verify the result is an Array sort (Z3 store requires this).
        if !array_expr.sort().is_array() {
            debug!("handle_field_index_store: field chain result is not Array sort");
            return false;
        }

        // Step 2: Resolve index and perform array store.
        let index_expr = match index_proj {
            ProjectionElem::Index(index_local) => {
                let index_local_idx: usize = *index_local;
                // Part of #3768: graceful fallback instead of panic
                let Some(idx_vec) = self.try_state_idx_for_local(index_local_idx) else {
                    return false;
                };
                let raw = if acc.modified.contains(&index_local_idx) {
                    let Some((name, sort)) = self.state_var_mgr.output_state_vars.get(idx_vec)
                    else {
                        return false;
                    };
                    Expr::var(&**name, sort.clone())
                } else {
                    let Some((name, sort)) = self.state_var_mgr.state_vars.get(idx_vec) else {
                        return false;
                    };
                    Expr::var(&**name, sort.clone())
                };
                coerce_bitvec_width_safe(raw, POINTER_WIDTH, SignExtension::ZeroExtend)
            }
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                // #from_end needs the slice's runtime length -> fail closed (projection_path.rs)
                let Some(actual) = constant_index_offset(*offset, *min_length, *from_end) else {
                    return false;
                };
                Expr::bitvec_const(actual as u128, POINTER_WIDTH)
            }
            _ => return false,
        };

        let value_to_store =
            Self::coerce_store_value(array_expr.sort(), rhs_expr, false, &self.diagnostics);
        let new_array = array_expr.store(index_expr, value_to_store);

        // Step 3: Functional update — replace the array field in the root.
        let Some(updated_root) = Self::apply_projection_update(&root_expr, &field_projs, new_array)
        else {
            return false;
        };

        // Emit constraint: output_var = updated_root
        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        else {
            return false;
        };
        let out_var = Expr::var(&*out_name, out_sort.clone());
        if let Some(constraint) =
            coerce_eq_constraint(&out_var, updated_root.clone(), &out_sort, false)
        {
            self.encode.local_expr_env.insert(store_local, updated_root);
            acc.replace_constraint(store_local, constraint);
            acc.modified.insert(store_local);
            debug!(store_local, "CHC: Field->Index store via functional update (Part of #3561)");
            true
        } else {
            false
        }
    }

    /// The flattened slot of the Field-only path `projs` on `local`, placed
    /// the way read case C places it (`faithful_flat_field_path`, then
    /// `compute_nested_flat_slot`), or why it cannot be placed faithfully.
    pub(in crate::codegen_ay::chc) fn faithful_nested_flat_slot(
        &self,
        local: usize,
        projs: &[FieldProjection],
    ) -> Result<usize, &'static str> {
        if projs.iter().any(|fp| fp.cons_idx.is_some()) {
            return Err("enum_downcast_in_path");
        }
        let projs = self.faithful_flat_field_path(local, projs)?;
        let local_ty = self.body.locals().get(local).ok_or("local_missing")?.ty;
        let sort = Self::translate_ty(local_ty).ok_or("root_sort_unavailable")?;
        let indices: Vec<usize> = projs.iter().map(|fp| fp.field_idx).collect();
        compute_nested_flat_slot(&sort, &indices).ok_or("slot_unresolved")
    }

    /// `slot[index] = rhs` on the array-sorted flattened slot `fld` of
    /// `store_local`, keeping every other slot. False when the slot is not an
    /// array or the index cannot be resolved; nothing is emitted then.
    fn store_into_flattened_array_slot(
        &mut self,
        store_local: usize,
        fld: usize,
        index_proj: &ProjectionElem,
        rhs_expr: Expr,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let field_count = self.flattened_field_count(store_local);
        if fld >= field_count {
            return false;
        }

        let Some(array_expr) = self.flattened_local_field_expr(store_local, fld, acc.modified)
        else {
            return false;
        };
        if !array_expr.sort().is_array() {
            debug!(
                store_local,
                fld, "handle_field_index_store: flattened field slot is not an Array sort"
            );
            return false;
        }

        let index_expr = match index_proj {
            ProjectionElem::Index(index_local) => {
                let Some(raw) = self.resolve_local_expr(*index_local, acc.modified) else {
                    return false;
                };
                coerce_bitvec_width_safe(raw, POINTER_WIDTH, SignExtension::ZeroExtend)
            }
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                // #from_end needs the slice's runtime length -> fail closed (projection_path.rs)
                let Some(actual_index) = constant_index_offset(*offset, *min_length, *from_end)
                else {
                    return false;
                };
                Expr::bitvec_const(actual_index as u128, POINTER_WIDTH)
            }
            _ => return false,
        };
        let value_to_store =
            Self::coerce_store_value(array_expr.sort(), rhs_expr, false, &self.diagnostics);
        let new_array = array_expr.store(index_expr, value_to_store);

        let mut values = Vec::with_capacity(field_count);
        for field_idx in 0..field_count {
            if field_idx == fld {
                values.push(Some(new_array.clone()));
            } else {
                values.push(self.flattened_local_field_expr(store_local, field_idx, acc.modified));
            }
        }

        if self.constrain_flattened_fields(store_local, &values, acc) {
            debug!(
                store_local,
                fld, "CHC: emitted flattened Field+Index store directly on array slot"
            );
            return true;
        }
        false
    }

    /// Encode a flattened tuple/enum field projection assignment.
    ///
    /// Computes the target slot from the field projection metadata, then
    /// delegates to `encode_flattened_field_slot` for the actual write.
    ///
    /// Part of #3561: consolidated with encode_flattened_field_slot to
    /// eliminate duplicate OOB and constrain-failed fallback sites.
    pub(super) fn encode_flattened_field_projection(
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

        // The field's slot span through the checked path (C5b): a step
        // `translate_ty` collapses (`UnsafeCell<T>.0`) is the whole local.
        match self.flat_span_for(local_idx, std::slice::from_ref(fp)) {
            Ok((leaf_slot, leaf_count)) => {
                // Part of #3814: top-level non-leaf fields on recursively
                // flattened locals (for example `LinearExpr.constant:
                // Rational`) must rewrite the entire leaf span, not just the
                // first slot.
                if leaf_count == 1 {
                    self.encode_flattened_field_slot(rhs_expr, local_idx, leaf_slot, acc);
                } else {
                    self.encode_flattened_field_span(
                        rhs_expr, local_idx, leaf_slot, leaf_count, acc,
                    );
                }
            }
            Err(why) => {
                // There is no raw-index fallback: it named another leaf's slot
                // whenever the sort walk disagreed with the type.
                warn!(local_idx, why, "CHC: flattened field store has no faithful slot");
                self.havoc_local_fail_closed(local_idx, "flat_field_store_unresolved", acc);
            }
        }
    }

    /// Encode a nested field projection assignment on a recursively flattened local.
    ///
    /// Takes a pre-computed leaf slot index (from `compute_nested_flat_slot`) and
    /// constrains that slot while preserving all other flattened fields.
    ///
    /// Part of #2989: Fix multi-level MIR projection on recursively flattened locals.
    pub(super) fn encode_flattened_field_slot(
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

    pub(super) fn encode_flattened_field_span(
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
}
