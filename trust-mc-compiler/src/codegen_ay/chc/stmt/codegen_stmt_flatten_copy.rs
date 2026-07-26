// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Flattened local copy/move and generic rvalue assignment helpers.
//!
//! Extracted from `codegen_stmt_flatten.rs` per #4130. Contains:
//! - BV-flattened multi-constructor enum Aggregate assignment
//! - Pattern 4: Use(Copy/Move(src)) where src is also flattened
//! - Pattern 5: Use(Copy/Move(src)) with field projections
//! - Generic rvalue fallback (Cast, Ref, Transmute, etc.)
//! - `propagate_collection_len_cap_from_flattened_aggregate`
//! - `collect_leaf_exprs` free function

use ay_bindings::Expr;
use rustc_public::mir::{AggregateKind, Operand, ProjectionElem, Rvalue};
use tracing::{debug, warn};

use crate::rustc_public_bridge::IndexedVal;

use super::ChcCtx;
use super::codegen_call_coerce::coerce_eq_constraint;
use super::stmt_accumulator::StmtAccumulator;
use crate::codegen_ay::types::ptr_sort;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Try to encode a BV-flattened multi-constructor enum Aggregate assignment.
    ///
    /// Part of #3215: State vars: [tag, payload_fld0, ..., payload_fldN].
    /// Sets tag to constructor index, maps operands to payload slots per
    /// the constructor's field layout, zero-inits unused slots (#3994).
    ///
    /// Returns `true` if handled.
    /// Part of #4130: extracted from codegen_stmt_flatten.rs.
    pub(in crate::codegen_ay::chc) fn try_encode_bv_flattened_enum(
        &mut self,
        local_idx: usize,
        rhs: &'body Rvalue,
        acc: &mut StmtAccumulator<'_>,
        field_count: usize,
    ) -> bool {
        let Rvalue::Aggregate(AggregateKind::Adt(_, variant_idx, _, _, _), operands) = rhs else {
            return false;
        };
        let Some(layout) = self.flatten.enum_bv_layouts.get(&local_idx).cloned() else {
            return false;
        };

        let ctor_idx = variant_idx.to_index();
        // Tag expression: Bool for 2-ctor, BV(n) for 3+
        let tag_expr: Option<Expr> = Some(if layout.num_constructors == 2 {
            Expr::bool_const(ctor_idx == 1)
        } else {
            Expr::bitvec_const(ctor_idx as u64, layout.tag_bits)
        });
        let mut values: Vec<Option<Expr>> = vec![tag_expr];

        // Part of #3994: Initialize unused payload slots to sort-appropriate
        // zero instead of leaving unconstrained. BV-flattened enum comparison
        // uses raw BV equality on the concat'd representation; unconstrained
        // payload bits for ZST/unit variants cause spurious inequality.
        let vec_idx_opt = self.try_state_idx_for_local(local_idx);
        let mut payload_values: Vec<Option<Expr>> = (0..layout.max_payload_slots)
            .map(|slot_idx| {
                vec_idx_opt
                    .and_then(|vi| self.state_var_mgr.output_state_vars.get(vi + 1 + slot_idx))
                    .and_then(|(_, sort)| ChcCtx::sort_default_expr(sort))
            })
            .collect();

        if ctor_idx < layout.ctor_field_slot.len() {
            let ctor_slots = &layout.ctor_field_slot[ctor_idx];
            for (field_idx, operand) in operands.iter().enumerate() {
                if let Some(expr) = self.translate_operand_with_modified(operand, acc.modified) {
                    if field_idx < ctor_slots.len() {
                        let slot = ctor_slots[field_idx];
                        if slot == usize::MAX {
                            continue;
                        }
                        // Decompose nested structs into leaf scalars
                        let mut leaves = Vec::new();
                        collect_leaf_exprs(&expr, &mut leaves);
                        for (i, leaf) in leaves.into_iter().enumerate() {
                            if slot + i < layout.max_payload_slots {
                                payload_values[slot + i] = leaf;
                            }
                        }
                    }
                }
            }
        }
        values.extend(payload_values);

        self.constrain_flattened_fields(local_idx, &values, acc);
        // Part of #4101: Propagate ref_targets through BV-flattened enum
        // construction. When Option::Some(ptr) is encoded and the operand
        // local has a ref_target (e.g., NonNull::new result), carry it to
        // the enum local so downstream Downcast+Field extraction can
        // propagate it to the unwrapped payload local.
        for operand in operands.iter() {
            if let Operand::Copy(place) | Operand::Move(place) = operand
                && place.projection.is_empty()
            {
                let src_local: usize = place.local;
                if let Some(ref_target) = self.ref_resolution.ref_targets.get(&src_local).cloned() {
                    debug!(
                        local_idx,
                        src_local, "bv_flattened_enum: propagated ref_target from operand (#4101)"
                    );
                    self.ref_resolution.ref_targets.insert(local_idx, ref_target);
                    self.ref_resolution.call_forwarded_raw_ptrs.insert(local_idx);
                    break;
                }
            }
        }
        debug!(
            local_idx,
            variant = ctor_idx,
            field_count,
            "CHC: assigned BV-flattened multi-ctor enum Aggregate (#3215)"
        );
        true
    }

    /// Try to encode a flattened local assignment from copy/move or generic rvalue.
    ///
    /// Handles patterns 4, 5, and generic rvalue fallback from
    /// `try_encode_flattened_local_assign`. Returns `true` if handled.
    ///
    /// Part of #4130: extracted from codegen_stmt_flatten.rs.
    pub(in crate::codegen_ay::chc) fn try_encode_flattened_copy_or_rvalue(
        &mut self,
        local_idx: usize,
        rhs: &'body Rvalue,
        acc: &mut StmtAccumulator<'_>,
        field_count: usize,
    ) -> bool {
        // Pattern 4: Use(Copy/Move(src)) where src is also flattened → copy N fields
        if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rhs {
            let src_idx: usize = src.local;
            if src.projection.is_empty() && self.flatten.flattened_tuple_locals.contains(&src_idx) {
                // Part of #3768: graceful fallback instead of panic
                let Some(dst_vec) = self.try_state_idx_for_local(local_idx) else {
                    return false;
                };
                let locals_len = self.body.locals().len();
                let n = field_count.min(self.flattened_field_count(src_idx));
                // Part of #3447: track field-level fallbacks inside the loop
                // (borrow checker prevents calling record_sound_fallback inside).
                let mut flatten_copy_fallbacks: usize = 0;

                for i in 0..n {
                    let fld_key = if i == 0 { local_idx } else { local_idx + i * locals_len };
                    if let (Some(src_expr), Some((dn, ds))) = (
                        self.flattened_local_field_expr(src_idx, i, acc.modified),
                        self.state_var_mgr.output_state_vars.get(dst_vec + i).cloned(),
                    ) {
                        let dst_var = Expr::var(&*dn, ds.clone());
                        // Part of #2214: use coerce_eq_constraint for sort-safe
                        // copy. Handles BV width mismatches and Bool↔BV coercion
                        // when source and destination flattened field sorts differ.
                        if let Some(eq) =
                            coerce_eq_constraint(&dst_var, src_expr.clone(), &ds, false)
                        {
                            acc.replace_constraint(fld_key, eq);
                            if let Some(cached_expr) =
                                Self::coerce_flatten_slot_value(&ds, src_expr.clone())
                            {
                                self.encode.flattened_field_env.insert((local_idx, i), cached_expr);
                            } else {
                                self.encode
                                    .flattened_field_env
                                    .insert((local_idx, i), src_expr.clone());
                            }
                        } else {
                            // Part of #3038: emit self-loop (fld_out = fld_in) instead of
                            // leaving this field unconstrained. The local is unconditionally
                            // added to `modified` below, so all field output vars appear in
                            // the transition. Without a constraint, this field would be free.
                            if let Some((in_name, in_sort)) =
                                self.state_var_mgr.state_vars.get(dst_vec + i).cloned()
                            {
                                let in_var = Expr::var(&*in_name, in_sort);
                                acc.replace_constraint(fld_key, dst_var.eq(in_var));
                            }
                            flatten_copy_fallbacks += 1;
                            warn!(
                                local_idx,
                                field = i,
                                dst_sort = ?ds,
                                "CHC: flattened copy sort mismatch — self-loop emitted for field"
                            );
                        }
                    } else {
                        // Part of #3052: Source or destination slot missing.
                        // Emit a BoolConst(true) placeholder for #3038 invariant
                        // since modified.insert(local_idx) runs unconditionally below.
                        acc.replace_constraint(fld_key, Expr::bool_const(true));
                        flatten_copy_fallbacks += 1;
                    }
                }
                // Part of #3447: record sound fallback for sort mismatches and
                // missing slots so CTREX classification reports OverApproximation.
                for _ in 0..flatten_copy_fallbacks {
                    self.record_sound_fallback_reason("flatten_copy_sort_mismatch");
                }
                // Part of #3348: Propagate collection shadow state (present/len/cap)
                // for flattened local copies. Without this, struct copies like
                // `_7 = Move(_29)` where _29 contains a BTreeMap copy the data
                // array (fld0) but leave the presence/len shadow vars pointing
                // to the pre-insert version, causing false counterexamples.
                // The simple assign path (codegen_stmt_assign_simple.rs) has this
                // propagation but is unreachable for flattened locals.
                self.propagate_collection_shadow_state(src_idx, local_idx, acc.constraints);
                acc.modified.insert(local_idx);
                debug!(local_idx, src_idx, n, "CHC: copied flattened local ({n} scalar fields)");
                return true;
            }
        }

        // Pattern 5: Use(Copy/Move(src)) where src has field projections or src
        // is not itself flattened — translate the operand (which resolves field
        // projections on flattened sources to their scalar state vars) and
        // decompose into leaf values matching the destination's flattened layout.
        // Part of #3048: Without this, `_6 = Copy(_5.0)` where _5 is a flattened
        // struct and _6 is a flattened newtype leaves _6 unconstrained (spurious CTREX).
        if let Rvalue::Use(operand @ (Operand::Copy(_) | Operand::Move(_))) = rhs {
            if let Some(rhs_expr) = self.translate_operand_with_modified(operand, acc.modified) {
                let mut leaf_values = Vec::with_capacity(field_count);
                collect_leaf_exprs(&rhs_expr, &mut leaf_values);
                if leaf_values.len() == field_count {
                    self.constrain_flattened_fields(local_idx, &leaf_values, acc);
                    // Part of #3284: propagate collection ghost state (vec_len, vec_cap)
                    // through field projection on flattened locals.
                    if let Operand::Copy(src_place) | Operand::Move(src_place) = operand {
                        let src_field_idx = src_place.projection.iter().find_map(|p| {
                            if let ProjectionElem::Field(idx, _) = p { Some(*idx) } else { None }
                        });
                        if let Some(field_idx) = src_field_idx {
                            self.propagate_collection_ghost_through_projection(
                                local_idx,
                                &rhs_expr,
                                src_place.local,
                                field_idx,
                                acc.modified,
                                acc.constraints,
                            );
                        }
                    }
                    debug!(
                        local_idx,
                        field_count,
                        "CHC: assigned flattened local from projected source ({n} leaf fields)",
                        n = field_count
                    );
                    return true;
                }
                // Single-field newtypes: even if collect_leaf_exprs returns a
                // different count (e.g., expr is a non-decomposable DT), we can
                // still constrain directly when field_count == 1.
                if field_count == 1 {
                    self.constrain_flattened_fields(local_idx, &[Some(rhs_expr.clone())], acc);
                    debug!(
                        local_idx,
                        "CHC: assigned single-field flattened local from projected source"
                    );
                    return true;
                }
                // Part of #4022: multi-constructor enum → BV-flattened local.
                // Pattern 5 leaf decomposition can't handle ControlFlow/Result DTs.
                // Use build_flattened_destination_constraints which already chains
                // enum_bv_destination_values → bitvec_destination_values →
                // decompose_datatype → collect_leaf_exprs as a unified pipeline.
                if let Some(constraints) =
                    self.build_flattened_destination_field_constraints(local_idx, rhs_expr)
                {
                    // Part of #4068: register constraints via replace_constraint
                    // so last_constraint_for_local is updated. Without this,
                    // enforce_modified_constraint_invariant sees the local as
                    // modified but unconstrained, causing spurious fixups.
                    for (field_idx, c) in constraints {
                        let key = self.flattened_field_constraint_key(local_idx, field_idx);
                        acc.replace_constraint(key, c);
                    }
                    acc.modified.insert(local_idx);
                    debug!(
                        local_idx,
                        field_count,
                        "CHC: assigned flattened local via enum BV constraints (projected source)"
                    );
                    return true;
                }
            }
        }

        // Generic rvalue fallback: translate the rvalue and decompose into
        // leaf fields. Handles Cast (including Transmute), Ref, and other
        // non-Aggregate rvalue shapes that aren't covered by patterns 1-5.
        // Part of #3252: without this, transmute results assigned to flattened
        // struct locals (e.g., `[u8; 4]` → `Pair { u16, u16 }`) leave fields
        // unconstrained, causing spurious CTREX.
        if let Some(rhs_expr) =
            self.translate_rvalue_with_modified(rhs, acc.modified, Some(local_idx))
        {
            if field_count == 1 {
                self.constrain_flattened_fields(local_idx, &[Some(rhs_expr)], acc);
                debug!(local_idx, "CHC: assigned single-field flattened local from generic rvalue");
                return true;
            }
            let mut leaf_values = Vec::with_capacity(field_count);
            collect_leaf_exprs(&rhs_expr, &mut leaf_values);
            if leaf_values.len() == field_count {
                self.constrain_flattened_fields(local_idx, &leaf_values, acc);
                debug!(
                    local_idx,
                    field_count,
                    "CHC: assigned flattened local via rhs leaf decomposition (generic fallback)"
                );
                return true;
            }
            // Part of #4022: multi-constructor enum → BV-flattened local.
            // collect_leaf_exprs can't decompose multi-constructor DTs.
            // Use build_flattened_destination_constraints which chains
            // enum_bv → bitvec → dt_decompose → collect_leaf as a pipeline.
            if let Some(constraints) =
                self.build_flattened_destination_field_constraints(local_idx, rhs_expr)
            {
                // Part of #4068: use replace_constraint to update
                // last_constraint_for_local (see projected source fix above).
                for (field_idx, c) in constraints {
                    let key = self.flattened_field_constraint_key(local_idx, field_idx);
                    acc.replace_constraint(key, c);
                }
                acc.modified.insert(local_idx);
                debug!(
                    local_idx,
                    field_count,
                    "CHC: assigned flattened local via enum BV constraints (generic fallback)"
                );
                return true;
            }
        }

        false
    }

    /// Emit len/cap equality constraints when a flattened wrapper aggregate
    /// re-embeds a collection local.
    ///
    /// Part of #3348: iterator-backed Vec locals can already have precise len/cap
    /// ghost vars, but `Bits(vec_local)` only constrains the flattened leaf fields.
    /// The wrapper local's auxiliary len/cap vars would otherwise remain
    /// unconstrained and later `Bits::width()`-style queries lose the source length.
    pub(in crate::codegen_ay::chc) fn propagate_collection_len_cap_from_flattened_aggregate(
        &mut self,
        dest_local: usize,
        operands: &[Operand],
        constraints: &mut Vec<Expr>,
    ) {
        for operand in operands {
            let src_local = match operand {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    place.local
                }
                _ => continue,
            };

            if let Some(src_var) = self.collections.len_state.get_len_var(src_local).cloned()
                && let Some(dst_var) = self.collections.len_state.get_len_var(dest_local).cloned()
            {
                let sort = ptr_sort();
                let src_expr = if self.collections.len_state.modified_len_vars.contains(&*src_var) {
                    Expr::var(crate::codegen_ay::names::out_name(&src_var), sort.clone())
                } else {
                    Expr::var(&*src_var, sort.clone())
                };
                let dst_out = crate::codegen_ay::names::out_name(&dst_var);
                constraints.push(Expr::var(&dst_out, sort).eq(src_expr));
                self.mark_collection_len_modified(&dst_var);
            }

            if let Some(src_var) = self.collections.len_state.get_cap_var(src_local).cloned()
                && let Some(dst_var) = self.collections.len_state.get_cap_var(dest_local).cloned()
            {
                let sort = ptr_sort();
                let src_expr = if self.collections.len_state.modified_cap_vars.contains(&*src_var) {
                    Expr::var(crate::codegen_ay::names::out_name(&src_var), sort.clone())
                } else {
                    Expr::var(&*src_var, sort.clone())
                };
                let dst_out = crate::codegen_ay::names::out_name(&dst_var);
                constraints.push(Expr::var(&dst_out, sort).eq(src_expr));
                self.mark_collection_cap_modified(&dst_var);
            }
        }
    }
}

/// Recursively decompose a possibly-nested Datatype expression into leaf
/// scalar expressions.
///
/// When the expression is a `DatatypeConstructor` application, extracts
/// constructor arguments directly instead of emitting `field_select` wrappers.
/// This avoids injecting Datatype operations (e.g., `fld_0(Tuple_mk(x, y))`)
/// into CHC rules where PDR expects pure scalar constraints. The
/// `field_select` round-trip is semantically equivalent but PDR's invariant
/// synthesis cannot simplify it, causing spurious CTREX on nested tuples.
///
/// Part of #2970, #3037: enables recursively flattened struct aggregate
/// assignment where operands (e.g., `Point_mk(5, 6)`) need to be split into
/// individual leaf values (`[5, 6]`) matching the leaf state var layout.
pub(in crate::codegen_ay::chc) fn collect_leaf_exprs(expr: &Expr, out: &mut Vec<Option<Expr>>) {
    use ay_bindings::ExprValue;

    // Fast path: if the expression is already a DatatypeConstructor application,
    // extract the constructor arguments directly. This avoids the field_select
    // round-trip that produces Datatype operations in CHC rules.
    if let ExprValue::DatatypeConstructor { args, .. } = expr.value() {
        for arg in args {
            collect_leaf_exprs(arg, out);
        }
        return;
    }

    if let Some(dt) = expr.sort().datatype_sort() {
        if dt.constructors.len() == 1 {
            let cons = &dt.constructors[0];
            for field in &cons.fields {
                let field_expr =
                    expr.clone().field_select(&dt.name, &field.name, field.sort.clone());
                collect_leaf_exprs(&field_expr, out);
            }
            return;
        }
    }
    // Leaf (scalar or non-flattenable Datatype): add as-is.
    out.push(Some(expr.clone()));
}
