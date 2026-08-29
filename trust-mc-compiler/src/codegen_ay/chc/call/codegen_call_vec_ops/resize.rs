// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec resize operation and the resize-array quantifier helper.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Operand, ProjectionElem};

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

use super::super::codegen_call_misc::CallMisc;

use super::super::ChcCtx;
use super::super::codegen_call_vec::ChcVecFields;
use super::super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::super::codegen_ctx::types::CollectionProjectionKind;
use super::shared::{ProjectedVecState, coerce_array_element};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// VecResize: `resize(&mut self, new_len, value)`.
    ///
    /// Model: len' = new_len, cap' = max(cap, new_len).
    /// On growth (new_len > old_len): introduce a fresh backing array linked by
    /// quantified constraints that preserve the old prefix and, when available,
    /// constrain the new suffix to the resize fill value. This blocks
    /// store→resize→load false proofs (#3647) without discarding all data.
    /// On shrink/same: data preserved (no realloc).
    /// Part of #3348, #3647.
    pub(in crate::codegen_ay::chc) fn vec_op_resize(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        field_projections: &[ProjectionElem],
        acc: &mut CallAccumulator<'_>,
    ) {
        // args[0] = &mut self, args[1] = new_len: usize, args[2] = value: T
        let new_len = args
            .get(1)
            .and_then(|a| self.translate_operand_with_modified(a, modified_locals))
            .unwrap_or_else(|| Expr::bitvec_const(0u64, POINTER_WIDTH));

        // Part of #3647: Invalidate store-to-load forwarding on resize.
        // Forwarded values from before the resize must not bypass data array
        // invalidation (the store→resize→load false proof path).
        self.heap_state.invalidate_store_forwards();

        // Task #69: every modeling path below requires the collection local.
        // Without it the whole call silently becomes a no-op transition (stale
        // len/cap/data persist), so a shrink-then-index real OOB can prove
        // Safe. Record a fail-closed marker instead of exiting silently.
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_resize_no_local");
            return;
        };

        // Sidecar len/cap tracking
        let mut sidecar_len_modeled = false;
        if let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() {
            self.collection_len_set(&len_var, new_len.clone(), acc);
            sidecar_len_modeled = true;
        }
        if let Some(cap_var) = self.collections.len_state.get_cap_var(coll_local).cloned() {
            let current_cap = self.collection_current_cap(&cap_var);
            let grow_needed = current_cap.clone().bvult(new_len.clone());
            let new_cap = Expr::ite(grow_needed, new_len.clone(), current_cap);
            self.collection_cap_set(&cap_var, new_cap.clone(), acc);
            Self::emit_cap_ge_len(new_cap, new_len.clone(), acc.constraints);
        }

        let fill_value = args.get(2).and_then(|a| {
            self.translate_operand_with_modified(a, modified_locals)
                .or_else(|| self.resolve_ref_or_const_referent(a, modified_locals))
        });

        // Projected path: preserve data + ptr, update len + cap
        if self.collections.projection_locals.get(&coll_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            if let Some((ptr, old_len, cap, data)) =
                self.extract_projected_vec_fields(coll_local, modified_locals)
            {
                let grow_needed = cap.clone().bvult(new_len.clone());
                let new_cap = Expr::ite(grow_needed, new_len.clone(), cap);
                Self::emit_cap_ge_len(new_cap.clone(), new_len.clone(), acc.constraints);
                let (out_data, resize_relation, modeled_fill) =
                    quantified_resize_growth_array(data, old_len, new_len.clone(), fill_value);
                acc.constraints.push(resize_relation);
                if !modeled_fill {
                    // Part of #3447: resize growth without a translated fill value
                    // still over-approximates the new suffix as unconstrained.
                    self.record_aggregate_gap("vec_resize_growth_no_fill_projected");
                }
                if !self.constrain_projected_vec_fields_for_call(
                    coll_local,
                    ProjectedVecState { ptr, len: new_len, cap: new_cap, data: out_data },
                    acc.constraints,
                    acc.dests,
                ) {
                    self.record_sound_fallback_reason("vec_field_constraint_not_emitted");
                }
            } else {
                // Task #69: projected-Vec field extraction failed — the four
                // flat slots (ptr/len/cap/data) stay stale across the resize.
                self.record_sound_fallback_reason("vec_resize_state_unmodeled");
            }
            return;
        }

        // Datatype path: build new Vec with updated len/cap, preserved data/ptr
        let mut datatype_entered = false;
        let mut datatype_modeled = false;
        if let Some(vec_idx) = self.state_var_mgr.local_to_state_idx.get(&coll_local).copied() {
            datatype_entered = true;
            let (name, sort) = if modified_locals.contains(&coll_local) {
                self.state_var_mgr.output_state_vars.get(vec_idx)
            } else {
                self.state_var_mgr.state_vars.get(vec_idx)
            }
            .cloned()
            .unzip();
            if let Some(name) = name
                && let Some(sort) = sort
                && sort.datatype_name().is_some()
            {
                let vec_in = Expr::var(&*name, sort);
                if let Some(fields) = ChcVecFields::extract(vec_in) {
                    let ChcVecFields { vec_sort, ptr, len: old_len, cap, data } = fields;
                    let grow_needed = cap.clone().bvult(new_len.clone());
                    let new_cap = Expr::ite(grow_needed, new_len.clone(), cap);
                    Self::emit_cap_ge_len(new_cap.clone(), new_len.clone(), acc.constraints);
                    let (out_data, resize_relation, modeled_fill) =
                        quantified_resize_growth_array(data, old_len, new_len.clone(), fill_value);
                    acc.constraints.push(resize_relation);
                    if !modeled_fill {
                        // Part of #3447: resize growth without a translated fill value
                        // still over-approximates the new suffix as unconstrained.
                        self.record_aggregate_gap("vec_resize_growth_no_fill_dt");
                    }
                    if let Some((out_name, out_sort)) =
                        self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
                    {
                        let dt_name = vec_sort
                            .datatype_name()
                            .expect("invariant: ChcVecFields::extract ensures datatype Vec sort");
                        acc.constraints.push(Self::build_vec_datatype_eq(
                            dt_name,
                            vec![ptr, new_len.clone(), new_cap, out_data],
                            &out_name,
                            &out_sort,
                        ));
                        // Task #69 (dests index-space fix): `vec_idx` is a
                        // STATE-VAR index, but `acc.dests` entries are read as
                        // MIR locals by `build_output_args` (see the contract in
                        // codegen_call_coerce.rs). Pushing it there left the
                        // constrained `__out` var out of the rule head, so the
                        // Vec state var stayed stale (fld_len kept the
                        // pre-resize length). Route through
                        // `mark_state_var_modified` — the documented channel
                        // for raw state-vector slots.
                        self.mark_state_var_modified(vec_idx);
                        datatype_modeled = true;
                    }
                }
            }
        }

        // Path 3: Struct-embedded Vec resize.
        // When collection_local is a struct and field_projections describe the
        // path from struct to Vec, extract the Vec from the struct's state var
        // and perform resize on its fields.
        // Part of #3647: struct-embedded Vec resize false proof.
        let mut struct_modeled = false;
        if !field_projections.is_empty() {
            struct_modeled = self.vec_resize_struct_embedded(
                coll_local,
                args,
                field_projections,
                new_len,
                modified_locals,
                acc.constraints,
                acc.dests,
            );
        }

        // Task #69: partial-failure attribution. If a Vec-shaped state var (or
        // struct-embedded Vec) exists but was not updated, readers of that
        // state see the stale pre-resize Vec — record a fail-closed marker. If
        // no structural representation exists at all and the sidecar len was
        // also missing, the resize modeled nothing (silent no-op).
        if !datatype_modeled && !struct_modeled {
            if datatype_entered || !field_projections.is_empty() {
                self.record_sound_fallback_reason("vec_resize_state_unmodeled");
            } else if !sidecar_len_modeled {
                self.record_sound_fallback_reason("vec_resize_no_len");
            }
        }
    }
}

/// Largest literal `new_len` that may be written as an explicit `store` chain
/// instead of the quantified relation. Each slot costs one array `store`; the
/// cap keeps a `resize(10_000, x)` from unrolling.
const MAX_UNROLLED_RESIZE_LEN: u64 = 64;

/// How many ground index instances of the quantified resize relation to spell
/// out when the lengths are not literals. Each instance is implied by the
/// `forall` it accompanies, so this trades VC size for the derivation's ability
/// to use the relation at all.
const GROUND_RESIZE_INSTANCES: u64 = 32;

/// The literal value of a bitvector constant, if `e` is one.
fn bitvec_const_u64(e: &Expr) -> Option<u64> {
    match e.value() {
        ay_bindings::ExprValue::BitVecConst { value, .. } => u64::try_from(value).ok(),
        _ => None,
    }
}

pub(in crate::codegen_ay::chc) fn quantified_resize_growth_array(
    data: Expr,
    old_len: Expr,
    new_len: Expr,
    fill_value: Option<Expr>,
) -> (Expr, Expr, bool) {
    let Some(data_arr) = data.sort().array_sort() else {
        return (data, Expr::bool_const(true), true);
    };

    let fill_value = fill_value
        .map(|fill| coerce_array_element(fill, &data.sort()))
        .filter(|fill| fill.sort() == &data_arr.element_sort);
    let modeled_fill = fill_value.is_some();

    // Preferred form: say the whole thing in the array theory's own vocabulary.
    //
    // The quantified relation further down states the resize correctly, but a
    // `forall` in a CHC RULE BODY is outside what the solver's CHC portfolio
    // discharges — it answers `unknown` on the quantified query, and the
    // in-process derivation treats the premise as non-constraining, so
    // `v.resize(4, p); assert!(v[3] == p)` reports a counterexample against a
    // true assertion. One `store` per slot below the new length carries the
    // same fact quantifier-free, and carries it more precisely: `store`
    // preserves every other index by definition, so the prefix needs no
    // premise and no fresh array is introduced at all.
    if let Some(new) = bitvec_const_u64(&new_len)
        && new <= MAX_UNROLLED_RESIZE_LEN
        && let Some(fill) = fill_value.clone()
    {
        // Each slot holds the value it has AFTER the resize: the old element
        // while the index is still inside the old length, the fill value once
        // past it. Indices at or above `new_len` are untouched. This covers
        // growth AND shrink — when `old_len >= new_len` every guard is false
        // and the result is `data` element-for-element.
        let mut out = data.clone();
        for slot in 0..new {
            let idx = Expr::bitvec_const(i128::from(slot), POINTER_WIDTH);
            let grown = idx.clone().bvuge(old_len.clone());
            let kept = data.clone().select(idx.clone());
            out = out.store(idx, Expr::ite(grown, fill.clone(), kept));
        }
        return (out, Expr::bool_const(true), true);
    }

    let fresh = declare_pending_var(chc_fresh_name("__resize_data"), data.sort().clone());
    let idx_name = chc_fresh_name("__resize_idx");
    let idx_sort = ptr_sort();

    // The relation, stated at one index. Used for the bound variable and again
    // for each ground index below.
    let body_at = |at: &Expr| {
        let prefix_eq = fresh.clone().select(at.clone()).eq(data.clone().select(at.clone()));
        let mut body = at.clone().bvult(old_len.clone()).implies(prefix_eq);
        if let Some(fill) = &fill_value {
            let in_grown_suffix =
                at.clone().bvuge(old_len.clone()).and(at.clone().bvult(new_len.clone()));
            let fill_eq = fresh.clone().select(at.clone()).eq(fill.clone());
            body = body.and(in_grown_suffix.implies(fill_eq));
        }
        body
    };

    let idx = Expr::var(&idx_name, idx_sort.clone());
    let mut resize_relation = Expr::forall(vec![(idx_name, idx_sort)], body_at(&idx));
    // The lengths are not literal here, so the slot count is unknown and the
    // `store` chain above does not apply. Spell the relation out at the low
    // ground indices anyway: these are instances of the `forall` just above, so
    // they add no assumption the resize does not already make, and they are the
    // instances a derivation that skips the quantifier would otherwise miss.
    for slot in 0..GROUND_RESIZE_INSTANCES {
        let at = Expr::bitvec_const(i128::from(slot), POINTER_WIDTH);
        resize_relation = resize_relation.and(body_at(&at));
    }

    let is_growing = old_len.bvult(new_len);
    (Expr::ite(is_growing, fresh, data), resize_relation, modeled_fill)
}
