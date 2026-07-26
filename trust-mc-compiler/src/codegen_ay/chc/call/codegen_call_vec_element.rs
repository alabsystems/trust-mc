// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec element mutation operations: Push and Pop.
//!
//! Extracted from `codegen_call_vec.rs` per #2884 (500 LOC threshold).

use std::collections::HashSet;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{Operand, Place, ProjectionElem};
use tracing::debug;

use crate::args::ChcTrackLevel;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

use super::ChcCtx;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_ctx::types::CollectionProjectionKind;
use super::stubs_option_helpers::OptionHelpers;

use super::codegen_call_vec::ChcVecFields;

/// Parameter bundle for `vec_op_pop`.
///
/// Part of #2381: remove local `too_many_arguments` suppression by grouping
/// destination/local state parameters into a typed context.
pub(in crate::codegen_ay::chc) struct VecPopContext<'a> {
    pub(in crate::codegen_ay::chc) modified_locals: &'a HashSet<usize>,
    pub(in crate::codegen_ay::chc) collection_local: Option<usize>,
    pub(in crate::codegen_ay::chc) field_projections: &'a [ProjectionElem],
    pub(in crate::codegen_ay::chc) dest_local: usize,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// VecPush: len += 1, data[old_len] = val.
    pub(in crate::codegen_ay::chc) fn vec_op_push(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        field_projections: &[ProjectionElem],
        acc: &mut CallAccumulator<'_>,
    ) {
        // Part of #3084: When field_projections is non-empty, collection_local
        // is a struct containing Vec fields. The sidecar len_var belongs to the
        // struct (or a sibling Vec), not the projected Vec field. Skip the
        // sidecar path and fall through to the struct-embedded handler which
        // navigates the Datatype to the correct Vec field.
        let old_len_for_store = if !field_projections.is_empty() {
            None
        } else if let Some(coll_local) = collection_local
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            let old_len = self.collection_current_len(&len_var_name);
            let new_len = old_len.clone().bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH));
            self.collection_len_set(&len_var_name, new_len.clone(), acc);
            // Capacity growth on push (#2877): cap = max(cap, new_len).
            if let Some(cap_var_name) = self.collections.len_state.get_cap_var(coll_local).cloned()
            {
                let old_cap = self.collection_current_cap(&cap_var_name);
                let grow_needed = old_cap.clone().bvult(new_len.clone());
                let grown_cap = Expr::ite(grow_needed, new_len.clone(), old_cap);
                self.collection_cap_set(&cap_var_name, grown_cap.clone(), acc);
                // Part of #1037 V2: cap >= len background invariant on sidecar path.
                acc.constraints.push(grown_cap.bvuge(new_len));
            }
            Some(old_len)
        } else {
            None
        };

        // Update the Vec's fld_data backing array: data_out = store(data, old_len, val).
        if let Some(ref old_len) = old_len_for_store
            && args.len() >= 2
            && let Some(coll_local) = collection_local
            && let Some(val) = self.translate_operand_with_modified(&args[1], modified_locals)
        {
            // Projected path (#2874): Vec flattened into scalar fields.
            // This does not require local_to_state_idx and must run even when the
            // aggregate Vec local itself is not state-tracked.
            if self.collections.projection_locals.get(&coll_local).copied()
                == Some(CollectionProjectionKind::Vec)
            {
                let ptr_field = self.flattened_local_field_expr(coll_local, 0, modified_locals);
                let data_field = self.flattened_local_field_expr(coll_local, 3, modified_locals);
                let len_field = self.flattened_local_field_expr(coll_local, 1, modified_locals);
                let cap_field = self.flattened_local_field_expr(coll_local, 2, modified_locals);
                if let (Some(old_ptr), Some(old_len_field), Some(old_cap), Some(old_data)) =
                    (ptr_field, len_field, cap_field, data_field)
                    && old_data.sort().is_array()
                {
                    let val =
                        super::codegen_call_vec_ops::coerce_array_element(val, &old_data.sort());
                    let new_data = old_data.store(old_len.clone(), val);
                    let new_fld_len = old_len_field.bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH));
                    // Mirror sidecar cap growth semantics (max(cap, new_len)) so
                    // projected Vec state stays reachable at len==cap boundaries.
                    let grow_needed = old_cap.clone().bvult(new_fld_len.clone());
                    let new_fld_cap = Expr::ite(grow_needed, new_fld_len.clone(), old_cap.clone());
                    let new_ptr = self.allocate_vec_backing_on_zero_cap_growth(
                        old_ptr,
                        &old_cap,
                        &new_fld_cap,
                        Some(self.body.locals()[coll_local].ty),
                        acc.constraints,
                    );
                    // Part of #1037 V2: cap >= len background invariant on projected path.
                    acc.constraints.push(new_fld_cap.clone().bvuge(new_fld_len.clone()));
                    let emitted = self.constrain_flattened_fields_for_call(
                        coll_local,
                        &[Some(new_ptr), Some(new_fld_len), Some(new_fld_cap), Some(new_data)],
                        acc.constraints,
                    );
                    if emitted {
                        acc.dests.push(coll_local);
                    }
                    debug!(
                        fn_name = %self.fn_name,
                        "VecPush: projected path — updated ptr/len/cap/data fields (#2874)"
                    );
                }
                return;
            }

            let vec_idx = self
                .ref_resolution
                .ref_arg_pointee_idx
                .get(&coll_local)
                .copied()
                .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied());
            if let Some(vec_idx) = vec_idx {
                let vec_input = self
                    .state_var_mgr
                    .state_vars
                    .get(vec_idx)
                    .map(|(name, sort)| Expr::var(&**name, sort.clone()));
                if let Some(vec_in) = vec_input
                    && vec_in.sort().datatype_name().is_some()
                    && Self::get_dt_field_sort(&vec_in, vec_layout::FLD_DATA)
                        .is_some_and(|s| s.is_array())
                {
                    // Datatype path: extract all fields, store, reconstruct.
                    if let Some(fields) = ChcVecFields::extract(vec_in) {
                        let ChcVecFields { vec_sort, ptr, len, cap, data } = fields;
                        let val =
                            super::codegen_call_vec_ops::coerce_array_element(val, &data.sort());
                        let new_data = data.store(old_len.clone(), val);
                        let new_len_field = len.bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH));
                        let grow_needed = cap.clone().bvult(new_len_field.clone());
                        let new_cap_field =
                            Expr::ite(grow_needed, new_len_field.clone(), cap.clone());
                        let new_ptr = self.allocate_vec_backing_on_zero_cap_growth(
                            ptr,
                            &cap,
                            &new_cap_field,
                            Some(self.body.locals()[coll_local].ty),
                            acc.constraints,
                        );
                        // Part of #1037 V2: cap >= len background invariant.
                        // Datatype path now mirrors sidecar/projected growth
                        // semantics (cap = max(cap, new_len)).
                        acc.constraints.push(new_cap_field.clone().bvuge(new_len_field.clone()));
                        if let Some((out_name, out_sort)) =
                            self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
                        {
                            let dt_name = vec_sort.datatype_name().expect(
                                "invariant: ChcVecFields::extract ensures datatype Vec sort",
                            );
                            acc.constraints.push(Self::build_vec_datatype_eq(
                                dt_name,
                                vec![new_ptr, new_len_field, new_cap_field, new_data],
                                &out_name,
                                &out_sort,
                            ));
                            acc.dests.push(vec_idx);
                        }
                    }
                    debug!(
                        fn_name = %self.fn_name,
                        "VecPush: stored value into fld_data at index old_len"
                    );
                }
            }
            return;
        }

        // Path 3: Struct-embedded Vec push.
        // When collection_local is a struct (no sidecar len_var) and field_projections
        // describe the path from struct to Vec, extract the Vec from the struct's
        // state var and perform push directly on its fields.
        // Part of #3348: handles patterns like `m.indices.push(var)` where `m` is a struct.
        if old_len_for_store.is_none()
            && !field_projections.is_empty()
            && args.len() >= 2
            && let Some(coll_local) = collection_local
            && let Some(val) = self.translate_operand_with_modified(&args[1], modified_locals)
        {
            self.vec_push_struct_embedded(
                coll_local,
                field_projections,
                val,
                modified_locals,
                acc.constraints,
                acc.dests,
            );
        }
    }

    /// VecPop: len = max(len - 1, 0), dest = ITE(nonempty, Some(data[len-1]), None).
    pub(in crate::codegen_ay::chc) fn build_vec_pop_option_result(
        &self,
        old_data: Expr,
        elem_sort: Sort,
        is_nonempty: Expr,
        new_len: Expr,
    ) -> Option<Expr> {
        let popped_value = old_data.select(new_len);
        let opt_sort = super::stubs_option_helpers::make_option_sort(&elem_sort);
        let some_expr = self.make_some_expr_for_option(popped_value, &opt_sort)?;
        let none_expr = self.make_none_expr(&elem_sort);
        Some(Expr::ite(is_nonempty, some_expr, none_expr))
    }

    pub(in crate::codegen_ay::chc) fn bind_vec_pop_destination(
        &mut self,
        dest_local: usize,
        modified_locals: &HashSet<usize>,
        option_result: Expr,
        constraints: &mut Vec<Expr>,
    ) -> bool {
        let bound = if let Some(flat_constraints) =
            self.build_flattened_destination_constraints(dest_local, option_result.clone())
        {
            let emitted = flat_constraints
                .iter()
                .any(|constraint| !matches!(constraint.value(), ExprValue::BoolConst(true)));
            constraints.extend(flat_constraints);
            emitted
        } else if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                option_result.clone(),
                dest_var.sort(),
                dest_local,
                "codegen_call_vec_core::VecPop",
            ) {
                constraints.push(eq);
                true
            } else {
                false
            }
        } else {
            false
        };

        if bound && self.track_level >= ChcTrackLevel::Mem {
            let local_place = Place { local: dest_local, projection: vec![] };
            if let Some(addr_expr) = self.translate_ref_to_address(&local_place, modified_locals) {
                let local_ty = self.body.locals()[dest_local].ty;
                if let Some(store_constraint) =
                    self.build_memory_store(addr_expr, option_result, local_ty)
                {
                    constraints.push(store_constraint);
                }
                constraints.append(&mut self.heap_state.pending_updates);
                constraints.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
            }
        }

        bound
    }

    pub(in crate::codegen_ay::chc) fn vec_op_pop(
        &mut self,
        pop: VecPopContext<'_>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let VecPopContext { modified_locals, collection_local, field_projections, dest_local } =
            pop;
        let mut dest_bound = false;

        if let Some(coll_local) = collection_local {
            if !field_projections.is_empty() {
                dest_bound = self.vec_pop_struct_embedded(
                    coll_local,
                    field_projections,
                    dest_local,
                    modified_locals,
                    acc,
                );
            } else if let Some(len_var_name) =
                self.collections.len_state.get_len_var(coll_local).cloned()
            {
                let old_len = self.collection_current_len(&len_var_name);
                let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                let is_nonempty = old_len.clone().ne(zero.clone());
                let new_len = Expr::ite(is_nonempty.clone(), old_len.bvsub(one), zero);
                self.collection_len_set(&len_var_name, new_len.clone(), acc);
                // Part of #1037 V2: cap >= len background invariant on sidecar path.
                if let Some(cap_var_name) =
                    self.collections.len_state.get_cap_var(coll_local).cloned()
                {
                    let current_cap = self.collection_current_cap(&cap_var_name);
                    acc.constraints.push(current_cap.bvuge(new_len.clone()));
                }

                if let Some(vec_idx) = self
                    .ref_resolution
                    .ref_arg_pointee_idx
                    .get(&coll_local)
                    .copied()
                    .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied())
                {
                    let vec_input = self
                        .state_var_mgr
                        .state_vars
                        .get(vec_idx)
                        .map(|(name, sort)| Expr::var(&**name, sort.clone()));
                    if let Some(vec_in) = vec_input {
                        if vec_in.sort().datatype_name().is_some()
                            && Self::get_dt_field_sort(&vec_in, vec_layout::FLD_DATA)
                                .is_some_and(|s| s.is_array())
                        {
                            if let Some(fields) = ChcVecFields::extract(vec_in) {
                                let ChcVecFields { vec_sort, ptr, len: _, cap, data } = fields;
                                let elem_sort = data
                                    .sort()
                                    .array_sort()
                                    .map_or_else(ptr_sort, |a| a.element_sort.clone());
                                if let Some(option_result) = self.build_vec_pop_option_result(
                                    data.clone(),
                                    elem_sort,
                                    is_nonempty,
                                    new_len.clone(),
                                ) {
                                    dest_bound = self.bind_vec_pop_destination(
                                        dest_local,
                                        modified_locals,
                                        option_result,
                                        acc.constraints,
                                    );
                                }
                                debug!(
                                    fn_name = %self.fn_name,
                                    "VecPop: dest = ITE(nonempty, Some(data[new_len]), None)"
                                );

                                // Reconstruct Vec datatype with decremented fld_len.
                                // Part of #1037 V2: cap >= len background invariant.
                                acc.constraints.push(cap.clone().bvuge(new_len.clone()));
                                if let Some((out_name, out_sort)) =
                                    self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
                                {
                                    let dt_name = vec_sort.datatype_name().expect(
                                        "invariant: ChcVecFields::extract ensures datatype Vec sort",
                                    );
                                    acc.constraints.push(Self::build_vec_datatype_eq(
                                        dt_name,
                                        vec![ptr, new_len, cap, data],
                                        &out_name,
                                        &out_sort,
                                    ));
                                    acc.dests.push(vec_idx);
                                    debug!(
                                        fn_name = %self.fn_name,
                                        "VecPop: reconstructed Vec datatype with decremented fld_len (#2852)"
                                    );
                                }
                            }
                        } else if self.collections.projection_locals.get(&coll_local).copied()
                            == Some(CollectionProjectionKind::Vec)
                        {
                            // Projected path (#2874).
                            let ptr_field =
                                self.flattened_local_field_expr(coll_local, 0, modified_locals);
                            let cap_field =
                                self.flattened_local_field_expr(coll_local, 2, modified_locals);
                            let data_field =
                                self.flattened_local_field_expr(coll_local, 3, modified_locals);
                            if let Some(old_data) = data_field
                                && old_data.sort().is_array()
                            {
                                let elem_sort = old_data
                                    .sort()
                                    .array_sort()
                                    .map_or_else(ptr_sort, |a| a.element_sort.clone());
                                if let Some(option_result) = self.build_vec_pop_option_result(
                                    old_data.clone(),
                                    elem_sort,
                                    is_nonempty,
                                    new_len.clone(),
                                ) {
                                    dest_bound = self.bind_vec_pop_destination(
                                        dest_local,
                                        modified_locals,
                                        option_result,
                                        acc.constraints,
                                    );
                                }

                                // Constrain all 4 Vec fields: ptr (unchanged), len (decremented),
                                // cap (unchanged), data (unchanged). Without this, the solver
                                // treats unconstrained output fields as free variables, causing
                                // spurious CTREX on subsequent index operations.
                                // Part of #1037 V2: cap >= len background invariant.
                                if let Some(old_cap) = cap_field.clone() {
                                    acc.constraints.push(old_cap.bvuge(new_len.clone()));
                                }
                                let emitted = self.constrain_flattened_fields_for_call(
                                    coll_local,
                                    &[ptr_field, Some(new_len), cap_field, Some(old_data)],
                                    acc.constraints,
                                );
                                if emitted {
                                    acc.dests.push(coll_local);
                                }
                                debug!(
                                    fn_name = %self.fn_name,
                                    "VecPop: projected path — updated all fields (ptr/len/cap/data)"
                                );
                            }
                        }
                    }
                }
            }
        }

        if dest_bound {
            acc.dests.push(dest_local);
        }
    }
}
