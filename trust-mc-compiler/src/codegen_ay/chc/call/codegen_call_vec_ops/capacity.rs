// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec capacity operations: VecReserve, VecReserveExact, VecShrinkToFit.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Operand;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::names::vec_layout;

use super::super::ChcCtx;
use super::super::codegen_call_vec::ChcVecFields;
use super::super::codegen_ctx::types::CollectionProjectionKind;
use super::shared::ProjectedVecState;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn preserve_vec_ptr_len_data(&self, vec_idx: usize, extra_constraints: &mut Vec<Expr>) {
        if let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(vec_idx).cloned()
            && let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        {
            let in_vec = Expr::var(&*in_name, in_sort);
            let out_vec = Expr::var(&*out_name, out_sort);
            let in_f = ChcVecFields::extract_without_name(in_vec);
            let out_f = ChcVecFields::extract_without_name(out_vec);
            if let (
                Some((in_ptr, in_len, _in_cap, in_data)),
                Some((out_ptr, out_len, _out_cap, out_data)),
            ) = (in_f, out_f)
            {
                extra_constraints.push(out_data.eq(in_data));
                extra_constraints.push(out_ptr.eq(in_ptr));
                extra_constraints.push(out_len.eq(in_len));
            }
        }
    }

    /// VecReserve / VecReserveExact: cap = max(cap, len + additional).
    pub(in crate::codegen_ay::chc) fn vec_op_reserve(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        // Cap state variable tracking (Path C). Part of #2877.
        if let Some(coll_local) = collection_local
            && args.len() >= 2
            && let Some(cap_var_name) = self.collections.len_state.get_cap_var(coll_local).cloned()
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
            && let Some(additional) =
                self.translate_operand_with_modified(&args[1], modified_locals)
        {
            let current_len = self.collection_current_len(&len_var_name);
            let current_cap = self.collection_current_cap(&cap_var_name);
            let required = current_len.clone().bvadd(additional);
            // Part of #3409: guard against unsigned overflow on len+additional.
            // Rust's Vec::reserve panics on capacity overflow (checked_add),
            // so assume no wraparound — blocks false PROOF from wrapped required.
            acc.constraints.push(required.clone().bvuge(current_len.clone()));
            let grow_needed = current_cap.clone().bvult(required.clone());
            let new_cap = Expr::ite(grow_needed, required, current_cap);
            self.collection_cap_set(&cap_var_name, new_cap.clone(), acc);
            // Part of #1037 V2: cap >= len background invariant on sidecar path.
            Self::emit_cap_ge_len(new_cap, current_len, acc.constraints);
        }
        if let Some(coll_local) = collection_local
            && args.len() >= 2
            && self.collections.projection_locals.get(&coll_local).copied()
                == Some(CollectionProjectionKind::Vec)
        {
            let additional = self.translate_operand_with_modified(&args[1], modified_locals);
            if let (Some((ptr, len, cap, data)), Some(additional)) =
                (self.extract_projected_vec_fields(coll_local, modified_locals), additional)
            {
                let required_cap = len.clone().bvadd(additional);
                // Part of #3409: guard against unsigned overflow on len+additional.
                acc.constraints.push(required_cap.clone().bvuge(len.clone()));
                let grow_needed = cap.clone().bvult(required_cap.clone());
                let new_cap = Expr::ite(grow_needed, required_cap, cap);
                // Part of #1037 V2: cap >= len background invariant on projected path.
                Self::emit_cap_ge_len(new_cap.clone(), len.clone(), acc.constraints);
                if !self.constrain_projected_vec_fields_for_call(
                    coll_local,
                    ProjectedVecState { ptr, len, cap: new_cap, data },
                    acc.constraints,
                    acc.dests,
                ) {
                    self.record_sound_fallback_reason("vec_field_constraint_not_emitted");
                }
            }
            return;
        }

        if let Some(coll_local) = collection_local
            && args.len() >= 2
            && let Some(vec_idx) = self.state_var_mgr.local_to_state_idx.get(&coll_local).copied()
        {
            let additional = self.translate_operand_with_modified(&args[1], modified_locals);
            // Read from current (possibly output) state for cap computation.
            let (name, sort) = if modified_locals.contains(&coll_local) {
                self.state_var_mgr.output_state_vars.get(vec_idx)
            } else {
                self.state_var_mgr.state_vars.get(vec_idx)
            }
            .cloned()
            .unzip();
            if let Some(name) = name
                && let Some(sort) = sort
                && let Some(additional) = additional
                && sort.datatype_name().is_some()
            {
                // Part of #2267: create Expr::var once instead of twice.
                let vec_in = Expr::var(&*name, sort);
                if Self::get_dt_field_sort(&vec_in, vec_layout::FLD_CAP).is_none() {
                    return;
                }
                if let Some(fields) = ChcVecFields::extract(vec_in) {
                    let ChcVecFields { vec_sort, ptr, len, cap, data } = fields;
                    let required_cap = len.clone().bvadd(additional);
                    // Part of #3409: guard against unsigned overflow on len+additional.
                    acc.constraints.push(required_cap.clone().bvuge(len.clone()));
                    let grow_needed = cap.clone().bvult(required_cap.clone());
                    let new_cap = Expr::ite(grow_needed, required_cap, cap);
                    // Part of #1037 V2: cap >= len background invariant on Datatype path.
                    Self::emit_cap_ge_len(new_cap.clone(), len.clone(), acc.constraints);
                    if let Some((out_name, out_sort)) =
                        self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
                    {
                        let dt_name = vec_sort
                            .datatype_name()
                            .expect("invariant: ChcVecFields::extract ensures datatype Vec sort");
                        acc.constraints.push(Self::build_vec_datatype_eq(
                            dt_name,
                            vec![ptr, len, new_cap, data],
                            &out_name,
                            &out_sort,
                        ));
                        acc.dests.push(vec_idx);
                    }
                    // Part of #1037 V3: explicit data/ptr/len preservation across reserve.
                    // Constrains that the output Vec's data, ptr, and len equal the
                    // input Vec's values. Reserve only changes capacity.
                    self.preserve_vec_ptr_len_data(vec_idx, acc.constraints);
                }
            }
        }
    }

    /// VecShrinkToFit: cap = len.
    pub(in crate::codegen_ay::chc) fn vec_op_shrink_to_fit(
        &mut self,
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        // Cap state variable tracking (Path C): cap = len. Part of #2877.
        if let Some(coll_local) = collection_local
            && let Some(cap_var_name) = self.collections.len_state.get_cap_var(coll_local).cloned()
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            let current_len = self.collection_current_len(&len_var_name);
            self.collection_cap_set(&cap_var_name, current_len, acc);
        }
        if let Some(coll_local) = collection_local
            && self.collections.projection_locals.get(&coll_local).copied()
                == Some(CollectionProjectionKind::Vec)
        {
            if let Some((ptr, len, _, data)) =
                self.extract_projected_vec_fields(coll_local, modified_locals)
            {
                if !self.constrain_projected_vec_fields_for_call(
                    coll_local,
                    ProjectedVecState { ptr, len: len.clone(), cap: len, data },
                    acc.constraints,
                    acc.dests,
                ) {
                    self.record_sound_fallback_reason("vec_field_constraint_not_emitted");
                }
            }
            return;
        }

        if let Some(coll_local) = collection_local
            && let Some(vec_idx) = self.state_var_mgr.local_to_state_idx.get(&coll_local).copied()
        {
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
                // Part of #2267: create Expr::var once instead of twice.
                let vec_in = Expr::var(&*name, sort);
                if Self::get_dt_field_sort(&vec_in, vec_layout::FLD_CAP).is_some() {
                    if let Some(fields) = ChcVecFields::extract(vec_in)
                        && let Some((out_name, out_sort)) =
                            self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
                    {
                        let ChcVecFields { vec_sort, ptr, len, cap: _, data } = fields;
                        let dt_name = vec_sort
                            .datatype_name()
                            .expect("invariant: ChcVecFields::extract ensures datatype Vec sort");
                        acc.constraints.push(Self::build_vec_datatype_eq(
                            dt_name,
                            vec![ptr, len.clone(), len, data],
                            &out_name,
                            &out_sort,
                        ));
                        acc.dests.push(vec_idx);
                    }
                    // Part of #1037 V3: explicit data/ptr/len preservation across shrink.
                    // ShrinkToFit only changes capacity (to len); data, ptr, and len
                    // are carried through from input to output.
                    self.preserve_vec_ptr_len_data(vec_idx, acc.constraints);
                }
            }
        }
    }
}
