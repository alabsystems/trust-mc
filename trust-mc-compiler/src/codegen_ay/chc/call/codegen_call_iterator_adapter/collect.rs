// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! IterCollect dispatch and Vec constraint threading.
//!
//! Extracted from `codegen_call_iterator_adapter` per #4129 (500 LOC threshold).

use ay_bindings::Expr;
use tracing::debug;

use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::{CtorFieldExt, ptr_sort};

use super::super::ChcCtx;
use super::super::call_accumulator::CallAccumulator;
use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_vec_ops::ProjectedVecState;
use super::super::codegen_ctx::globals::declare_pending_var;
use super::super::codegen_ctx::types::CollectionProjectionKind;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle IterCollect and thread the current result state through the extraction boundary.
    pub(in crate::codegen_ay::chc) fn codegen_iter_collect(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        dest_vec_idx: usize,
        flattened_result_fields: &mut Option<Vec<Option<Expr>>>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) -> Option<Expr> {
        let args = cx.args;
        let modified_locals = cx.modified_locals;
        let (iter_expr, iter_local) =
            self.iterator_receiver_expr_and_local(args, modified_locals)?;

        // Part of #3348: Iterator::collect(self) -> Vec<T>.
        // For VecIntoIter-based chains, extract the original Vec when pos == 0;
        // otherwise use symbolic Vec. Propagate remaining length to ghost vars.
        let remaining_len = self.try_extract_iterator_remaining_len(&iter_expr).or_else(|| {
            iter_local.and_then(|il| self.collections.adapter_remaining_len.get(&il).cloned())
        });
        if let Some(ref rl) = remaining_len {
            if let Some(len_var_name) = self.collections.len_state.get_len_var(dest_local).cloned()
            {
                self.collection_len_set(
                    &len_var_name,
                    rl.clone(),
                    &mut CallAccumulator::new(extra_constraints, extra_dests),
                );
            }
            if let Some(cap_var_name) = self.collections.len_state.get_cap_var(dest_local).cloned()
            {
                self.collection_cap_set(
                    &cap_var_name,
                    rl.clone(),
                    &mut CallAccumulator::new(extra_constraints, extra_dests),
                );
                Self::emit_cap_ge_len(rl.clone(), rl.clone(), extra_constraints);
            }
        }

        // Part of #3348: Look up adapter source data from the iterator chain.
        let adapter_src =
            iter_local.and_then(|il| self.collections.adapter_source_data.get(&il).cloned());
        let iterator_at_start = iter_local
            .is_some_and(|il| self.collections.adapter_at_start.contains(&il))
            || self.iterator_position_is_definitely_zero(&iter_expr);

        // Part of #3692: Override remaining_len with concrete element count
        // only when a replay path has pre-computed final output elements and
        // the iterator has not already consumed part of that sequence.
        let remaining_len = if let Some(ref src) = adapter_src
            && let Some(ref elems) = src.concrete_elems
            && !src.has_transform
            && iterator_at_start
        {
            let concrete_len =
                Expr::bitvec_const(elems.len() as u128, crate::codegen_ay::types::POINTER_WIDTH);
            // Re-set ghost vars with the concrete length.
            if let Some(len_var_name) = self.collections.len_state.get_len_var(dest_local).cloned()
            {
                self.collection_len_set(
                    &len_var_name,
                    concrete_len.clone(),
                    &mut CallAccumulator::new(extra_constraints, extra_dests),
                );
            }
            if let Some(cap_var_name) = self.collections.len_state.get_cap_var(dest_local).cloned()
            {
                self.collection_cap_set(
                    &cap_var_name,
                    concrete_len.clone(),
                    &mut CallAccumulator::new(extra_constraints, extra_dests),
                );
            }
            Some(concrete_len)
        } else {
            remaining_len
        };

        // Try to extract the original Vec from VecIntoIter-based chains.
        if let Some(vec_result) = self.try_collect_vec_from_iterator(&iter_expr) {
            return Some(vec_result);
        }

        if let Some(ref rl) = remaining_len {
            // Part of #3381: Build a len-constrained Vec instead of
            // fully symbolic. When map/filter adapters wrap the iterator,
            // try_collect_vec_from_iterator fails (it only handles
            // direct VecIntoIter). The sidecar ghost vars are constrained
            // above, but the Vec Datatype's fld_len is unconstrained in
            // a fresh symbolic, causing false CTREX when struct-embedded
            // VecLen reads fld_len directly.
            let is_projected = self.collections.projection_locals.get(&dest_local).copied();
            if is_projected == Some(CollectionProjectionKind::Vec) {
                // Flattened Vec: constrain ptr/len/cap/data individually.
                let ptr = declare_pending_var(format!("iter_collect_ptr_{dest_local}"), ptr_sort());
                let data_sort = self
                    .state_var_mgr
                    .output_state_vars
                    .get(dest_vec_idx + vec_layout::IDX_DATA)
                    .map(|(_, s)| s.clone())
                    .unwrap_or_else(|| ay_bindings::Sort::array(ptr_sort(), ptr_sort()));

                // Part of #3348: Use adapter source data to constrain
                // the collected Vec's data array. For transform chains
                // with a translated closure, build a forall constraint:
                //   forall idx: idx < len -> select(result, idx) = closure(src[idx])
                // For identity chains, set result_data = source_data directly.
                let data = self.try_constrain_iter_collect_data(
                    dest_local,
                    &data_sort,
                    rl,
                    adapter_src.as_ref(),
                    iterator_at_start,
                    extra_constraints,
                );

                Self::emit_cap_ge_len(rl.clone(), rl.clone(), extra_constraints);
                if !self.constrain_projected_vec_fields_for_call(
                    dest_local,
                    ProjectedVecState { ptr, len: rl.clone(), cap: rl.clone(), data },
                    extra_constraints,
                    extra_dests,
                ) {
                    self.record_sound_fallback_reason("vec_field_constraint_not_emitted");
                }
                // Mark flattened result as handled so the fallback
                // doesn't create a second symbolic assignment.
                *flattened_result_fields = Some(Vec::new());
                debug!(
                    fn_name = %self.fn_name,
                    dest_local,
                    "IterCollect: built len-constrained projected Vec (#3348/#3381)"
                );
            } else if let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
                && let Some(dt) = out_sort.datatype_sort()
                && dt.constructors.first().is_some_and(|c| c.has_field(vec_layout::FLD_LEN))
            {
                // Non-flattened Datatype Vec: build Vec(ptr, len, cap, data).
                let dt_name = out_sort.datatype_name().expect("has datatype_sort");
                let ptr = declare_pending_var(format!("iter_collect_ptr_{dest_local}"), ptr_sort());
                let data_sort = dt
                    .constructors
                    .first()
                    .and_then(|c| c.field_sort(vec_layout::FLD_DATA))
                    .unwrap_or_else(|| ay_bindings::Sort::array(ptr_sort(), ptr_sort()));

                // Part of #3348: Use adapter source data to constrain
                // the collected Vec's data array (non-flattened path).
                let data = self.try_constrain_iter_collect_data(
                    dest_local,
                    &data_sort,
                    rl,
                    adapter_src.as_ref(),
                    iterator_at_start,
                    extra_constraints,
                );

                Self::emit_cap_ge_len(rl.clone(), rl.clone(), extra_constraints);
                extra_constraints.push(Self::build_vec_datatype_eq(
                    dt_name,
                    vec![ptr, rl.clone(), rl.clone(), data],
                    &out_name,
                    &out_sort,
                ));
                extra_dests.push(dest_local);
                // Set result as handled so the output-arg path
                // doesn't produce a contradictory assignment.
                *flattened_result_fields = Some(Vec::new());
                debug!(
                    fn_name = %self.fn_name,
                    dest_local,
                    "IterCollect: built len-constrained Datatype Vec (#3381)"
                );
            }
        }

        None
    }
}
