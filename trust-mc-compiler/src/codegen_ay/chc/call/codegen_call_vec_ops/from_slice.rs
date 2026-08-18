// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VecFromSlice (slice::to_vec): rebuild an owned Vec from borrowed slice backing.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::{CtorFieldExt, ptr_sort};

use super::super::ChcCtx;
use super::super::codegen_call_slice_helpers::SLICE_BACKING_REBASE_MAX_ELEMS;
use super::super::codegen_ctx::globals::declare_pending_var;
use super::super::codegen_ctx::types::CollectionProjectionKind;
use super::shared::ProjectedVecState;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn vec_from_slice_input_len(&self, args: &[Operand]) -> Option<Expr> {
        if let Some(Operand::Copy(place) | Operand::Move(place)) = args.first() {
            let ref_local = place.local;
            self.ref_resolution.subslice_len.get(&ref_local).cloned().or_else(|| {
                let resolved = self
                    .ref_resolution
                    .ref_targets
                    .get(&ref_local)
                    .map_or(ref_local, |rt| rt.local);
                self.ref_resolution.subslice_len.get(&resolved).cloned().or_else(|| {
                    self.collections
                        .len_state
                        .get_len_var(resolved)
                        .cloned()
                        .map(|lv| self.collection_current_len(&lv))
                })
            })
        } else {
            None
        }
    }

    /// VecFromSlice / slice::to_vec(): rebuild an owned Vec from borrowed slice backing.
    pub(in crate::codegen_ay::chc) fn vec_op_from_slice(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        dest_local: usize,
        dest_vec_idx: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        let slice_backing =
            args.first().and_then(|arg| self.resolve_slice_backing(arg, modified_locals));
        let input_len = slice_backing
            .as_ref()
            .map(|backing| backing.len.as_expr().clone())
            .or_else(|| self.vec_from_slice_input_len(args));

        if let Some(len_expr) = input_len.clone() {
            if let Some(len_var) = self.collections.len_state.get_len_var(dest_local).cloned() {
                self.collection_len_set(&len_var, len_expr.clone(), acc);
            }
            if let Some(cap_var) = self.collections.len_state.get_cap_var(dest_local).cloned() {
                self.collection_cap_set(&cap_var, len_expr.clone(), acc);
                Self::emit_cap_ge_len(len_expr.clone(), len_expr, acc.constraints);
            }
        }

        if self.collections.projection_locals.get(&dest_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let Some((ptr_name, ptr_sort_val)) = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_PTR)
                .cloned()
            else {
                return;
            };
            let Some((len_name, len_sort)) = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_LEN)
                .cloned()
            else {
                return;
            };
            let Some((cap_name, cap_sort)) = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_CAP)
                .cloned()
            else {
                return;
            };
            let Some((data_name, data_sort)) = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_DATA)
                .cloned()
            else {
                return;
            };

            let ptr = declare_pending_var(
                {
                    let mut n = String::with_capacity(ptr_name.len() + 15);
                    n.push_str(&ptr_name);
                    n.push_str("_slice_vec_ptr");
                    n
                },
                ptr_sort_val,
            );
            let data = if let Some(backing) = slice_backing.as_ref() {
                let uses_exact_data = backing.data.as_expr().sort() == &data_sort
                    && Self::is_zero_pointer_width_bitvec(backing.offset.as_expr());
                if !uses_exact_data {
                    self.record_aggregate_gap("vec_from_slice_data_sort_or_offset_mismatch");
                }
                self.rebase_slice_backing_to_zero_based_array(
                    backing,
                    &data_sort,
                    "__vec_from_slice_data",
                    SLICE_BACKING_REBASE_MAX_ELEMS,
                )
                .unwrap_or_else(|| {
                    declare_pending_var(
                        {
                            let mut n = String::with_capacity(data_name.len() + 16);
                            n.push_str(&data_name);
                            n.push_str("_slice_vec_data");
                            n
                        },
                        data_sort.clone(),
                    )
                })
            } else {
                declare_pending_var(
                    {
                        let mut n = String::with_capacity(data_name.len() + 16);
                        n.push_str(&data_name);
                        n.push_str("_slice_vec_data");
                        n
                    },
                    data_sort.clone(),
                )
            };
            let len_val = input_len.clone().unwrap_or_else(|| {
                declare_pending_var(
                    {
                        let mut n = String::with_capacity(len_name.len() + 15);
                        n.push_str(&len_name);
                        n.push_str("_slice_vec_len");
                        n
                    },
                    len_sort,
                )
            });
            let cap_val = input_len.unwrap_or_else(|| {
                declare_pending_var(
                    {
                        let mut n = String::with_capacity(cap_name.len() + 15);
                        n.push_str(&cap_name);
                        n.push_str("_slice_vec_cap");
                        n
                    },
                    cap_sort,
                )
            });
            Self::emit_cap_ge_len(cap_val.clone(), len_val.clone(), acc.constraints);
            if !self.constrain_projected_vec_fields_for_call(
                dest_local,
                ProjectedVecState { ptr, len: len_val, cap: cap_val, data },
                acc.constraints,
                acc.dests,
            ) {
                self.record_sound_fallback_reason("vec_field_constraint_not_emitted");
            }
            return;
        }

        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
            && let Some(dt) = out_sort.datatype_sort()
            && dt.constructors.first().is_some_and(|c| c.has_field(vec_layout::FLD_CAP))
        {
            let dt_name = out_sort.datatype_name().expect("has datatype_sort");
            let len_sort = dt
                .constructors
                .first()
                .and_then(|c| c.field_sort(vec_layout::FLD_LEN))
                .unwrap_or_else(ptr_sort);
            let cap_sort = dt
                .constructors
                .first()
                .and_then(|c| c.field_sort(vec_layout::FLD_CAP))
                .unwrap_or_else(ptr_sort);
            let ptr = declare_pending_var(
                {
                    let mut n = String::with_capacity(out_name.len() + 15);
                    n.push_str(&out_name);
                    n.push_str("_slice_vec_ptr");
                    n
                },
                ptr_sort(),
            );
            let data_sort = dt
                .constructors
                .first()
                .and_then(|c| c.field_sort(vec_layout::FLD_DATA))
                .unwrap_or_else(|| Sort::array(ptr_sort(), ptr_sort()));
            let data = if let Some(backing) = slice_backing.as_ref() {
                let uses_exact_data = backing.data.as_expr().sort() == &data_sort
                    && Self::is_zero_pointer_width_bitvec(backing.offset.as_expr());
                if !uses_exact_data {
                    self.record_aggregate_gap("vec_from_slice_dt_data_sort_or_offset_mismatch");
                }
                self.rebase_slice_backing_to_zero_based_array(
                    backing,
                    &data_sort,
                    "__vec_from_slice_data",
                    SLICE_BACKING_REBASE_MAX_ELEMS,
                )
                .unwrap_or_else(|| {
                    declare_pending_var(
                        {
                            let mut n = String::with_capacity(out_name.len() + 16);
                            n.push_str(&out_name);
                            n.push_str("_slice_vec_data");
                            n
                        },
                        data_sort.clone(),
                    )
                })
            } else {
                declare_pending_var(
                    {
                        let mut n = String::with_capacity(out_name.len() + 16);
                        n.push_str(&out_name);
                        n.push_str("_slice_vec_data");
                        n
                    },
                    data_sort.clone(),
                )
            };
            let len_val = input_len.clone().unwrap_or_else(|| {
                declare_pending_var(
                    {
                        let mut n = String::with_capacity(out_name.len() + 15);
                        n.push_str(&out_name);
                        n.push_str("_slice_vec_len");
                        n
                    },
                    len_sort,
                )
            });
            let cap_val = input_len.unwrap_or_else(|| {
                declare_pending_var(
                    {
                        let mut n = String::with_capacity(out_name.len() + 15);
                        n.push_str(&out_name);
                        n.push_str("_slice_vec_cap");
                        n
                    },
                    cap_sort,
                )
            });
            Self::emit_cap_ge_len(cap_val.clone(), len_val.clone(), acc.constraints);
            acc.constraints.push(Self::build_vec_datatype_eq(
                dt_name,
                vec![ptr, len_val, cap_val, data],
                &out_name,
                &out_sort,
            ));
            acc.dests.push(dest_local);
        }
    }
}
