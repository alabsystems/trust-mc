// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Emission logic for iter-map-collect method dispatcher.
//!
//! Contains Vec Datatype construction, forall constraint emission, and
//! destination sort resolution. Extracted from `codegen_call_iter_collect_method.rs`
//! per 500 LOC threshold.
//!
//! Part of #3348: iter-map-collect encoding for bv_bitblast operations.

use ay_bindings::{Expr, Sort};
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_rules::CodegenRules;
use super::ClosureResult;
use super::SourceVecInfo;
use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::names;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::{CtorFieldExt, ptr_sort};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Emit the result Vec with length preservation and forall element constraint.
    pub(in crate::codegen_ay::chc) fn emit_iter_collect_result(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        dest_local: usize,
        source: &SourceVecInfo,
        closure: &ClosureResult,
    ) -> bool {
        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
            debug!(dest_local, "CHC: iter_collect dest not in state map — sound over-approx");
            self.record_sound_fallback_reason("state_idx_missing_iter_collect_dest");
            return false;
        };
        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();

        let len_bv = source.len_expr.clone();

        // Set sidecar ghost vars (len, cap).
        if let Some(len_var_name) = self.collections.len_state.get_len_var(dest_local).cloned() {
            self.collection_len_set(
                &len_var_name,
                len_bv.clone(),
                &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
            );
        }
        if let Some(cap_var_name) = self.collections.len_state.get_cap_var(dest_local).cloned() {
            self.collection_cap_set(
                &cap_var_name,
                len_bv.clone(),
                &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
            );
        }

        // Determine the result data sort from the destination type.
        let result_data_sort = match self.resolve_dest_data_sort(dest_local, dest_vec_idx) {
            Some(s) => s,
            None => return false,
        };

        // Create the symbolic data array and add forall constraint.
        let data = super::super::declare_pending_var(
            format!("icm_data_{dest_local}"),
            result_data_sort.clone(),
        );

        let idx = Expr::var(closure.idx_var_name.clone(), ptr_sort());
        let in_range = idx.clone().bvult(len_bv.clone());

        // Coerce closure body sort to match the array element sort.
        let elem_sort =
            result_data_sort.array_sort().map(|a| a.element_sort.clone()).unwrap_or_else(ptr_sort);
        let body = coerce_body_to_elem(&closure.body_expr, &elem_sort);

        let element_eq = data.clone().select(idx).eq(body);
        let forall_body = Expr::implies(in_range, element_eq);
        let forall = Expr::forall(vec![(closure.idx_var_name.clone(), ptr_sort())], forall_body);
        extra_constraints.push(forall);

        // Emit the result Vec Datatype.
        let handled = self.emit_iter_collect_vec_dt(
            dest_local,
            dest_vec_idx,
            &len_bv,
            &data,
            &mut extra_constraints,
            &mut extra_dests,
        );
        if !handled {
            return false;
        }

        let new_output_args = self.build_output_args(dcx.modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );
        true
    }

    /// Resolve the data array sort for the destination local's Vec field.
    fn resolve_dest_data_sort(&self, dest_local: usize, dest_vec_idx: usize) -> Option<Sort> {
        use super::super::codegen_ctx::types::CollectionProjectionKind;

        // Case 1: Flattened/projected Vec.
        if self.collections.projection_locals.get(&dest_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            return self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_DATA)
                .map(|(_, s)| s.clone())
                .or_else(|| Some(Sort::array(ptr_sort(), ptr_sort())));
        }

        // Case 2/3: Datatype Vec or struct wrapping Vec.
        let (_, out_sort) = self.state_var_mgr.output_state_vars.get(dest_vec_idx)?.clone();
        let dt = out_sort.datatype_sort()?;

        // Case 2: Direct Vec DT — extract data field sort.
        if let Some(ctor) = dt.constructors.first() {
            if ctor.has_field(vec_layout::FLD_DATA) {
                return ctor.field_sort(vec_layout::FLD_DATA);
            }
            // Case 3: Struct wrapping Vec — find inner Vec DT's data sort.
            for field in &ctor.fields {
                if let Some(inner_dt) = field.sort.datatype_sort() {
                    if inner_dt
                        .constructors
                        .first()
                        .is_some_and(|c| c.has_field(vec_layout::FLD_DATA))
                    {
                        return inner_dt
                            .constructors
                            .first()
                            .and_then(|c| c.field_sort(vec_layout::FLD_DATA));
                    }
                }
            }
        }
        None
    }

    /// Emit the destination Vec Datatype with given len and data.
    fn emit_iter_collect_vec_dt(
        &mut self,
        dest_local: usize,
        dest_vec_idx: usize,
        len_bv: &Expr,
        data: &Expr,
        constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) -> bool {
        use super::super::codegen_ctx::types::CollectionProjectionKind;

        // Case 1: Flattened/projected Vec.
        if self.collections.projection_locals.get(&dest_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let ptr =
                super::super::declare_pending_var(format!("icm_ptr_{dest_local}"), ptr_sort());
            return self.constrain_projected_vec_fields_for_call(
                dest_local,
                super::super::codegen_call_vec_ops::ProjectedVecState {
                    ptr,
                    len: len_bv.clone(),
                    cap: len_bv.clone(),
                    data: data.clone(),
                },
                constraints,
                extra_dests,
            );
        }

        // Case 2/3: Datatype destination.
        let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
        else {
            return false;
        };
        let Some(dt) = out_sort.datatype_sort() else {
            return false;
        };

        // Case 2: Direct Vec DT.
        if dt.constructors.first().is_some_and(|c| c.has_field(vec_layout::FLD_LEN)) {
            let dt_name = out_sort.datatype_name().expect("has datatype_sort");
            let ptr =
                super::super::declare_pending_var(format!("icm_ptr_{dest_local}"), ptr_sort());
            constraints.push(Self::build_vec_datatype_eq(
                dt_name,
                vec![ptr, len_bv.clone(), len_bv.clone(), data.clone()],
                &out_name,
                &out_sort,
            ));
            extra_dests.push(dest_local);
            return true;
        }

        // Case 3: Struct wrapping Vec.
        let Some(ctor) = dt.constructors.first() else {
            return false;
        };
        self.emit_icm_struct_wrapping_vec(
            dest_local,
            ctor,
            len_bv,
            data,
            &out_name,
            &out_sort,
            constraints,
            extra_dests,
        )
    }

    /// Emit a struct-wrapping-Vec Datatype (Case 3 of emit_iter_collect_vec_dt).
    fn emit_icm_struct_wrapping_vec(
        &self,
        dest_local: usize,
        ctor: &ay_bindings::DatatypeConstructor,
        len_bv: &Expr,
        data: &Expr,
        out_name: &str,
        out_sort: &Sort,
        constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) -> bool {
        for field in &ctor.fields {
            let inner_dt = match field.sort.datatype_sort() {
                Some(d) => d,
                None => continue,
            };
            if !inner_dt.constructors.first().is_some_and(|c| c.has_field(vec_layout::FLD_LEN)) {
                continue;
            }
            let inner_dt_name = field.sort.datatype_name().expect("has datatype_sort");
            let vec_ptr =
                super::super::declare_pending_var(format!("icm_ptr_{dest_local}"), ptr_sort());

            let vec_expr = Expr::datatype_constructor(
                inner_dt_name,
                names::cons_name(inner_dt_name),
                vec![vec_ptr, len_bv.clone(), len_bv.clone(), data.clone()],
                field.sort.clone(),
            );

            let outer_dt_name = out_sort.datatype_name().expect("has datatype_sort");
            let outer_ctor_name = names::resolve_ctor_name(out_sort, outer_dt_name);
            let vec_field_idx = ctor.fields.iter().position(|ff| ff.name == field.name);
            let outer_fields: Vec<Expr> = ctor
                .fields
                .iter()
                .enumerate()
                .map(|(fi, f)| {
                    if Some(fi) == vec_field_idx {
                        vec_expr.clone()
                    } else {
                        super::super::declare_pending_var(
                            format!("icm_fld{fi}_{dest_local}"),
                            f.sort.clone(),
                        )
                    }
                })
                .collect();

            let outer_expr = Expr::datatype_constructor(
                outer_dt_name,
                outer_ctor_name,
                outer_fields,
                out_sort.clone(),
            );
            constraints.push(Expr::var(out_name, out_sort.clone()).eq(outer_expr));
            extra_dests.push(dest_local);
            return true;
        }
        false
    }
}

/// Coerce a closure body expression to match the expected element sort.
/// Handles Bool→BV and BV→Bool conversions (common for Vec<bool> patterns).
fn coerce_body_to_elem(body_expr: &Expr, elem_sort: &Sort) -> Expr {
    if *body_expr.sort() == *elem_sort {
        return body_expr.clone();
    }
    // Bool → BV coercion.
    if body_expr.sort().is_bool() && elem_sort.is_bitvec() {
        let width = elem_sort.bitvec_width().unwrap_or(64);
        return Expr::ite(
            body_expr.clone(),
            Expr::bitvec_const(1u64, width),
            Expr::bitvec_const(0u64, width),
        );
    }
    // BV → Bool coercion.
    if body_expr.sort().is_bitvec() && elem_sort.is_bool() {
        let width = body_expr.sort().bitvec_width().unwrap_or(64);
        return body_expr.clone().eq(Expr::bitvec_const(0u64, width)).not();
    }
    body_expr.clone()
}
