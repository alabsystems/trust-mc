// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Direct array element store via Index/ConstantIndex projection.
//!
//! Extracted from codegen_stmt_store.rs per #2246 to bring it below 500 lines.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//!
//! Contains:
//! - `handle_array_element_store`: `arr[idx] = value` via Index/ConstantIndex (#1739)
//! - Extended for `arr[idx].field = value` via select+update+store (#2919)

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use tracing::{debug, warn};

use crate::codegen_ay::shared::ty_signedness_shallow;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::ChcCtx;
use super::codegen_call_coerce::coerce_eq_constraint;
use super::codegen_ctx::diagnostics::CellCounter;
use super::constant_index_offset;
use super::stmt_accumulator::StmtAccumulator;
use super::{UnknownProjectionPolicy, collect_field_projections};

/// Extension trait for array element stores on `ChcCtx`.
pub(crate) trait StmtStoreArray {
    /// Handles array element store via Index/ConstantIndex projection.
    ///
    /// Generates `arr_out = store(arr_in, idx, value)` for simple `arr[idx] = value`.
    /// Part of #1739.
    ///
    /// Returns `true` if the store was handled (caller should `continue`).
    fn handle_array_element_store(
        &mut self,
        lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool;
}

impl<'tcx, 'body> StmtStoreArray for ChcCtx<'tcx, 'body> {
    fn handle_array_element_store(
        &mut self,
        lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        // First projection must be Index or ConstantIndex.
        let first = match lhs.projection.first() {
            Some(p @ (ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })) => p,
            _ => return false,
        };

        // Trailing projections after the index must all be Field/Downcast.
        // Part of #2919: support `arr[idx].field = value` patterns.
        let trailing = &lhs.projection[1..];
        let all_field_downcast = trailing
            .iter()
            .all(|p| matches!(p, ProjectionElem::Field(..) | ProjectionElem::Downcast(..)));
        if !all_field_downcast {
            return false;
        }

        // Extract field projections from trailing elements (empty for bare `arr[idx] = val`).
        let field_projs = if trailing.is_empty() {
            Vec::new()
        } else {
            let fp = collect_field_projections(
                trailing,
                UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
            );
            if fp.is_empty() {
                return false;
            }
            fp
        };

        // Fix #2238: Use local_to_state_idx mapping for correct vector indices
        // Part of #3768: graceful fallback instead of panic
        let Some(arr_vec_idx) = self.try_state_idx_for_local(local_idx) else {
            self.diagnostics.store_dropped_transition.inc();
            acc.modified.insert(local_idx);
            return true;
        };

        // Resolve the index expression.
        let index_expr = match first {
            ProjectionElem::Index(index_local) => {
                let index_local_idx: usize = *index_local;
                // Part of #3768: graceful fallback instead of panic
                let Some(idx_vec) = self.try_state_idx_for_local(index_local_idx) else {
                    self.diagnostics.store_dropped_transition.inc();
                    acc.modified.insert(local_idx);
                    return true;
                };
                let raw = if acc.modified.contains(&index_local_idx) {
                    let Some((name, sort)) = self.state_var_mgr.output_state_vars.get(idx_vec)
                    else {
                        warn!(
                            ?local_idx,
                            "CHC: dropped array store — missing index output state var (Part of #2236)"
                        );
                        self.diagnostics.store_dropped_transition.inc();
                        // Part of #3138: mark array modified-unconstrained (universally quantified)
                        acc.modified.insert(local_idx);
                        return true;
                    };
                    Expr::var(&**name, sort.clone())
                } else {
                    let Some((name, sort)) = self.state_var_mgr.state_vars.get(idx_vec) else {
                        warn!(
                            ?local_idx,
                            "CHC: dropped array store — missing index input state var (Part of #2236)"
                        );
                        self.diagnostics.store_dropped_transition.inc();
                        // Part of #3138: mark array modified-unconstrained (universally quantified)
                        acc.modified.insert(local_idx);
                        return true;
                    };
                    Expr::var(&**name, sort.clone())
                };
                coerce_bitvec_width_safe(raw, POINTER_WIDTH, SignExtension::ZeroExtend)
            }
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                // #from_end needs the slice's runtime length -> fail closed (projection_path.rs)
                let Some(actual_index) = constant_index_offset(*offset, *min_length, *from_end)
                else {
                    warn!(
                        ?local_idx,
                        "CHC: dropped array store - from_end ConstantIndex needs the slice's \
                         runtime length, which min_length does not provide"
                    );
                    self.diagnostics.store_dropped_transition.inc();
                    // Part of #3138: mark array modified-unconstrained (universally quantified)
                    acc.modified.insert(local_idx);
                    return true;
                };
                Expr::bitvec_const(actual_index as u128, POINTER_WIDTH)
            }
            _ => unreachable!("guard above ensures Index or ConstantIndex"),
        };

        // Get array input expression (use output if array was modified in this block).
        let arr_in = if acc.modified.contains(&local_idx) {
            let Some((name, sort)) = self.state_var_mgr.output_state_vars.get(arr_vec_idx) else {
                warn!(
                    ?local_idx,
                    "CHC: dropped array store — missing array output state var (Part of #2236)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark array modified-unconstrained (universally quantified)
                acc.modified.insert(local_idx);
                return true;
            };
            Expr::var(&**name, sort.clone())
        } else {
            let Some((name, sort)) = self.state_var_mgr.state_vars.get(arr_vec_idx) else {
                warn!(
                    ?local_idx,
                    "CHC: dropped array store — missing array input state var (Part of #2236)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark array modified-unconstrained (universally quantified)
                acc.modified.insert(local_idx);
                return true;
            };
            Expr::var(&**name, sort.clone())
        };

        // Get output array variable.
        // Part of #3296: Clone out_sort to release the immutable borrow on self,
        // allowing &mut self calls (try_unflatten_bv_to_datatype) below.
        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(arr_vec_idx)
        else {
            warn!(
                ?local_idx,
                "CHC: dropped array store — missing array output var (Part of #2236)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark array modified-unconstrained (universally quantified)
            acc.modified.insert(local_idx);
            return true;
        };
        let out_sort = out_sort.clone();
        let arr_out = Expr::var(&**out_name, out_sort.clone());

        // Compute the value to store.
        // For bare `arr[idx] = value`: store rhs_expr directly.
        // For `arr[idx].field = value` (#2919): select element, functional-update field, store back.
        // Part of #3034: derive signedness from array element MIR type.
        let signed = self
            .body
            .locals()
            .get(local_idx)
            .and_then(|decl| match decl.ty.kind() {
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Array(elem_ty, _)) => {
                    ty_signedness_shallow(elem_ty)
                }
                _ => ty_signedness_shallow(decl.ty),
            })
            .unwrap_or(false);
        let value_to_store = if field_projs.is_empty() {
            Self::coerce_store_value(arr_in.sort(), rhs_expr, signed, &self.diagnostics)
        } else {
            let mut element = arr_in.clone().select(index_expr.clone());
            // Part of #3296: Unflatten BV→DT after array select if element was flattened.
            if let Some(local_decl) = self.body.locals().get(local_idx) {
                if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Array(
                    elem_ty,
                    _,
                )) = local_decl.ty.kind()
                {
                    element = self.try_unflatten_bv_to_datatype(element, elem_ty);
                }
            }
            if !element.sort().is_datatype() {
                warn!(
                    ?local_idx,
                    element_sort = ?element.sort(),
                    "CHC: array element is not Datatype — cannot apply field update (Part of #2919)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark array modified-unconstrained (universally quantified)
                acc.modified.insert(local_idx);
                return true;
            }
            let Some(updated) = Self::apply_projection_update(&element, &field_projs, rhs_expr)
            else {
                warn!(
                    ?local_idx,
                    field_count = field_projs.len(),
                    "CHC: apply_projection_update failed for array element field store (Part of #2919)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark array modified-unconstrained (universally quantified)
                acc.modified.insert(local_idx);
                return true;
            };
            // Re-flatten Datatype→BV if the array element sort is BV (Part of #2970).
            // The unflatten+update produces a Datatype value but the array expects BV.
            Self::coerce_store_value(arr_in.sort(), updated, signed, &self.diagnostics)
        };

        // Generate: arr_out = store(arr_in, index, value_to_store).
        let store_expr = arr_in.store(index_expr, value_to_store);
        if let Some(c) = coerce_eq_constraint(&arr_out, store_expr, &out_sort, false) {
            // Part of #3112: Track constraint index in last_constraint_for_local to
            // satisfy the #3038 modified-without-constraint invariant.
            acc.replace_constraint(local_idx, c);
        } else {
            warn!(
                ?local_idx,
                "CHC: dropped array store — arr_out/store_expr sort mismatch (Part of #2244)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark array modified-unconstrained (universally quantified)
            acc.modified.insert(local_idx);
            return true;
        }
        acc.modified.insert(local_idx);
        if field_projs.is_empty() {
            debug!(
                ?local_idx,
                "CHC: emitted array element store via Index/ConstantIndex (Part of #1739)"
            );
        } else {
            debug!(
                ?local_idx,
                field_count = field_projs.len(),
                "CHC: emitted array element field store via select+update+store (Part of #2919)"
            );
        }
        true
    }
}
