// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Array element store handlers for ref_target and arg-ref pointee paths.
//!
//! Extracted from `codegen_stmt_store_ref.rs` to stay under the 500-line limit.
//! Part of #2750: array element store through arg-ref pointee.
//!
//! Contains:
//! - `handle_deref_store_array_via_ref_targets`: array element case for ref_target stores (#1957)
//! - `handle_deref_store_array_arg_ref`: array element through arg-ref pointee (#2750)

use ay_bindings::Expr;
use rustc_public::mir::ProjectionElem;
use tracing::{debug, warn};

use super::codegen_call_coerce::coerce_eq_constraint;
use super::codegen_ctx::diagnostics::CellCounter;
use super::stmt_accumulator::StmtAccumulator;
use super::{ChcCtx, FieldProjection, POINTER_WIDTH, constant_index_offset};
use crate::codegen_ay::shared::ty_signedness_shallow;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Array element store via ref_targets (#1957).
    ///
    /// Handles `*ref_local[idx] = val` where `ref_local` has a ref_target entry.
    /// Resolves the index, builds `arr.store(idx, val)`, emits the constraint.
    pub(in crate::codegen_ay::chc) fn handle_deref_store_array_via_ref_targets_impl(
        &mut self,
        rhs_expr: Expr,
        ref_local: usize,
        ref_target: &super::RefTarget,
        index_proj: &ProjectionElem,
        field_projs: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let target_local = ref_target.local;
        // Part of #3768: graceful fallback instead of panic
        let Some(target_vec_idx) = self.try_state_idx_for_local(target_local) else {
            return false;
        };

        let index_expr = match index_proj {
            ProjectionElem::Index(index_local) => {
                self.resolve_local_expr(*index_local, &acc.modified)
            }
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                let actual_index = constant_index_offset(*offset, *min_length, *from_end);
                Some(Expr::bitvec_const(actual_index as u128, POINTER_WIDTH))
            }
            other => {
                warn!(
                    ?other,
                    ref_local, "CHC: non-index projection in array store path (Part of #2236)"
                );
                None
            }
        };

        let Some(index_expr) = index_expr else {
            warn!(
                ref_local,
                "CHC: dropped array store via ref_targets — index_expr not resolved (Part of #2236)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return true;
        };

        let index_expr =
            coerce_bitvec_width_safe(index_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
        // Part of #2992: Post-coercion BV check — non-BV index causes sort mismatch
        // in select/store operations downstream.
        if index_expr.sort().bitvec_width().is_none() {
            warn!(
                ref_local,
                sort = ?index_expr.sort(),
                "CHC: dropped array store via ref_targets — non-BV index after coercion (#2992)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return true;
        }

        let arr_in = if acc.modified.contains(&target_local) {
            let Some((name, sort)) = self.state_var_mgr.output_state_vars.get(target_vec_idx)
            else {
                warn!(
                    ?target_local,
                    ref_local,
                    "CHC: dropped array store via ref_targets — missing array output state var (Part of #2236)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark target modified-unconstrained (universally quantified)
                acc.modified.insert(target_local);
                return true;
            };
            Expr::var(&**name, sort.clone())
        } else {
            let Some((name, sort)) = self.state_var_mgr.state_vars.get(target_vec_idx) else {
                warn!(
                    ?target_local,
                    ref_local,
                    "CHC: dropped array store via ref_targets — missing array input state var (Part of #2236)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark target modified-unconstrained (universally quantified)
                acc.modified.insert(target_local);
                return true;
            };
            Expr::var(&**name, sort.clone())
        };

        // Part of #3296: Clone out_sort to release the immutable borrow on self,
        // allowing &mut self calls (try_unflatten_bv_to_datatype) below.
        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(target_vec_idx)
        else {
            warn!(
                ?target_local,
                ref_local,
                "CHC: dropped array store via ref_targets — missing array output var (Part of #2236)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return true;
        };
        let out_sort = out_sort.clone();
        let arr_out = Expr::var(&**out_name, out_sort.clone());

        let value_to_store = if field_projs.is_empty() {
            rhs_expr
        } else {
            let mut struct_val = arr_in.clone().select(index_expr.clone());
            // Part of #3296: Unflatten BV→DT after array select if element was flattened.
            // When array elements are BV-encoded (flattened structs), select() returns a BV.
            // apply_projection_update needs a Datatype to do field navigation, so we unflatten
            // first and re-flatten after update via coerce_store_value below.
            if let Some(local_decl) = self.body.locals().get(target_local) {
                if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Array(
                    elem_ty,
                    _,
                )) = local_decl.ty.kind()
                {
                    struct_val = self.try_unflatten_bv_to_datatype(struct_val, elem_ty);
                }
            }
            if let Some(updated) =
                ChcCtx::apply_projection_update(&struct_val, field_projs, rhs_expr)
            {
                updated
            } else {
                warn!(
                    ref_local,
                    "CHC: dropped array store — apply_projection_update failed for arr[idx].field (Part of #2236)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark target modified-unconstrained (universally quantified)
                acc.modified.insert(target_local);
                return true;
            }
        };

        // Part of #3034: derive signedness from array element MIR type.
        let signed = self
            .body
            .locals()
            .get(target_local)
            .and_then(|decl| match decl.ty.kind() {
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Array(elem_ty, _)) => {
                    ty_signedness_shallow(elem_ty)
                }
                _ => ty_signedness_shallow(decl.ty),
            })
            .unwrap_or(false);
        let value_to_store =
            ChcCtx::coerce_store_value(arr_in.sort(), value_to_store, signed, &self.diagnostics);
        let store_expr = arr_in.store(index_expr, value_to_store);
        if let Some(c) = coerce_eq_constraint(&arr_out, store_expr, &out_sort, false) {
            // Part of #3112: Track constraint index in last_constraint_for_local to
            // satisfy the #3038 modified-without-constraint invariant.
            acc.replace_constraint(target_local, c);
        } else {
            warn!(
                ?target_local,
                ref_local,
                "CHC: dropped Deref array store — arr_out/store_expr sort mismatch (Part of #2244)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return true;
        }
        acc.modified.insert(target_local);
        debug!(
            target_local,
            ref_local,
            has_field_projs = !field_projs.is_empty(),
            "CHC: emitted Reg-level Deref store via ref_targets (#1957)"
        );
        true
    }

    /// Array element store through arg-ref pointee (#2750).
    ///
    /// Analogous to `handle_deref_store_array_via_ref_targets_impl` but operates on
    /// the auxiliary pointee state vars from `ref_arg_pointee_idx` rather than
    /// the `ref_targets` map. Handles `(*arg_ref)[i] = val` patterns.
    pub(in crate::codegen_ay::chc) fn handle_deref_store_array_arg_ref_impl(
        &mut self,
        rhs_expr: Expr,
        local_idx: usize,
        pointee_vec_idx: usize,
        index_proj: &ProjectionElem,
        field_projs: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let track_key = usize::MAX - pointee_vec_idx;
        let index_expr = match index_proj {
            ProjectionElem::Index(index_local) => {
                let idx_local: usize = *index_local;
                // Part of #3768: graceful fallback instead of panic
                let Some(idx_vec) = self.try_state_idx_for_local(idx_local) else {
                    return false;
                };
                if self.encode.modified_state_indices.contains(&idx_vec) {
                    self.state_var_mgr
                        .output_state_vars
                        .get(idx_vec)
                        .map(|(n, s)| Expr::var(&**n, s.clone()))
                } else {
                    self.state_var_mgr
                        .state_vars
                        .get(idx_vec)
                        .map(|(n, s)| Expr::var(&**n, s.clone()))
                }
            }
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                let actual_index = constant_index_offset(*offset, *min_length, *from_end);
                Some(Expr::bitvec_const(actual_index as u128, POINTER_WIDTH))
            }
            other => {
                warn!(
                    ?other,
                    local_idx, "CHC: non-index projection in arg-ref array store path (#2750)"
                );
                None
            }
        };

        let Some(index_expr) = index_expr else {
            warn!(
                local_idx,
                pointee_vec_idx,
                "CHC: dropped arg-ref array store — index_expr not resolved (#2750)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark pointee modified-unconstrained (universally quantified)
            self.mark_state_var_modified(pointee_vec_idx);
            return true;
        };

        let index_expr =
            coerce_bitvec_width_safe(index_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
        // Part of #2992: Post-coercion BV check — non-BV index causes sort mismatch
        // in select/store operations downstream.
        if index_expr.sort().bitvec_width().is_none() {
            warn!(
                local_idx,
                sort = ?index_expr.sort(),
                "CHC: dropped arg-ref array store — non-BV index after coercion (#2992)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark pointee modified-unconstrained (universally quantified)
            self.mark_state_var_modified(pointee_vec_idx);
            return true;
        }

        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(pointee_vec_idx)
        else {
            warn!(
                local_idx,
                pointee_vec_idx,
                "CHC: dropped arg-ref array store — missing pointee output state var (#2750)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark pointee modified-unconstrained (universally quantified)
            self.mark_state_var_modified(pointee_vec_idx);
            return true;
        };
        let out_name = out_name.clone();
        let out_sort = out_sort.clone();

        let arr_in = if self.encode.modified_state_indices.contains(&pointee_vec_idx) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&track_key) {
                env_expr.clone()
            } else {
                Expr::var(&*out_name, out_sort.clone())
            }
        } else if let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(pointee_vec_idx)
        {
            Expr::var(&**in_name, in_sort.clone())
        } else {
            warn!(
                local_idx,
                pointee_vec_idx,
                "CHC: dropped arg-ref array store — missing pointee input state var (#2750)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark pointee modified-unconstrained (universally quantified)
            self.mark_state_var_modified(pointee_vec_idx);
            return true;
        };

        let arr_out = Expr::var(&*out_name, out_sort.clone());

        let value_to_store = if field_projs.is_empty() {
            rhs_expr
        } else {
            let struct_val = arr_in.clone().select(index_expr.clone());
            if let Some(updated) =
                ChcCtx::apply_projection_update(&struct_val, field_projs, rhs_expr)
            {
                updated
            } else {
                warn!(
                    local_idx,
                    pointee_vec_idx,
                    "CHC: dropped arg-ref array store — apply_projection_update failed (#2750)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark pointee modified-unconstrained (universally quantified)
                self.mark_state_var_modified(pointee_vec_idx);
                return true;
            }
        };

        // Part of #3034: derive signedness from local's array element MIR type.
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
        let value_to_store =
            ChcCtx::coerce_store_value(arr_in.sort(), value_to_store, signed, &self.diagnostics);
        let store_expr = arr_in.store(index_expr, value_to_store);
        if let Some(c) = coerce_eq_constraint(&arr_out, store_expr, &out_sort, false) {
            acc.replace_constraint(track_key, c);
            self.mark_state_var_modified(pointee_vec_idx);
        } else {
            warn!(
                local_idx,
                pointee_vec_idx,
                "CHC: dropped arg-ref array store — arr_out/store sort mismatch (#2750)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark pointee modified-unconstrained (universally quantified)
            self.mark_state_var_modified(pointee_vec_idx);
            return true;
        }
        debug!(
            local_idx,
            pointee_vec_idx,
            has_field_projs = !field_projs.is_empty(),
            "CHC: emitted Reg-level arg-ref array Deref store (#2750)"
        );
        true
    }
}
