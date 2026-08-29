// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Local array update when a ref_target points to an array element.
//!
//! Part of #1957: When writing through a reference that points to arr[idx] (or
//! arr[idx].field), we update both memory (via build_memory_store, done by caller)
//! and the local array state so reads of arr[idx] see the new value.

use ay_bindings::Expr;
use rustc_public::mir::ProjectionElem;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, trace, warn};

use crate::codegen_ay::shared::ty_signedness_shallow;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::super::codegen_call_coerce::coerce_eq_constraint;
use super::super::codegen_ctx::diagnostics::CellCounter;
use super::super::stmt_accumulator::StmtAccumulator;
use super::super::{ChcCtx, FieldProjection, RefTarget, constant_index_offset};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Emits a local array update when a ref_target points to an array element.
    ///
    /// Part of #1957: When writing through a reference that points to arr[idx] (or
    /// arr[idx].field), we update both memory (via build_memory_store, done by caller)
    /// and the local array state so reads of arr[idx] see the new value.
    /// Part of #3517: accepts `StmtAccumulator` instead of raw `modified` + `constraints`.
    pub(in crate::codegen_ay::chc) fn emit_ref_target_array_update(
        &self,
        ref_target: &RefTarget,
        rhs_expr: &Expr,
        ref_local: usize,
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        self.emit_ref_target_array_update_indexed(
            ref_target, rhs_expr, ref_local, bb_idx, acc, None,
        )
    }

    /// As [`Self::emit_ref_target_array_update`], but with the element index
    /// supplied directly rather than read off an `Index` projection.
    ///
    /// A pointer produced by `as_mut_ptr().add(n)` carries its element index in
    /// `ref_resolution.subslice_offset`, NOT as a projection on the ref target
    /// (whose target is the whole array). Without this entry point such a store
    /// had nowhere to land in the scalarized value lanes.
    pub(in crate::codegen_ay::chc) fn emit_ref_target_array_update_indexed(
        &self,
        ref_target: &RefTarget,
        rhs_expr: &Expr,
        ref_local: usize,
        _bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
        explicit_index: Option<Expr>,
    ) {
        // Check if ref_target has an Index projection (points to array element)
        let index_proj = ref_target
            .projections
            .iter()
            .find(|p| matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }));

        // Collect field projections after the Index for patterns like
        // `*r = v` where `r` points to `arr[idx].field`.
        let mut field_projs_iter = ref_target.projections.iter().skip_while(|p| {
            !matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
        });
        // Skip the first projection after skip_while (the Index/ConstantIndex itself).
        field_projs_iter.next();
        let field_projs: Vec<FieldProjection> = field_projs_iter
            .filter_map(|p| match p {
                ProjectionElem::Field(idx, ty) => {
                    Some(FieldProjection { field_idx: *idx, cons_idx: None, field_ty: Some(*ty) })
                }
                _ => None, // external enum: ProjectionElem
            })
            .collect();

        if index_proj.is_none() && explicit_index.is_none() {
            // No Index/ConstantIndex projection — ref doesn't point to array element.
            // This is not a dropped store; the caller already handled memory via build_memory_store.
            return;
        }

        let target_local = ref_target.local;
        let Some(target_vec_idx) = self.try_state_idx_for_local(target_local) else {
            warn!(
                ?target_local,
                ref_local,
                "CHC: dropped local array update — missing target local mapping (Part of #2236)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return;
        };

        // Get index expression — an explicitly supplied one wins, since it
        // comes from the pointer's own offset rather than from the target's
        // shape.
        let index_expr = if let Some(idx) = explicit_index {
            Some(idx)
        } else {
            match index_proj.expect("index_proj or explicit_index is Some") {
                ProjectionElem::Index(index_local) => {
                    // Fix #2238: Use local_to_state_idx mapping for index local
                    self.try_resolve_local_expr(*index_local, acc.modified)
                }
                ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                    // #from_end: needs the slice's runtime length -> fail closed (projection_path.rs)
                    constant_index_offset(*offset, *min_length, *from_end)
                        .map(|i| Expr::bitvec_const(i as u128, POINTER_WIDTH))
                }
                other => {
                    trace!(?other, "CHC: non-index projection in array store path");
                    None
                }
            }
        };

        let Some(index_expr) = index_expr else {
            warn!(
                ref_local,
                "CHC: dropped local array update — index_expr not resolved (Part of #2236)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return;
        };

        // Coerce index to pointer width
        let index_expr =
            coerce_bitvec_width_safe(index_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
        // Part of #2992: Post-coercion BV check — non-BV index causes sort mismatch
        // in select/store operations downstream.
        if index_expr.sort().bitvec_width().is_none() {
            warn!(
                ref_local,
                sort = ?index_expr.sort(),
                "CHC: dropped local array update — non-BV index after coercion (#2992)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return;
        }

        // Get input array (use output if already modified)
        let arr_in = if acc.modified.contains(&target_local) {
            let Some((name, sort)) = self.state_var_mgr.output_state_vars.get(target_vec_idx)
            else {
                warn!(
                    ?target_local,
                    ref_local,
                    "CHC: dropped local array update — missing array output state var (Part of #2236)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark target modified-unconstrained (universally quantified)
                acc.modified.insert(target_local);
                return;
            };
            Expr::var(&**name, sort.clone())
        } else {
            let Some((name, sort)) = self.state_var_mgr.state_vars.get(target_vec_idx) else {
                warn!(
                    ?target_local,
                    ref_local,
                    "CHC: dropped local array update — missing array input state var (Part of #2236)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark target modified-unconstrained (universally quantified)
                acc.modified.insert(target_local);
                return;
            };
            Expr::var(&**name, sort.clone())
        };

        // Get output array
        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(target_vec_idx)
        else {
            warn!(
                ?target_local,
                ref_local,
                "CHC: dropped local array update — missing array output var (Part of #2236)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return;
        };
        let arr_out = Expr::var(&**out_name, out_sort.clone());

        let value_to_store = if field_projs.is_empty() {
            rhs_expr.clone()
        } else {
            let struct_val = arr_in.clone().select(index_expr.clone());
            if let Some(updated) =
                ChcCtx::apply_projection_update(&struct_val, &field_projs, rhs_expr.clone())
            {
                updated
            } else if struct_val.sort().is_bitvec() {
                // Part of #2970, #3086: BV-flattened struct field update via shared helper.
                // CHC flattens Datatype array elements to BV (#1739). When updating
                // arr[idx].field_chain, the element is BV, not a Datatype. Use extract/concat
                // to replace the specific field bits.
                if let Some(updated) = self.bv_flattened_field_update(
                    &struct_val,
                    &field_projs,
                    rhs_expr,
                    target_local,
                ) {
                    updated
                } else {
                    warn!(
                        ref_local,
                        "CHC: dropped local array update — bv_projection_update failed (Part of #2970)"
                    );
                    self.diagnostics.store_dropped_transition.inc();
                    // Part of #3138: mark target modified-unconstrained (universally quantified)
                    acc.modified.insert(target_local);
                    return;
                }
            } else {
                warn!(
                    ref_local,
                    "CHC: dropped local array update — apply_projection_update failed for arr[idx].field (Part of #2236)"
                );
                self.diagnostics.store_dropped_transition.inc();
                // Part of #3138: mark target modified-unconstrained (universally quantified)
                acc.modified.insert(target_local);
                return;
            }
        };

        // Generate: arr_out = store(arr_in, index, value)
        // Part of #2244, #3034: coerce value sort to match array element sort
        let signed = self
            .body
            .locals()
            .get(target_local)
            .and_then(|decl| match decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => ty_signedness_shallow(elem_ty),
                _ => ty_signedness_shallow(decl.ty),
            })
            .unwrap_or(false);
        let value_to_store =
            Self::coerce_store_value(arr_in.sort(), value_to_store, signed, &self.diagnostics);
        let store_expr = arr_in.store(index_expr, value_to_store);
        // Part of #2244 Phase 3: use coerce_eq_constraint to avoid sort mismatch panic
        // when arr_out sort differs from store_expr sort (arr_in's sort).
        if let Some(c) = coerce_eq_constraint(&arr_out, store_expr, out_sort, false) {
            // Part of #3544: Use replace_constraint (not raw push) to implement
            // "last write wins" for the target array local. Without this, a prior
            // constraint from encode_simple_assignment (e.g., _1__out = [10, 20])
            // conflicts with the ref-write constraint (_1__out = store(..., 0, 100)),
            // making the block UNSAT and causing Genuine CTREX regressions.
            acc.replace_constraint(target_local, c);
        } else {
            warn!(
                ?target_local,
                ref_local,
                "CHC: dropped local array update — arr_out/store_expr sort mismatch (Part of #2244)"
            );
            self.diagnostics.store_dropped_transition.inc();
            // Part of #3138: mark target modified-unconstrained (universally quantified)
            acc.modified.insert(target_local);
            return;
        }
        acc.modified.insert(target_local);
        debug!(
            target_local,
            ref_local,
            has_field_projs = !field_projs.is_empty(),
            "CHC: emitted local array update via ref_targets (#1957)"
        );
    }

    /// BV-flattened struct field update for array elements.
    ///
    /// Part of #2970: CHC flattens Datatype elements to BV for PDR compatibility
    /// (#1739). When updating `arr[idx].field_N`, the array element is a BV (not
    /// Datatype). This reconstructs the BV via extract/concat with the target field
    /// replaced.
    ///
    /// Part of #3086: Delegates to shared `bv_projection_update` helper.
    fn bv_flattened_field_update(
        &self,
        container: &Expr,
        field_projs: &[FieldProjection],
        rhs_expr: &Expr,
        target_local: usize,
    ) -> Option<Expr> {
        // Get the Rust type of the array element from the target local's MIR type.
        let local_ty = self
            .body
            .local_decls()
            .find(|(idx, _)| *idx == target_local)
            .map(|(_, decl)| decl.ty)?;

        let elem_ty = match local_ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => elem,
            _ => return None, // external enum: TyKind
        };

        Self::bv_projection_update(container, elem_ty, field_projs, rhs_expr.clone())
    }
}
