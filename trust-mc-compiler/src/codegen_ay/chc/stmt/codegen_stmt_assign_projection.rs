// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Projection assignment encoding for CHC block statements.
//!
//! Handles `_N.field = rhs` assignments including:
//! - Deref store at Mem level: `*ptr = value`, `(*ptr).field = value` (#905, #1100)
//! - Array element store via Index/ConstantIndex (#1739)
//! - Deref store at Reg level via ref_targets (#1957)
//! - Flattened tuple/enum field projection (#2214)
//! - Regular field projection with datatype functional update (#600)
//!
//! Extracted from codegen_stmt.rs to keep production LOC under 500.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

use super::codegen_call_coerce::coerce_eq_constraint;
use super::codegen_decl_flatten::compute_nested_flat_slot;
use super::codegen_stmt_store_array::StmtStoreArray;
use super::codegen_stmt_store_ref::StmtStoreRef;
use super::codegen_types::CodegenTypes;
use super::stmt_accumulator::StmtAccumulator;
use super::{ChcCtx, FieldProjection, UnknownProjectionPolicy, collect_field_projections};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Return whether a projection base local represents a real dereference.
    ///
    /// Mirrors `deref_pointee_ty` for pointer-like wrappers without emitting
    /// warnings on the scalar fast path probe logic.
    fn projection_base_supports_real_deref(local_ty: rustc_public::ty::Ty) -> bool {
        match local_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)) => true,
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                let wrapper_name = def.name();
                let trimmed_name = def.trimmed_name();
                matches!(
                    wrapper_name.as_str(),
                    "std::boxed::Box"
                        | "alloc::boxed::Box"
                        | "std::rc::Rc"
                        | "alloc::rc::Rc"
                        | "std::sync::Arc"
                        | "alloc::sync::Arc"
                ) || trimmed_name == "NonNull"
                    || trimmed_name == "Unique"
            }
            _ => false,
        }
    }

    /// Emit a sound over-approximation fallback for a projection assignment.
    ///
    /// Makes the local nondeterministic (universally quantified in CHC) and
    /// records a categorized sound_fallback counter for diagnostic triage.
    ///
    /// Part of #3561: extracted from 11 duplicate fallback sites.
    pub(super) fn projection_sound_fallback(
        &mut self,
        local_idx: usize,
        category: &'static str,
        acc: &mut StmtAccumulator<'_>,
    ) {
        acc.modified.insert(local_idx);
        acc.replace_constraint(local_idx, Expr::bool_const(true));
        self.record_sound_fallback_categorized(category);
    }

    /// Encode a projection assignment (`_N.field = rhs`, `*ptr = rhs`, etc.).
    ///
    /// Dispatches to the appropriate handler for deref stores, array stores,
    /// flattened tuple fields, and datatype functional updates.
    pub(in crate::codegen_ay::chc) fn encode_projection_assignment(
        &mut self,
        lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        self.encode.local_signedness.remove(&local_idx);

        // Some range-lowered MIR paths materialize `(*x).0` where `x` is already a
        // scalar local (no actual pointer indirection). Treat this projection as an
        // identity assignment to avoid dropping the update.
        let local_ty = self.body.locals()[local_idx].ty;
        let lhs_has_deref = matches!(lhs.projection.first(), Some(ProjectionElem::Deref));
        let lhs_base_is_pointer = Self::projection_base_supports_real_deref(local_ty);
        let strip_spurious_deref = lhs_has_deref && !lhs_base_is_pointer;

        // Soundness: a raw-pointer deref STORE (`*p = v`, `(*p).field = v`)
        // carries a `p != 0` obligation no matter which store handler below
        // resolves it (Mem-level memory store, ref_targets, fallback, or
        // mem-promote retry). Mirrors the load-side hook at the top of
        // try_resolve_deref_cascade. The helper itself is a no-op for
        // non-raw-pointer bases and provably non-null pointers.
        if lhs_has_deref && lhs_base_is_pointer {
            self.emit_raw_ptr_null_deref_check(lhs, acc.modified);
        }
        let scalar_deref_field_zero = matches!(
            lhs.projection.as_slice(),
            [ProjectionElem::Deref, ProjectionElem::Field(0, field_ty)] if *field_ty == local_ty
        ) && strip_spurious_deref;
        if scalar_deref_field_zero {
            // Part of #3768: graceful fallback instead of panic on unregistered locals
            let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
                self.projection_sound_fallback(local_idx, "state_idx_missing_scalar_deref", acc);
                return;
            };
            if let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
            {
                let out_var = Expr::var(&*out_name, out_sort.clone());
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, rhs_expr.clone(), &out_sort, false)
                {
                    self.encode.local_expr_env.insert(local_idx, rhs_expr);
                    acc.replace_constraint(local_idx, constraint);
                    acc.modified.insert(local_idx);
                } else {
                    warn!(
                        local_idx,
                        ?lhs,
                        "CHC: scalar deref-field projection sort mismatch — constraint dropped"
                    );
                    self.projection_sound_fallback(local_idx, "proj_sort_mismatch", acc);
                }
            } else {
                warn!(
                    local_idx,
                    vec_idx,
                    output_state_len = self.state_var_mgr.output_state_vars.len(),
                    "CHC: scalar deref-field projection missing output slot"
                );
                self.projection_sound_fallback(local_idx, "proj_missing_state_var", acc);
            }
            return;
        }

        let flattened_deref_field = self.flatten.flattened_tuple_locals.contains(&local_idx)
            && matches!(lhs.projection.first(), Some(ProjectionElem::Deref));
        let proj_slice = if flattened_deref_field || strip_spurious_deref {
            &lhs.projection[1..]
        } else {
            lhs.projection.as_slice()
        };

        // Flattened locals can appear with a no-op leading Deref after range lowering
        // (pattern: [Deref, Field(..)]). Handle this directly to avoid routing through
        // pointer-store handlers that expect pointer-typed base locals.
        if flattened_deref_field {
            let field_projections = collect_field_projections(
                proj_slice,
                UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
            );
            if field_projections.len() == 1 {
                self.encode_flattened_field_projection(
                    rhs_expr,
                    local_idx,
                    &field_projections[0],
                    acc,
                );
            } else {
                warn!(?lhs, "CHC: unsupported flattened deref projection — sound fallback");
                self.projection_sound_fallback(local_idx, "proj_unsupported_deref", acc);
            }
            return;
        }

        // Deref store at Mem level: *ptr = value, (*ptr).field = value (#1100)
        if !strip_spurious_deref
            && self.handle_deref_store_mem_level(lhs, &rhs_expr, local_idx, bb_idx, acc)
        {
            return;
        }

        // Array element store via Index/ConstantIndex (#1739)
        if self.handle_array_element_store(lhs, rhs_expr.clone(), local_idx, acc) {
            return;
        }

        // Part of #3561: Mixed Field+Index projection assignment (e.g., _N.data[i] = rhs).
        if self.handle_field_index_store(lhs, rhs_expr.clone(), local_idx, acc) {
            return;
        }

        // Deref store at Reg level via ref_targets (#1957)
        if !strip_spurious_deref
            && self.handle_deref_store_via_ref_targets(lhs, rhs_expr.clone(), local_idx, acc)
        {
            return;
        }

        // Part of #2967: Fallback for Deref+Field on pointer locals whose ref_target is
        // a flattened bv-encoded struct (e.g., std::slice::Iter/IterMut encoded as bv128).
        // The Mem-level handler defers when ref_targets exists (deref_mem.rs:64), and the
        // ref_targets handler fails because apply_projection_update can't handle bv128 sort.
        // Resolve through ref_targets and route to the flattened field projection path.
        //
        // Part of #3041: Use collect_field_projections_with_downcast to preserve Downcast
        // cons_idx in the projection chain, enabling correct payload slot resolution for
        // BV-flattened multi-ctor enums via EnumBvLayout.
        //
        // Part of #3041: Guard: skip this fallback when the LHS contains Index/ConstantIndex
        // after the Deref. Those patterns must be handled by handle_lhs_index_through_ref_target_projs
        // in the ref_targets handler above. Without this guard, the fallback drops the Index
        // projection and overwrites the whole payload field as a scalar.
        let lhs_has_index_after_deref = lhs.projection[1..]
            .iter()
            .any(|p| matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }));
        if lhs_base_is_pointer && lhs_has_deref && !lhs_has_index_after_deref {
            if let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx) {
                let target_local = ref_target.local;
                if self.flatten.flattened_tuple_locals.contains(&target_local) {
                    let mut combined_field_projs = collect_field_projections(
                        &ref_target.projections,
                        UnknownProjectionPolicy::Skip,
                    );
                    combined_field_projs.extend(collect_field_projections(
                        &lhs.projection[1..],
                        UnknownProjectionPolicy::Break,
                    ));
                    if combined_field_projs.len() == 1 {
                        debug!(
                            local_idx,
                            target_local,
                            field_idx = combined_field_projs[0].field_idx,
                            cons_idx = ?combined_field_projs[0].cons_idx,
                            "CHC: Deref+Field fallback to flattened ref_target (#2967)"
                        );
                        self.encode_flattened_field_projection(
                            rhs_expr,
                            target_local,
                            &combined_field_projs[0],
                            acc,
                        );
                        return;
                    }
                }
            }
        }

        // Real deref stores that survive the Reg-level handlers require the
        // Mem-level store path. Request a retry at Mem so `*box = ...` and
        // similar wrapper-backed writes do not fall through to projection
        // sound fallback.
        if lhs_has_deref
            && lhs_base_is_pointer
            && self.track_level < crate::args::ChcTrackLevel::Mem
        {
            self.needs_mem_promote = true;
            warn!(
                ?lhs,
                track_level = ?self.track_level,
                "CHC: deref store requires mem-track promotion"
            );
            return;
        }

        let field_projections = collect_field_projections(
            proj_slice,
            UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
        );

        // Part of #2214: Flattened locals (tuples, Option, Result) -
        // field projection assignment directly constrains the scalar
        // state var. For enums (Downcast+Field), cons_idx is Some
        // and payload is always at vec_idx + 1.
        if self.flatten.flattened_tuple_locals.contains(&local_idx) && field_projections.len() == 1
        {
            self.encode_flattened_field_projection(rhs_expr, local_idx, &field_projections[0], acc);
            return;
        }

        // Part of #2989: Multi-level field projections on recursively flattened locals.
        // For nested single-constructor ADTs, compute the leaf slot offset and write
        // directly to that scalar state var while preserving all other fields.
        if self.flatten.flattened_tuple_locals.contains(&local_idx)
            && field_projections.len() > 1
            && field_projections.iter().all(|fp| fp.cons_idx.is_none())
        {
            if let Some(local_decl) = self.body.locals().get(local_idx)
                && let Some(sort) = Self::translate_ty(local_decl.ty)
            {
                let field_indices: Vec<usize> =
                    field_projections.iter().map(|fp| fp.field_idx).collect();
                if let Some(leaf_slot) = compute_nested_flat_slot(&sort, &field_indices) {
                    self.encode_flattened_field_slot(rhs_expr, local_idx, leaf_slot, acc);
                    return;
                }
            }
            // Fall through to datatype functional update if slot computation fails.
        }

        if field_projections.is_empty() {
            // Other unsupported projection types
            warn!(?lhs, "CHC: unsupported projection type (no field projections) — sound fallback");
            self.projection_sound_fallback(local_idx, "proj_no_field_projections", acc);
            return;
        }

        // Part of #3041: Union field projection assignment (e.g., `u.g = 42`).
        // All union fields overlap at offset 0, so writing any field is writing
        // the entire union. Coerce the RHS to the union's BV width.
        // For ZST field writes (e.g., `u.f = ()`), the write is a no-op.
        if let TyKind::RigidTy(RigidTy::Adt(def, _)) = local_ty.kind() {
            if def.kind() == rustc_public::ty::AdtKind::Union {
                // Part of #3768: graceful fallback instead of panic
                let Some(proj_vec_idx) = self.try_state_idx_for_local(local_idx) else {
                    self.projection_sound_fallback(local_idx, "state_idx_missing_union_proj", acc);
                    return;
                };
                if let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(proj_vec_idx).cloned()
                {
                    // Check if the field being written is ZST.
                    let field_is_zst = field_projections
                        .last()
                        .and_then(|fp| fp.field_ty)
                        .and_then(|ty| ty.layout().ok())
                        .map(|l| l.shape().size.bytes() == 0)
                        .unwrap_or(false);

                    if field_is_zst {
                        // ZST field write is a no-op — union value unchanged.
                        debug!(local_idx, "CHC: union ZST field write — no-op");
                        return;
                    }

                    // Non-ZST field: coerce RHS to union BV width and assign.
                    if let Some(target_width) = out_sort.bitvec_width() {
                        let coerced = coerce_bitvec_width_safe(
                            rhs_expr,
                            target_width,
                            SignExtension::ZeroExtend,
                        );
                        let out_var = Expr::var(&*out_name, out_sort);
                        acc.replace_constraint(local_idx, out_var.eq(coerced.clone()));
                        self.encode.local_expr_env.insert(local_idx, coerced);
                        acc.modified.insert(local_idx);
                        debug!(local_idx, target_width, "CHC: union field write — coerced to BV");
                        return;
                    }
                }
                // Fall through to datatype update if state var missing.
            }
        }

        // Regular field projection with datatype functional update
        self.encode_datatype_field_update(lhs, rhs_expr, local_idx, &field_projections, acc);
    }

    /// Encode a regular datatype field update via functional update.
    ///
    /// Resolves the root expression, applies `apply_projection_update`, and
    /// constrains the output variable with sort-safe equality.
    fn encode_datatype_field_update(
        &mut self,
        _lhs: &Place,
        rhs_expr: Expr,
        local_idx: usize,
        field_projections: &[FieldProjection],
        acc: &mut StmtAccumulator<'_>,
    ) {
        // Get the root expression, using expr env or OUTPUT for modified locals
        // Fix #2055: Check local_expr_env first
        // Fix #2238: Use local_to_state_idx mapping for correct vector index
        // Part of #3768: graceful fallback instead of panic
        let Some(proj_vec_idx) = self.try_state_idx_for_local(local_idx) else {
            self.projection_sound_fallback(local_idx, "state_idx_missing_dt_field_update", acc);
            return;
        };
        let root_in = if acc.modified.contains(&local_idx) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&local_idx) {
                env_expr.clone()
            } else {
                let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(proj_vec_idx)
                else {
                    warn!(
                        local_idx,
                        proj_vec_idx,
                        "CHC: datatype field update missing output state var — recording fallback"
                    );
                    // Local is already in `modified` (branch condition above);
                    // helper re-insert is a no-op.
                    self.projection_sound_fallback(local_idx, "proj_missing_state_var", acc);
                    return;
                };
                Expr::var(&**out_name, out_sort.clone())
            }
        } else {
            let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(proj_vec_idx) else {
                warn!(
                    local_idx,
                    proj_vec_idx,
                    "CHC: datatype field update missing input state var — recording fallback"
                );
                self.projection_sound_fallback(local_idx, "proj_missing_state_var", acc);
                return;
            };
            Expr::var(&**in_name, in_sort.clone())
        };

        let updated = if root_in.sort().is_bitvec() {
            let local_ty = self.body.locals()[local_idx].ty;
            Self::bv_projection_update(&root_in, local_ty, field_projections, rhs_expr.clone())
                .or_else(|| Self::apply_projection_update(&root_in, field_projections, rhs_expr))
        } else {
            Self::apply_projection_update(&root_in, field_projections, rhs_expr)
        };

        if let Some(updated_expr) = updated {
            // Get output variable for the root local
            if let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(proj_vec_idx)
            {
                let out_var = Expr::var(&**out_name, out_sort.clone());
                // Part of #2244: use coerce_eq_constraint for sort-safe
                // equality. Datatype field updates may produce a different
                // sort than the declared output variable.
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, updated_expr.clone(), out_sort, false)
                {
                    // Fix #2055: Record updated whole value in expression env
                    self.encode.local_expr_env.insert(local_idx, updated_expr);
                    // Fix #2055: Replace previous constraint for same local
                    acc.replace_constraint(local_idx, constraint);
                    acc.modified.insert(local_idx);
                } else {
                    warn!(
                        local_idx,
                        ?proj_vec_idx,
                        "CHC: datatype field update sort mismatch — constraint dropped"
                    );
                    self.projection_sound_fallback(local_idx, "proj_sort_mismatch", acc);
                }
            } else {
                warn!(
                    local_idx,
                    proj_vec_idx,
                    output_state_len = self.state_var_mgr.output_state_vars.len(),
                    "CHC: projection output slot missing — constraint dropped"
                );
                self.projection_sound_fallback(local_idx, "proj_missing_state_var", acc);
            }
        } else {
            warn!(
                local_idx,
                projection_depth = field_projections.len(),
                "CHC: apply_projection_update failed — constraint dropped"
            );
            self.projection_sound_fallback(local_idx, "proj_update_failed", acc);
        }
    }
}
