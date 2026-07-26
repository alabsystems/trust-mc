// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Struct-embedded Vec len/is_empty operations (C1/C2 paths).
//!
//! Extracted from `codegen_call_vec_ops_len.rs` to keep files under 500 lines.
//! Contains VecLen struct-embedded dispatch (C1 Datatype, C2 flattened) and
//! VecIsEmpty with its own struct-embedded support.
//!
//! Part of #3348: struct-embedded Vec support enables proof of properties on
//! struct-wrapped Vecs (e.g., `CnfClause(Vec<CnfLit>).0.is_empty()`) where
//! the sidecar len_var can't be resolved through the wrapper.

use ay_bindings::Expr;
use rustc_public::mir::ProjectionElem;
use std::collections::HashSet;
use tracing::debug;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::POINTER_WIDTH;
use rustc_public::ty::{RigidTy, TyKind};

use super::ChcCtx;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_vec::ChcVecFields;
use super::codegen_decl_flatten::collect_leaf_sorts;
use super::codegen_types::CodegenTypes;
use super::{UnknownProjectionPolicy, collect_field_projections};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve the owning struct type for a struct-embedded Vec access.
    ///
    /// `resolve_collection_local()` may return an `&self`/`&mut self` local for
    /// wrapper methods. Flattened C2 handlers need the pointee struct type, not
    /// the reference shell, to recover field offsets for tuple/newtype wrappers.
    pub(in crate::codegen_ay::chc) fn struct_embedded_owner_ty(
        &self,
        coll_local: usize,
    ) -> Option<rustc_public::ty::Ty> {
        let local_ty = self.body.locals().get(coll_local)?.ty;
        Some(match local_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            _ => local_ty,
        })
    }

    // ── VecLen struct-embedded ───────────────────────────────────────

    /// VecLen struct-embedded: read len from struct's Vec field.
    ///
    /// Handles two sub-cases mirroring the VecPush struct handler (#3348):
    /// - C1: Datatype struct — navigate Datatype selectors to Vec's fld_len
    /// - C2: Flattened struct — read flat leaf at base + IDX_LEN
    ///
    /// Part of #3348: VecLen on struct-embedded Vec.
    pub(in crate::codegen_ay::chc) fn vec_len_struct_embedded(
        &mut self,
        coll_local: usize,
        dest_local: usize,
        field_projections: &[ProjectionElem],
        modified_locals: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let struct_state_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied());
        let Some(struct_state_idx) = struct_state_idx else {
            debug!(coll_local, "VecLen: struct-embedded — no state var for struct local");
            acc.dests.push(dest_local);
            return;
        };
        let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(struct_state_idx).cloned()
        else {
            acc.dests.push(dest_local);
            return;
        };

        let field_projs =
            collect_field_projections(field_projections, UnknownProjectionPolicy::Skip);
        if field_projs.is_empty() {
            acc.dests.push(dest_local);
            return;
        }

        debug!(
            coll_local,
            ?struct_state_idx,
            in_name = %in_name,
            is_datatype = in_sort.datatype_name().is_some(),
            field_proj_count = field_projs.len(),
            "VecLen: struct-embedded dispatch"
        );
        if in_sort.datatype_name().is_some() {
            self.vec_len_struct_embedded_datatype(
                coll_local,
                dest_local,
                &in_name,
                &in_sort,
                &field_projs,
                acc,
            );
        } else {
            self.vec_len_struct_embedded_flattened(
                coll_local,
                dest_local,
                modified_locals,
                &field_projs,
                acc,
            );
        }
    }

    /// C1: Datatype struct — navigate to Vec field, read fld_len.
    fn vec_len_struct_embedded_datatype(
        &mut self,
        coll_local: usize,
        dest_local: usize,
        in_name: &str,
        in_sort: &ay_bindings::Sort,
        field_projs: &[super::FieldProjection],
        acc: &mut CallAccumulator<'_>,
    ) {
        let struct_in = Expr::var(in_name, in_sort.clone());

        let Some(vec_expr) = Self::apply_field_selections(struct_in, field_projs) else {
            debug!(coll_local, "VecLen: struct-embedded C1 — apply_field_selections failed");
            acc.dests.push(dest_local);
            return;
        };

        let sort_ref = vec_expr.sort().clone();
        let Some(dt_name) = sort_ref.datatype_name() else {
            debug!(coll_local, "VecLen: struct-embedded C1 — field is not a Datatype");
            acc.dests.push(dest_local);
            return;
        };

        let Some(len_expr) = Self::select_vec_len_datatype_field(&vec_expr) else {
            debug!(
                coll_local,
                %dt_name,
                "VecLen: struct-embedded C1 — selected field is not Vec-shaped"
            );
            acc.dests.push(dest_local);
            return;
        };

        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                len_expr,
                dest_var.sort(),
                dest_local,
                "VecLen::struct_embedded_C1",
            ) {
                acc.constraints.push(eq);
            }
            acc.dests.push(dest_local);
            debug!(
                fn_name = %self.fn_name,
                coll_local,
                "VecLen: struct-embedded C1 (Datatype) — len read complete (#3348)"
            );
        } else {
            acc.dests.push(dest_local);
        }
    }

    pub(crate) fn select_vec_len_datatype_field(vec_expr: &Expr) -> Option<Expr> {
        // Reuse the shared Vec-shape extractor so only actual Vec layouts can
        // surface `fld_len` through the struct-embedded C1 path.
        Some(ChcVecFields::extract(vec_expr.clone())?.len)
    }

    /// C2: Flattened struct — compute flat base offset, read len leaf.
    fn vec_len_struct_embedded_flattened(
        &mut self,
        coll_local: usize,
        dest_local: usize,
        modified_locals: &HashSet<usize>,
        field_projs: &[super::FieldProjection],
        acc: &mut CallAccumulator<'_>,
    ) {
        if field_projs.len() != 1 {
            acc.dests.push(dest_local);
            return;
        }
        let target_field_idx = field_projs[0].field_idx;

        let owner_ty = match self.struct_embedded_owner_ty(coll_local) {
            Some(ty) => ty,
            None => {
                acc.dests.push(dest_local);
                return;
            }
        };
        let struct_sort = match Self::translate_ty(owner_ty) {
            Some(s) => s,
            None => {
                acc.dests.push(dest_local);
                return;
            }
        };
        let dt = match struct_sort.datatype_sort() {
            Some(d) => d,
            None => {
                acc.dests.push(dest_local);
                return;
            }
        };
        if dt.constructors.len() != 1 || target_field_idx >= dt.constructors[0].fields.len() {
            acc.dests.push(dest_local);
            return;
        }
        let cons = &dt.constructors[0];

        let mut flat_base = 0;
        for f in &cons.fields[..target_field_idx] {
            flat_base += collect_leaf_sorts(&f.sort, 0).len();
        }

        let target_sort = &cons.fields[target_field_idx].sort;
        let target_leaves = collect_leaf_sorts(target_sort, 0);
        if target_leaves.len() != vec_layout::FIELD_COUNT
            || !target_leaves[vec_layout::IDX_DATA].is_array()
        {
            acc.dests.push(dest_local);
            return;
        }

        let Some(len_expr) = self.flattened_local_field_expr(
            coll_local,
            flat_base + vec_layout::IDX_LEN,
            modified_locals,
        ) else {
            debug!(coll_local, flat_base, "VecLen: C2 flattened_local_field_expr returned None");
            acc.dests.push(dest_local);
            return;
        };

        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                len_expr,
                dest_var.sort(),
                dest_local,
                "VecLen::struct_embedded_C2",
            ) {
                acc.constraints.push(eq);
            }
            acc.dests.push(dest_local);
            debug!(
                fn_name = %self.fn_name,
                coll_local,
                target_field_idx,
                flat_base,
                "VecLen: struct-embedded C2 (flattened) — len read complete (#3348)"
            );
        } else {
            acc.dests.push(dest_local);
        }
    }

    // ── VecIsEmpty ──────────────────────────────────────────────────

    /// VecIsEmpty: dest = (tracked_len == 0).
    ///
    /// Mirrors the three-path resolution from `vec_op_len` but produces
    /// a Bool result instead of a BV length value.
    ///
    /// Part of #3348: struct-embedded support unblocks proof_non_empty_clause_not_empty
    /// in ay_self_verify_tseitin.rs where CnfClause(Vec<CnfLit>).0.is_empty()
    /// couldn't resolve the sidecar len through the tuple struct wrapper.
    pub(in crate::codegen_ay::chc) fn vec_op_is_empty(
        &mut self,
        collection_local: Option<usize>,
        dest_local: usize,
        field_projections: &[ProjectionElem],
        modified_locals: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);

        // Path 1: Sidecar len_var — same as vec_op_len but produces len == 0.
        // Part of #3084: Skip sidecar when field_projections is non-empty.
        // See vec_op_push and vec_op_len for rationale.
        if field_projections.is_empty()
            && let Some(coll_local) = collection_local
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            let len_expr = self.collection_current_len(&len_var_name);
            let is_empty = len_expr.eq(zero);
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                if let Some(eq) = self.make_coerced_eq_constraint(
                    &dest_var,
                    is_empty,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_vec_core::VecIsEmpty",
                ) {
                    acc.constraints.push(eq);
                }
                acc.dests.push(dest_local);
            }
            return;
        }

        // Path 1.5: Ref-chase through field projections (Part of #3924, #4057).
        // Same as vec_op_len Path 1.5 but produces len == 0 instead of len.
        if !field_projections.is_empty()
            && let Some(coll_local) = collection_local
        {
            let mut len_via_ref = None;
            let mut matched_vec_local = None;
            for (&tracked_local, len_var) in &self.collections.len_state.len_var_names {
                let Some(rt) = self.ref_resolution.ref_targets.get(&tracked_local) else {
                    continue;
                };
                if rt.local != coll_local || rt.projections.len() != field_projections.len() {
                    continue;
                }
                let projs_match =
                    rt.projections.iter().zip(field_projections.iter()).all(|(a, b)| {
                        match (a, b) {
                            (ProjectionElem::Field(idx_a, _), ProjectionElem::Field(idx_b, _)) => {
                                idx_a == idx_b
                            }
                            _ => false,
                        }
                    });
                if !projs_match {
                    continue;
                }
                // Bucket A (#4046, #4057): accept when tracked local is Vec-shaped
                // OR when the field projection type is &Vec<T>.
                if !self.local_is_vec_shaped(tracked_local, modified_locals) {
                    let field_ty_is_vec_ref = rt.projections.last().map_or(false, |proj| {
                        if let ProjectionElem::Field(_, ty) = proj {
                            Self::is_vec_or_ref_to_vec(*ty)
                        } else {
                            false
                        }
                    });
                    if !field_ty_is_vec_ref {
                        continue;
                    }
                }
                matched_vec_local = Some(tracked_local);
                len_via_ref = Some(len_var.clone());
                break;
            }
            if let Some((len_var_name, matched_vec_local)) = len_via_ref.zip(matched_vec_local) {
                let effective_len_var =
                    self.resolve_source_vec_len_var(matched_vec_local, &len_var_name);
                debug!(
                    fn_name = %self.fn_name,
                    coll_local,
                    dest_local,
                    ?matched_vec_local,
                    %effective_len_var,
                    "VecIsEmpty: ref-chase through field projections (#3924, #4057)"
                );
                let len_expr = self.collection_current_len(&effective_len_var);
                let is_empty = len_expr.eq(zero);
                if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                    if let Some(eq) = self.make_coerced_eq_constraint(
                        &dest_var,
                        is_empty,
                        dest_var.sort(),
                        dest_local,
                        "VecIsEmpty::ref_chase",
                    ) {
                        acc.constraints.push(eq);
                    }
                    acc.dests.push(dest_local);
                }
                return;
            }
        }

        // Path 2: Struct-embedded Vec (Part of #3348).
        if !field_projections.is_empty()
            && let Some(coll_local) = collection_local
        {
            if let Some(len_expr) =
                self.vec_is_empty_struct_embedded(coll_local, field_projections, modified_locals)
            {
                let is_empty = len_expr.eq(zero);
                if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                    if let Some(eq) = self.make_coerced_eq_constraint(
                        &dest_var,
                        is_empty,
                        dest_var.sort(),
                        dest_local,
                        "VecIsEmpty::struct_embedded",
                    ) {
                        acc.constraints.push(eq);
                    }
                    acc.dests.push(dest_local);
                    debug!(
                        fn_name = %self.fn_name,
                        coll_local,
                        "VecIsEmpty: struct-embedded len resolved (#3348)"
                    );
                    return;
                }
            }
        }

        // Path 3: Sound fallback — leave destination unconstrained.
        // Unknown len may be 0 or >0, so constraining dest=true would
        // under-approximate to the empty branch only.
        debug!(
            fn_name = %self.fn_name,
            ?collection_local,
            "VecIsEmpty: fallback — no sidecar, no struct-embedded → unconstrained"
        );
        self.record_sound_fallback_reason("vec_is_empty_no_sidecar");
        acc.dests.push(dest_local);
    }

    /// Struct-embedded Vec len extraction for VecIsEmpty.
    ///
    /// Reuses the C1/C2 resolution pattern from vec_len_struct_embedded but
    /// returns just the len Expr instead of constraining a dest directly.
    fn vec_is_empty_struct_embedded(
        &self,
        coll_local: usize,
        field_projections: &[ProjectionElem],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let struct_state_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied())?;
        let (in_name, in_sort) = self.state_var_mgr.state_vars.get(struct_state_idx)?.clone();

        let field_projs =
            collect_field_projections(field_projections, UnknownProjectionPolicy::Skip);
        if field_projs.is_empty() {
            return None;
        }

        // C1: Datatype struct — navigate to Vec field, read fld_len.
        if in_sort.datatype_name().is_some() {
            let struct_in = Expr::var(&*in_name, in_sort);
            let vec_expr = Self::apply_field_selections(struct_in, &field_projs)?;
            return Self::select_vec_len_datatype_field(&vec_expr);
        }

        // C2: Flattened struct — compute flat base offset, read len leaf.
        if field_projs.len() != 1 {
            return None;
        }
        let target_field_idx = field_projs[0].field_idx;
        let owner_ty = self.struct_embedded_owner_ty(coll_local)?;
        let struct_sort = Self::translate_ty(owner_ty)?;
        let dt = struct_sort.datatype_sort()?;
        if dt.constructors.len() != 1 || target_field_idx >= dt.constructors[0].fields.len() {
            return None;
        }
        let cons = &dt.constructors[0];
        let mut flat_base = 0;
        for f in &cons.fields[..target_field_idx] {
            flat_base += collect_leaf_sorts(&f.sort, 0).len();
        }
        let target_sort = &cons.fields[target_field_idx].sort;
        let target_leaves = collect_leaf_sorts(target_sort, 0);
        if target_leaves.len() != vec_layout::FIELD_COUNT
            || !target_leaves[vec_layout::IDX_DATA].is_array()
        {
            return None;
        }
        self.flattened_local_field_expr(
            coll_local,
            flat_base + vec_layout::IDX_LEN,
            modified_locals,
        )
    }
}
