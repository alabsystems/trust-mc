// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec length resolution and type inspection utilities.
//!
//! Extracted from `codegen_call_vec_ops_len.rs` — Part of #4206.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, ProjectionElem};
use std::collections::HashSet;
use std::sync::Arc;
use tracing::debug;

use super::ChcCtx;
use super::codegen_call_vec::ChcVecFields;
use super::codegen_ctx::types::CollectionProjectionKind;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Traces the argument through ref_targets and slice_to_vec_local to find
    /// the tracked length of the underlying collection. Returns the input
    /// (block-entry) length following the same convention as `vec_op_push`
    /// and `vec_op_clone`.
    ///
    /// Strategy order:
    /// 1. Direct sidecar len_var on arg_local
    /// 2. Trace through ref_targets, then sidecar
    /// 3. slice_to_vec_local → sidecar
    /// 4. iter_to_collection_local → sidecar
    /// 5. Direct fld_len read from Vec's AY Datatype (for Vecs received as
    ///    function parameters without sidecar tracking)
    pub(in crate::codegen_ay) fn resolve_slice_arg_length(
        &self,
        args: &[Operand],
        arg_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let arg = args.get(arg_idx)?;
        let arg_local = match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return None,
        };

        // Strategy 1: arg directly has a tracked length
        if let Some(len_var) = self.collections.len_state.get_len_var(arg_local).cloned() {
            return Some(self.collection_current_len(&len_var));
        }

        // Strategy 2: trace through ref_targets to find the source collection
        let resolved =
            self.ref_resolution.ref_targets.get(&arg_local).map(|rt| rt.local).unwrap_or(arg_local);

        if resolved != arg_local {
            if let Some(len_var) = self.collections.len_state.get_len_var(resolved).cloned() {
                return Some(self.collection_current_len(&len_var));
            }
        }

        // Collect candidate Vec locals from strategies 3 and 4 for sidecar + fallback.
        let mut vec_candidates: Vec<usize> = Vec::new();

        // Strategy 3: check slice_to_vec_local mapping (from VecAsSlice/deref)
        if let Some(&vec_local) = self.ref_resolution.slice_to_vec_local.get(&arg_local) {
            if let Some(len_var) = self.collections.len_state.get_len_var(vec_local).cloned() {
                return Some(self.collection_current_len(&len_var));
            }
            vec_candidates.push(vec_local);
        }
        if resolved != arg_local {
            if let Some(&vec_local) = self.ref_resolution.slice_to_vec_local.get(&resolved) {
                if let Some(len_var) = self.collections.len_state.get_len_var(vec_local).cloned() {
                    return Some(self.collection_current_len(&len_var));
                }
                if !vec_candidates.contains(&vec_local) {
                    vec_candidates.push(vec_local);
                }
            }
        }

        // Strategy 4: check iter_to_collection_local mapping (from VecIter/VecIntoIter)
        // Part of #3348: Rust desugars extend_from_slice to spec_extend(self, iter),
        // where the iterator was constructed from the source slice via Vec::iter().
        if let Some(&coll_local) = self.ref_resolution.iter_to_collection_local.get(&arg_local) {
            if let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() {
                return Some(self.collection_current_len(&len_var));
            }
            if !vec_candidates.contains(&coll_local) {
                vec_candidates.push(coll_local);
            }
        }
        if resolved != arg_local {
            if let Some(&coll_local) = self.ref_resolution.iter_to_collection_local.get(&resolved) {
                if let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() {
                    return Some(self.collection_current_len(&len_var));
                }
                if !vec_candidates.contains(&coll_local) {
                    vec_candidates.push(coll_local);
                }
            }
        }

        // Strategy 5: Direct fld_len read from Vec's AY Datatype expression.
        // When the source Vec was not created in this function (e.g., received
        // as a field of a struct parameter), it has no sidecar len tracking.
        // Fall back to reading the Vec's fld_len field directly from the AY
        // Datatype. Part of #3348.
        for &vec_local in &vec_candidates {
            if let Some(len_expr) = self.try_read_vec_fld_len(vec_local, modified_locals) {
                tracing::debug!(vec_local, "resolve_slice_arg_length: Strategy 5 fld_len fallback");
                return Some(len_expr);
            }
        }

        None
    }

    /// Read the `fld_len` field directly from a Vec's AY Datatype expression.
    ///
    /// This is the fallback for Vecs that were not created in the current
    /// function scope (e.g., struct fields received as parameters). These Vecs
    /// have no sidecar len tracking, but their AY Datatype representation
    /// includes `fld_len` as a bitvec field that encodes the entry-state length.
    ///
    /// Handles both flattened Vecs (decomposed into per-field state vars) and
    /// non-flattened Vecs (single Datatype state var).
    fn try_read_vec_fld_len(
        &self,
        vec_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Try the given local first, then trace through ref_targets if it's a
        // pointer/reference (BitvecSort). When VecAsSlice records
        // slice_to_vec_local, the target may be the &Vec local (a pointer),
        // not the Vec value itself. Part of #3348.
        let ref_target = self.ref_resolution.ref_targets.get(&vec_local).map(|rt| rt.local);
        let candidates = [Some(vec_local), ref_target];
        for candidate in candidates.into_iter().flatten() {
            if let Some(expr) = self.try_read_vec_fld_len_inner(candidate, modified_locals) {
                return Some(expr);
            }
        }
        None
    }

    pub(in crate::codegen_ay::chc) fn local_is_vec_shaped(
        &self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> bool {
        if self.collections.projection_locals.get(&local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            return true;
        }
        self.try_resolve_local_expr(local, modified_locals)
            .and_then(ChcVecFields::extract)
            .is_some()
    }

    /// Part of #4057: Check if a type is `Vec<T>` or `&Vec<T>` (possibly nested refs).
    pub(in crate::codegen_ay::chc) fn is_vec_or_ref_to_vec(ty: rustc_public::ty::Ty) -> bool {
        use rustc_public::CrateDef;
        use rustc_public::ty::{RigidTy, TyKind};
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => def.name().contains("Vec"),
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Self::is_vec_or_ref_to_vec(inner),
            _ => false,
        }
    }

    /// Part of #4057: When a ref-chase matches a tracked local whose len_var
    /// is uninitialized (e.g., `vec_main_len_40` for a closure-captured `&Vec`),
    /// follow the ref_target chain to find the source Vec's len_var.
    ///
    /// The chain: tracked_local=40 → ref_target=(5, [Field(0, &Vec<T>)])
    /// means local 40 is a reference to closure_env.field0 which is `&Vec<T>`.
    /// The actual Vec is at the root — find a tracked local with `ref_target=None`
    /// whose len_var IS initialized (constrained in the init rule).
    pub(in crate::codegen_ay::chc) fn resolve_source_vec_len_var(
        &self,
        matched_local: usize,
        default_len_var: &str,
    ) -> Arc<str> {
        // Check if matched_local's ref_target field type is &Vec<T>.
        // If so, the tracked len_var for this local is likely uninitialized.
        let Some(rt) = self.ref_resolution.ref_targets.get(&matched_local) else {
            return Arc::from(default_len_var);
        };
        // Check if the last projection is a Field with &Vec<T> type.
        let is_ref_to_vec = rt.projections.last().map_or(false, |proj| {
            if let ProjectionElem::Field(_, ty) = proj {
                matches!(
                    ty.kind(),
                    rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(_, _, _))
                ) && Self::is_vec_or_ref_to_vec(*ty)
            } else {
                false
            }
        });
        if !is_ref_to_vec {
            return Arc::from(default_len_var);
        }
        // The ref_target points to a struct field that is &Vec<T>.
        // Find the source Vec: look for tracked locals that directly track
        // the original Vec (ref_target=None, or direct ref to it).
        // Strategy: find any tracked local with ref_target=None — that's
        // the original Vec local whose len_var IS initialized.
        for (&source_local, source_len_var) in &self.collections.len_state.len_var_names {
            if source_local == matched_local {
                continue;
            }
            // Prefer a tracked local with no ref_target (the original Vec).
            if !self.ref_resolution.ref_targets.contains_key(&source_local) {
                debug!(
                    fn_name = %self.fn_name,
                    matched_local,
                    source_local,
                    %source_len_var,
                    %default_len_var,
                    "VecLen #4057: resolved closure-captured &Vec ref to source Vec len_var"
                );
                return source_len_var.clone();
            }
        }
        Arc::from(default_len_var)
    }

    /// Inner helper: attempt to read fld_len from a single local.
    fn try_read_vec_fld_len_inner(
        &self,
        vec_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Flattened path: Vec was decomposed into (ptr, len, cap, data) state vars.
        if self.collections.projection_locals.get(&vec_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            // IDX_LEN = 1 (fld_len is the second field in the Vec layout)
            return self.flattened_local_field_expr(vec_local, 1, modified_locals);
        }

        // Non-flattened path: Vec is a single Datatype state variable.
        let vec_expr = self.try_resolve_local_expr(vec_local, modified_locals)?;
        if !vec_expr.sort().is_datatype() {
            return None;
        }
        Self::select_vec_len_datatype_field(&vec_expr)
    }
}
