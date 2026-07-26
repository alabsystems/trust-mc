// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Read-only SSA expression resolution helpers for `ChcCtx`.
//!
//! Extracted from `codegen_ctx/mod.rs` per #3254 packet 2.

use std::collections::HashSet;

use ay_bindings::Expr;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve a local variable to its current SSA Expr.
    /// Uses `output_state_vars` if the local was modified in this block,
    /// otherwise uses input `state_vars`.
    ///
    /// Returns `None` when the local has no state-var mapping (sound fallback).
    /// Use `try_resolve_local_expr` as an alias — both are now graceful.
    pub(in crate::codegen_ay::chc) fn resolve_local_expr(
        &self,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Part of #3768: graceful fallback instead of panic on unregistered locals
        let vec_idx = self.try_state_idx_for_local(local_idx)?;
        let (name, sort) = if modified_locals.contains(&local_idx) {
            self.state_var_mgr.output_state_vars.get(vec_idx)?
        } else {
            self.state_var_mgr.state_vars.get(vec_idx)?
        };
        Some(Expr::var(&**name, sort.clone()))
    }

    /// Like `resolve_local_expr` but returns `None` when the local has no
    /// state-var mapping instead of panicking. Used in store paths where
    /// unmapped locals are handled gracefully.
    pub(in crate::codegen_ay::chc) fn try_resolve_local_expr(
        &self,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let vec_idx = self.try_state_idx_for_local(local_idx)?;
        let (name, sort) = if modified_locals.contains(&local_idx) {
            self.state_var_mgr.output_state_vars.get(vec_idx)?
        } else {
            self.state_var_mgr.state_vars.get(vec_idx)?
        };
        Some(Expr::var(&**name, sort.clone()))
    }

    /// Resolve the pointee expression for a reference local backed by
    /// `ref_arg_pointee_idx`.
    ///
    /// Returns the auxiliary pointee state-var index, the synthetic track key
    /// used for intra-block write-then-read chaining, and the current pointee
    /// expression. This mirrors the arg-ref deref read/store paths.
    fn resolve_aux_state_var_expr(&self, state_var_idx: usize) -> Option<(usize, Expr)> {
        let track_key = usize::MAX - state_var_idx;
        let expr = if let Some(env_expr) = self.encode.local_expr_env.get(&track_key) {
            env_expr.clone()
        } else if self.encode.modified_state_indices.contains(&state_var_idx) {
            let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(state_var_idx)?;
            Expr::var(&**out_name, out_sort.clone())
        } else {
            let (in_name, in_sort) = self.state_var_mgr.state_vars.get(state_var_idx)?;
            Expr::var(&**in_name, in_sort.clone())
        };
        Some((track_key, expr))
    }

    pub(in crate::codegen_ay::chc) fn resolve_arg_ref_pointee_expr(
        &self,
        ref_local: usize,
    ) -> Option<(usize, usize, Expr)> {
        let pointee_vec_idx = *self.ref_resolution.ref_arg_pointee_idx.get(&ref_local)?;
        let (track_key, pointee_expr) = self.resolve_aux_state_var_expr(pointee_vec_idx)?;
        Some((pointee_vec_idx, track_key, pointee_expr))
    }

    /// Resolve a coroutine root expression from either a concrete local or a
    /// synthesized argument-pointee slot.
    /// Resolve a coroutine root state expression tuple `(state_idx, track_key, expr)`
    /// from the `coroutine_root_map`. Used by both `SetDiscriminant` and `Discriminant`
    /// handlers to resolve deref-based coroutine state access.
    /// Part of #3807: shared across stmt modules for both write and read paths.
    pub(in crate::codegen_ay::chc) fn resolve_coroutine_root_state_expr(
        &self,
        local_idx: usize,
    ) -> Option<(usize, usize, Expr)> {
        let root_state_idx = *self.ref_resolution.coroutine_root_map.get(&local_idx)?;
        let track_key = usize::MAX - root_state_idx;
        let root_expr = if let Some(env_expr) = self.encode.local_expr_env.get(&track_key) {
            env_expr.clone()
        } else if self.encode.modified_state_indices.contains(&root_state_idx) {
            let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(root_state_idx)?;
            Expr::var(&**out_name, out_sort.clone())
        } else {
            let (in_name, in_sort) = self.state_var_mgr.state_vars.get(root_state_idx)?;
            Expr::var(&**in_name, in_sort.clone())
        };
        Some((root_state_idx, track_key, root_expr))
    }

    pub(in crate::codegen_ay::chc) fn resolve_coroutine_root_expr(
        &self,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if let Some(&root_state_idx) = self.ref_resolution.coroutine_root_map.get(&local_idx) {
            let (_, root_expr) = self.resolve_aux_state_var_expr(root_state_idx)?;
            if crate::codegen_ay::types::coroutine_discriminant_select(root_expr.clone()).is_some()
            {
                return Some(root_expr);
            }
        }

        let local_expr = self
            .encode
            .local_expr_env
            .get(&local_idx)
            .cloned()
            .or_else(|| self.resolve_local_expr(local_idx, modified_locals));
        if let Some(expr) = local_expr
            && crate::codegen_ay::types::coroutine_discriminant_select(expr.clone()).is_some()
        {
            return Some(expr);
        }

        let (_, _, pointee_expr) = self.resolve_arg_ref_pointee_expr(local_idx)?;
        crate::codegen_ay::types::coroutine_discriminant_select(pointee_expr.clone())?;
        Some(pointee_expr)
    }
}
