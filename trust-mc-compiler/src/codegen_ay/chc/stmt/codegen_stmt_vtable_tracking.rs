// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vtable discriminant tracking for dyn dispatch in CHC encoding.
//!
//! Extracted from `codegen_stmt_mirror.rs` per #4130 to keep files
//! under 500 lines. Contains methods for capturing, propagating, and
//! clearing vtable discriminants through CHC state variables.

use std::sync::Arc;

use ay_bindings::{Expr, Sort};
use tracing::{debug, warn};

use crate::codegen_ay::types::CtorFieldExt;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// When `translate_rvalue` produces a `Dyn_Trait{fld_ptr, fld_vtable}` expression
    /// for an unsize coercion, extract and store the `fld_vtable` field so that
    /// virtual dispatch can recover it later. Must be called before sort coercion
    /// strips the datatype structure.
    ///
    /// Returns an `Option<Expr>` constraint (`vtable_out = vtable_val`) that the
    /// caller MUST push to the block constraints. This makes the vtable a CHC
    /// state variable, ensuring path-sensitivity across branches.
    pub(in crate::codegen_ay::chc) fn capture_vtable_discriminant(
        &mut self,
        local_idx: usize,
        rhs_expr: &Expr,
    ) -> Option<Expr> {
        let sort = rhs_expr.sort().clone();
        let dt = sort.datatype_sort()?;
        let cons = dt.constructors.first()?;
        if !cons.has_field("fld_vtable") {
            return None;
        }
        let vtable_expr = rhs_expr.clone().field_select(
            &dt.name,
            "fld_vtable",
            Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
        );
        // Keep the compile-time side-table for single-block cases.
        self.dyn_vtable_ids.insert(local_idx, vtable_expr.clone());

        // Create or reuse a CHC state variable for path-sensitive tracking.
        let (in_name, out_name) = self.get_or_create_vtable_state_var(local_idx);
        // Mark the vtable state variable as modified so the rule generator
        // emits out_var in the output args (not identity in=out).
        if let Some(idx) = self.state_var_index_by_name(&in_name) {
            self.mark_state_var_modified(idx);
        }
        let out_var = Expr::var(&*out_name, Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH));
        Some(out_var.eq(vtable_expr))
    }

    /// Record a known vtable discriminant on a local without requiring a Dyn_Trait RHS.
    ///
    /// This is used for wrapper-dyn values like `Box<dyn Trait>` loaded from memory:
    /// the loaded expression is a thin pointer bitvector, but the MIR body may still
    /// uniquely determine the concrete vtable from its Unsize coercion site.
    pub(in crate::codegen_ay::chc) fn capture_known_vtable_discriminant(
        &mut self,
        local_idx: usize,
        vtable_expr: Expr,
    ) -> Option<Expr> {
        self.dyn_vtable_ids.insert(local_idx, vtable_expr.clone());

        let (in_name, out_name) = self.get_or_create_vtable_state_var(local_idx);
        if let Some(idx) = self.state_var_index_by_name(&in_name) {
            self.mark_state_var_modified(idx);
        }
        let out_var = Expr::var(&*out_name, Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH));
        Some(out_var.eq(vtable_expr))
    }

    /// Part of #3869: Capture vtable discriminant for PointerCoercion::Unsize casts
    /// where the target wraps `dyn Trait` but the expression is a thin pointer (BV64).
    ///
    /// For `_dst = _src as Box<dyn Identity>`, the rhs_expr is BV64 so
    /// `capture_vtable_discriminant` fails (no `fld_vtable` in DT sort), and
    /// `propagate_vtable_discriminant` fails because the source `Box<Inner>` has
    /// no vtable entry. This method resolves the vtable ID from the concrete source
    /// type against the target's dyn trait candidates.
    pub(in crate::codegen_ay::chc) fn try_capture_unsize_coercion_vtable(
        &mut self,
        rhs: &rustc_public::mir::Rvalue,
        dst_local: usize,
    ) -> Option<Expr> {
        use rustc_public::mir::{CastKind, PointerCoercion};

        let rustc_public::mir::Rvalue::Cast(
            CastKind::PointerCoercion(PointerCoercion::Unsize),
            operand,
            target_ty,
        ) = rhs
        else {
            return None;
        };

        let target_inner = super::super::dyn_coercion::peel_pointer_like_wrapper_ty(*target_ty);
        super::super::dyn_coercion::find_dyn_trait_tail_ty(self, target_inner)?;

        let src_ty = operand.ty(self.body.locals()).ok()?;
        let src_inner = super::super::dyn_coercion::peel_pointer_like_wrapper_ty(src_ty);
        let concrete_ty =
            super::super::dyn_coercion::extract_concrete_tail_for_dyn(src_inner, target_inner);
        let vtable_id = super::super::dyn_coercion::resolve_dyn_target_vtable_id(
            self,
            target_inner,
            concrete_ty,
        )?;
        self.capture_known_vtable_discriminant(
            dst_local,
            Expr::bitvec_const(vtable_id as u128, crate::codegen_ay::types::POINTER_WIDTH),
        )
    }

    /// Clear any stored vtable tracking for a local and make the CHC output
    /// state unconstrained for this step instead of inheriting stale input state.
    pub(in crate::codegen_ay::chc) fn clear_known_vtable_discriminant(&mut self, local_idx: usize) {
        self.dyn_vtable_ids.remove(&local_idx);

        if let Some((in_name, _out_name)) = self.vtable_state_vars.get(&local_idx)
            && let Some(idx) = self.state_var_index_by_name(in_name)
        {
            self.mark_state_var_modified(idx);
        }
    }

    /// Propagate vtable discriminant through Copy/Move (Part of #3159).
    ///
    /// When `_dst = move _src` and `_src` has a stored vtable ID, `_dst`
    /// inherits it so virtual dispatch can look it up.
    ///
    /// Returns an `Option<Expr>` constraint (`dst_vtable_out = src_vtable`)
    /// for path-sensitive propagation via CHC state variables.
    pub(in crate::codegen_ay::chc) fn propagate_vtable_discriminant(
        &mut self,
        src_local: usize,
        dst_local: usize,
    ) -> Option<Expr> {
        // Keep the compile-time side-table for single-block cases.
        if let Some(vtable_expr) = self.dyn_vtable_ids.get(&src_local).cloned() {
            self.dyn_vtable_ids.insert(dst_local, vtable_expr);
        }

        // Propagate via CHC state variables for path-sensitive tracking.
        let (src_in, src_out) = self.vtable_state_vars.get(&src_local)?.clone();
        // Part of #4217: record propagation edge for reachability-based pruning.
        self.vtable_propagation_edges.insert(dst_local, src_local);
        let (dst_in, dst_out) = self.get_or_create_vtable_state_var(dst_local);
        // Mark the destination vtable state variable as modified.
        if let Some(idx) = self.state_var_index_by_name(&dst_in) {
            self.mark_state_var_modified(idx);
        }
        // Part of #3159: If the source vtable state var was already modified
        // in this block (e.g., by capture_vtable_discriminant for the same
        // block's Unsize coercion), use the __out name so the propagation
        // reads the newly captured value, not the stale predecessor input.
        let src_modified = self
            .state_var_index_by_name(&src_in)
            .map(|idx| self.encode.modified_state_indices.contains(&idx))
            .unwrap_or(false);
        let src_name: &str = if src_modified { &src_out } else { &src_in };
        let src_var = Expr::var(src_name, Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH));
        let dst_var = Expr::var(&*dst_out, Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH));
        Some(dst_var.eq(src_var))
    }

    /// Get or create a CHC state variable pair for vtable tracking (Part of #3159).
    ///
    /// Returns (input_name, output_name). Creates a late state variable pair
    /// on first call for a given local_idx.
    /// Part of #2267: returns Arc<str> pair — clones are cheap Arc bumps.
    pub(in crate::codegen_ay::chc) fn get_or_create_vtable_state_var(
        &mut self,
        local_idx: usize,
    ) -> (Arc<str>, Arc<str>) {
        if let Some(names) = self.vtable_state_vars.get(&local_idx) {
            return names.clone();
        }
        // Part of #2267: pre-allocate instead of format!().
        use std::fmt::Write;
        let mut in_name = String::with_capacity(20);
        in_name.push_str("__vtable_sv_");
        let _ = write!(in_name, "{local_idx}");
        let mut out_name = String::with_capacity(25);
        out_name.push_str("__vtable_sv_");
        let _ = write!(out_name, "{local_idx}");
        out_name.push_str("__out");
        let sort = Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH);
        // Part of #2267: create Arc<str> first, then share via O(1) clones
        // instead of cloning the String (O(n)) then converting to Arc.
        let in_arc: Arc<str> = Arc::from(in_name);
        let out_arc: Arc<str> = Arc::from(out_name);
        super::push_pending_var_decl(Arc::clone(&in_arc), sort.clone());
        super::push_pending_var_decl(Arc::clone(&out_arc), sort.clone());
        self.state_var_mgr.push_state_var_pair_arc(Arc::clone(&in_arc), &out_arc, sort);
        debug!(
            local_idx,
            in_name = %in_arc,
            "created vtable state variable for path-sensitive tracking (#3159)"
        );
        self.vtable_state_vars.insert(local_idx, (Arc::clone(&in_arc), Arc::clone(&out_arc)));
        (in_arc, out_arc)
    }
}

/// Enforce the constraint-or-unchanged invariant for a basic block.
///
/// Part of #3038, #3526: Every MIR local in `modified` must have a binding
/// constraint tracked in `last_constraint_for_local`. Locals that are modified
/// without a constraint are removed from `modified` so that
/// `build_block_output_args` uses INPUT vars for them (identity/unchanged).
/// This is a sound over-approximation: the modification is ignored rather than
/// leaving the output variable nondeterministic.
///
/// Part of #3517: accepts `StmtAccumulator` instead of raw `modified` + `last_constraint_for_local`.
/// Returns the number of locals that were repaired.
/// Part of #3447: the caller uses this count to increment a diagnostic counter
/// so that CTREX classification reports OverApproximation instead of Genuine.
///
/// Part of #3138: Previously removed unconstrained locals from `modified`,
/// which caused identity-copy (out = in) — unsound because dropped stores
/// preserve stale values instead of being universally quantified. Now emits
/// a tautological `true` constraint for each unconstrained local, keeping it
/// in `modified` so its output variable is genuinely universally quantified
/// by PDR. This fixes 29+ store failure sites that add locals to `modified`
/// without emitting a constraint.
pub(in crate::codegen_ay::chc) fn enforce_modified_constraint_invariant(
    bb_idx: usize,
    acc: &mut super::stmt_accumulator::StmtAccumulator<'_>,
) -> usize {
    let unconstrained: Vec<usize> = acc
        .modified
        .iter()
        .copied()
        .filter(|idx| !acc.last_constraint_for_local.contains_key(idx))
        .collect();
    let fixup_count = unconstrained.len();
    if fixup_count > 0 {
        warn!(
            "CHC: bb{} has {} modified locals with no binding constraint: {:?} — \
             emitting tautological constraint (universally quantified, sound). See #3038, #3138.",
            bb_idx, fixup_count, unconstrained,
        );
        for &idx in &unconstrained {
            // Part of #3138: Emit `true` constraint instead of removing from
            // modified. This keeps the local in last_constraint_for_local and
            // modified, so build_block_output_args uses the OUTPUT variable
            // (universally quantified) rather than INPUT (identity-copy).
            super::stmt_accumulator::replace_constraint_in(
                acc.constraints,
                acc.last_constraint_for_local,
                idx,
                ay_bindings::Expr::bool_const(true),
            );
        }
    }
    fixup_count
}
