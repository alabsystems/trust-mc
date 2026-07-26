// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Slice provenance resolution, equality via provenance, and IndexMut tracking.
//!
//! Extracted from `codegen_call_slice_helpers.rs` — Part of #4206.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Provenance-based shortcut for slice equality (Part of #3495).
    ///
    /// When both slice operands trace to the same const_ref_values backing array
    /// AND have the same subslice_offset, they reference identical data. Returns
    /// `Expr::bool_const(true)` in that case, avoiding the need for element-by-element
    /// comparison which fails when the SMT arrays are syntactically different expressions
    /// representing the same logical data.
    ///
    /// This handles the pattern in subslice3.rs where `tail @ ..` and `&slice[1..]`
    /// both derive from the same promoted constant array with offset 1.
    pub(in crate::codegen_ay::chc) fn try_slice_eq_via_provenance(
        &self,
        args: &[Operand],
    ) -> Option<Expr> {
        let lhs_local = match args.first()? {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };
        let rhs_local = match args.get(1)? {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };

        // Resolve each operand to a local with const_ref_values metadata,
        // following ref_targets chains (up to 5 hops to avoid cycles).
        let lhs_resolved = self.resolve_provenance_local(lhs_local);
        let rhs_resolved = self.resolve_provenance_local(rhs_local);

        let lhs_val = self.ref_resolution.const_ref_values.get(&lhs_resolved)?;
        let rhs_val = self.ref_resolution.const_ref_values.get(&rhs_resolved)?;

        // Check backing array identity via expression equality.
        if lhs_val != rhs_val {
            return None;
        }

        // Check subslice_offset equality. Both None (offset 0) or both same value.
        let lhs_off = self.ref_resolution.subslice_offset.get(&lhs_resolved);
        let rhs_off = self.ref_resolution.subslice_offset.get(&rhs_resolved);
        match (lhs_off, rhs_off) {
            (None, None) => {}
            (Some(l), Some(r)) if l == r => {}
            _ => return None,
        }

        // Check subslice_len: only reject if both are set but differ.
        // When one side lacks explicit len metadata (e.g., range-based subslice
        // vs pattern-based subslice), trust backing array + offset identity.
        let lhs_len = self.ref_resolution.subslice_len.get(&lhs_resolved);
        let rhs_len = self.ref_resolution.subslice_len.get(&rhs_resolved);
        if let (Some(l), Some(r)) = (lhs_len, rhs_len) {
            if l != r {
                return None;
            }
        }

        debug!(
            fn_name = %self.fn_name,
            lhs_local,
            rhs_local,
            lhs_resolved,
            rhs_resolved,
            "SlicePartialEq: provenance match — same backing array + offset + len"
        );
        Some(Expr::bool_const(true))
    }

    /// Resolve a local through ref_targets and Copy/Move chains to find the
    /// underlying local that carries const_ref_values metadata.
    ///
    /// Part of #3495: Slice equality operands are often intermediate locals
    /// created for call arguments. The actual provenance metadata lives on
    /// the original local from which the reference was taken.
    pub(in crate::codegen_ay::chc) fn resolve_provenance_local(&self, mut local: usize) -> usize {
        for _ in 0..8 {
            if self.ref_resolution.const_ref_values.contains_key(&local) {
                return local;
            }
            // Try ref_targets: _arg = &_source
            if let Some(rt) = self.ref_resolution.ref_targets.get(&local) {
                if rt.projections.is_empty() {
                    local = rt.local;
                    continue;
                }
            }
            // Try Copy/Move chains through MIR statements.
            let mut found = false;
            for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    if let rustc_public::mir::StatementKind::Assign(lhs, rhs) = &stmt.kind
                        && lhs.local == local
                    {
                        if let rustc_public::mir::Rvalue::Ref(_, _, place) = rhs {
                            if place.projection.is_empty() {
                                local = place.local;
                                found = true;
                                break;
                            }
                            // Follow direct reborrows like `_4 = &_1` and
                            // box-backed `&(*_26)` receivers used by range
                            // indexing before slice backing resolution.
                            if place.projection.len() == 1
                                && matches!(
                                    place.projection[0],
                                    rustc_public::mir::ProjectionElem::Deref
                                )
                            {
                                local = place.local;
                                found = true;
                                break;
                            }
                        }
                        // Part of #4098: Follow Cast (e.g., Unsize from
                        // &[T; N] to &[T]) so Box deref temps that go
                        // through an Unsize cast share provenance with
                        // the original Box local.
                        if let rustc_public::mir::Rvalue::Cast(
                            _,
                            Operand::Copy(p) | Operand::Move(p),
                            _,
                        ) = rhs
                        {
                            if p.projection.is_empty() {
                                local = p.local;
                                found = true;
                                break;
                            }
                            if p.projection.iter().all(|proj| {
                                matches!(proj, rustc_public::mir::ProjectionElem::Field(..))
                            }) {
                                local = p.local;
                                found = true;
                                break;
                            }
                        }
                        if let rustc_public::mir::Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) =
                            rhs
                        {
                            if p.projection.is_empty() {
                                local = p.local;
                                found = true;
                                break;
                            }
                            // Part of #3495: Follow single-Deref projections.
                            // MIR pattern: `_29 = Copy((*_27))` where _27 is the
                            // reference local carrying provenance metadata.
                            if p.projection.len() == 1
                                && matches!(
                                    p.projection[0],
                                    rustc_public::mir::ProjectionElem::Deref
                                )
                            {
                                local = p.local;
                                found = true;
                                break;
                            }
                            if p.projection.len() == 1
                                && let ProjectionElem::Field(field_idx, _) = p.projection[0]
                                && let Some(src_local) =
                                    self.resolve_aggregate_field_source_local(p.local, field_idx)
                            {
                                local = src_local;
                                found = true;
                                break;
                            }
                        }
                    }
                }
                if found {
                    break;
                }
            }
            if !found {
                break;
            }
        }
        local
    }

    /// Like `resolve_provenance_local` but traces all the way to the root
    /// allocation without stopping at `const_ref_values` entries.
    ///
    /// Part of #4098: For subslice cache keys, we need the root allocation
    /// local (e.g., the Box local) rather than an intermediate local that
    /// happens to have slice data. Two `&(*_box)` temps both trace to the
    /// same Box local, producing identical cache keys.
    pub(in crate::codegen_ay::chc) fn resolve_provenance_root(&self, mut local: usize) -> usize {
        for _iter in 0..8 {
            // Try ref_targets: _arg = &_source
            if let Some(rt) = self.ref_resolution.ref_targets.get(&local) {
                if rt.projections.is_empty() {
                    local = rt.local;
                    continue;
                }
            }
            // Try Copy/Move/Cast/Ref chains through MIR statements.
            let mut found = false;
            for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    if let rustc_public::mir::StatementKind::Assign(lhs, rhs) = &stmt.kind
                        && lhs.local == local
                    {
                        if let rustc_public::mir::Rvalue::Ref(_, _, place) = rhs {
                            if place.projection.is_empty() {
                                local = place.local;
                                found = true;
                                break;
                            }
                            if place.projection.len() == 1
                                && matches!(
                                    place.projection[0],
                                    rustc_public::mir::ProjectionElem::Deref
                                )
                            {
                                local = place.local;
                                found = true;
                                break;
                            }
                        }
                        if let rustc_public::mir::Rvalue::Cast(
                            _,
                            Operand::Copy(p) | Operand::Move(p),
                            _,
                        ) = rhs
                        {
                            if p.projection.is_empty() {
                                local = p.local;
                                found = true;
                                break;
                            }
                            if p.projection.iter().all(|proj| {
                                matches!(proj, rustc_public::mir::ProjectionElem::Field(..))
                            }) {
                                local = p.local;
                                found = true;
                                break;
                            }
                        }
                        if let rustc_public::mir::Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) =
                            rhs
                        {
                            if p.projection.is_empty() {
                                local = p.local;
                                found = true;
                                break;
                            }
                            if p.projection.len() == 1
                                && matches!(
                                    p.projection[0],
                                    rustc_public::mir::ProjectionElem::Deref
                                )
                            {
                                local = p.local;
                                found = true;
                                break;
                            }
                        }
                    }
                }
                if found {
                    break;
                }
            }
            if !found {
                break;
            }
        }
        local
    }

    fn resolve_aggregate_field_source_local(
        &self,
        aggregate_local: usize,
        field_idx: usize,
    ) -> Option<usize> {
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if lhs.local != aggregate_local || !lhs.projection.is_empty() {
                    continue;
                }
                let Rvalue::Aggregate(_, operands) = rhs else { continue };
                let operand = operands.get(field_idx)?;
                let (Operand::Copy(place) | Operand::Move(place)) = operand else { continue };
                if place.projection.is_empty() {
                    return Some(place.local);
                }
                if place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
                {
                    return Some(place.local);
                }
            }
        }
        None
    }

    /// Register IndexMut tracking so that `*dest = val` propagates to Vec fld_data.
    ///
    /// Part of #3348: When `IndexMut::index_mut(slice, idx)` returns `&mut T`,
    /// the dest local is recorded in `collection_mut_refs` with the Vec local and
    /// index expression. The deref-store handler uses this to emit
    /// `data' = store(data, idx, val)` on the backing array.
    ///
    /// Part of #3357: When IndexMut is called directly on `&mut Vec<T>` (not
    /// through an intermediate VecAsSlice/deref_mut), `slice_to_vec_local` has
    /// no entry. Fallback resolves the Vec local through `ref_targets` (same
    /// pattern as `resolve_collection_local`).
    pub(in crate::codegen_ay::chc) fn register_index_mut_tracking(
        &mut self,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
        dest_local: usize,
    ) {
        self.register_index_tracking_impl(args, modified_locals, dest_local, false);
    }

    /// Read-side analog of [`Self::register_index_mut_tracking`] for immutable
    /// `Index::index` results.
    ///
    /// Contract modifies clauses name collection elements with immutable
    /// borrows (`#[kani::modifies(&v[0])]`); the replace shim then casts the
    /// reference to `*mut T` (`kani::internal::Pointer::assignable`) and
    /// havocs through `write_any_slim`. Recording the same
    /// `(collection_local, index_expr)` context in `collection_index_refs`
    /// (a SEPARATE map that ordinary deref-store handlers never consult) lets
    /// the write_any collection-havoc lane resolve the target while read-only
    /// index results stay invisible to store propagation.
    pub(in crate::codegen_ay::chc) fn register_index_read_tracking(
        &mut self,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
        dest_local: usize,
    ) {
        self.register_index_tracking_impl(args, modified_locals, dest_local, true);
    }

    fn register_index_tracking_impl(
        &mut self,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
        dest_local: usize,
        read_only: bool,
    ) {
        let (slice_arg, index_arg) = self.split_chc_slice_index_args(args);

        // Extract slice local from operand.
        let slice_local = match slice_arg {
            Operand::Copy(place) | Operand::Move(place) => place.local,
            Operand::Constant(_) => return,
        };

        // Resolve Vec local: first try slice→vec mapping (set by VecAsSlice),
        // then fall back to ref_targets resolution for direct Vec IndexMut.
        // Part of #3439: preserve field projections for struct-embedded Vec.
        // When deref_mut resolves through a struct field (e.g., `(*_self).marks`),
        // slice_to_vec_local maps to the struct local and the field projections
        // are recorded separately in slice_to_vec_field_projections.
        let (vec_local, field_projections) =
            if let Some(&vl) = self.ref_resolution.slice_to_vec_local.get(&slice_local) {
                let projs = self
                    .ref_resolution
                    .slice_to_vec_field_projections
                    .get(&slice_local)
                    .cloned()
                    .unwrap_or_default();
                (vl, projs)
            } else if let Some(rt) = self.ref_resolution.ref_targets.get(&slice_local) {
                // Part of #3357: IndexMut called directly on &mut Vec<T> without
                // intermediate VecAsSlice/deref_mut. Resolve through ref_targets
                // (same as resolve_collection_local) to find the underlying Vec local.
                // Part of #3439: when ref_targets has projections (Vec is a struct field),
                // preserve them so handle_collection_mut_ref_store can reconstruct.
                (rt.local, rt.projections.clone())
            } else {
                (slice_local, vec![])
            };

        // Compute index expression.
        let Some(idx_expr) = index_arg
            .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals))
            .and_then(|expr| self.coerce_to_pointer_width(expr))
        else {
            debug!(
                fn_name = %self.fn_name,
                "IndexMut: cannot resolve index expr; skipping mut ref tracking"
            );
            return;
        };

        debug!(
            fn_name = %self.fn_name,
            dest_local,
            vec_local,
            read_only,
            field_projections_len = field_projections.len(),
            "IndexMut: registered collection_mut_ref for deferred store (#3348/#3357/#3439)"
        );

        let entry = super::codegen_ctx::types::CollectionMutRef {
            collection_local: vec_local,
            index_expr: idx_expr,
            field_projections,
        };
        if read_only {
            self.ref_resolution.collection_index_refs.insert(dest_local, entry);
        } else {
            self.ref_resolution.collection_mut_refs.insert(dest_local, entry);
        }
    }
}
