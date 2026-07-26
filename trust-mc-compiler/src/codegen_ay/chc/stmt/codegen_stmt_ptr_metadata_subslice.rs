// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Subslice length tracing helpers for PtrMetadata resolution.
//!
//! Extracted from `codegen_stmt_ptr_metadata.rs` per #4130 to keep files under 500 lines.
//! Contains: trace_subslice_len_through_copies, try_compute_subslice_len_from_call,
//! try_resolve_subslice_len_from_index_call, trace_local_to_referent,
//! find_array_aggregate_elements, uniform_subslice_len_from_elements,
//! try_resolve_subslice_len_from_index_proj, trace_ref_to_storage,
//! resolve_subslice_len_from_array_aggregate.

use std::collections::HashSet;

use rustc_public::CrateDef;
use rustc_public::mir::{
    AggregateKind, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use tracing::debug;
use ay_bindings::Expr;

use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Trace through MIR Copy/Move assignment chains to find a local with
    /// `subslice_len` metadata.
    ///
    /// When `_5 = Copy(_2)` and `subslice_len[_2]` exists, this returns the
    /// subslice length expression for `_5`. Follows chains up to 8 hops deep.
    ///
    /// Part of #3495: subslice_len is set during rule generation for the
    /// destination of `codegen_call_slice_range_index`, but downstream uses
    /// may reference a Copy of that local.
    ///
    /// Phase ordering fix: When the chain reaches a Call result (e.g.,
    /// `_2 = SliceIndex::index(range, slice)`), the subslice_len side table
    /// may not yet be populated because blocks are encoded in MIR array index
    /// order, not execution order. In this case, we compute the subslice
    /// length directly from the Call's Range arguments.
    pub(in crate::codegen_ay::chc) fn trace_subslice_len_through_copies(
        &self,
        start_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let mut current = start_local;
        let mut visited = HashSet::new();
        // Max 8 hops to prevent infinite loops.
        while visited.len() < 8 && visited.insert(current) {
            // Scan MIR for the assignment to `current`.
            let mut source_local = None;
            let mut is_call_result = false;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                        && lhs.local == current
                        && lhs.projection.is_empty()
                    {
                        match rvalue {
                            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                                if place.projection.is_empty()
                                    || (place.projection.len() == 1
                                        && matches!(
                                            place.projection[0],
                                            ProjectionElem::Deref
                                        )) =>
                            {
                                // Bare local: `_N = Copy(_M)` — follow the alias.
                                // Part of #3495: Single Deref: `_N = Copy(*_M)` —
                                // after function inlining, callee parameters receive
                                // fat pointers via `Copy(*_param_ref)`. Trace through
                                // the deref to follow the reference chain.
                                source_local = Some(place.local);
                            }
                            // Part of #4163: Also trace through Ref with Deref projection
                            // (`_N = &mut (*_M)`) which appears in custom DST reborrows.
                            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                                if place.projection.is_empty()
                                    || (place.projection.len() == 1
                                        && matches!(
                                            place.projection[0],
                                            ProjectionElem::Deref
                                        )) =>
                            {
                                source_local = Some(place.local);
                            }
                            // Part of #4163: Trace through Cast (PtrToPtr, Unsize).
                            Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                                if src.projection.is_empty() =>
                            {
                                source_local = Some(src.local);
                            }
                            _ => {}
                        }
                    }
                }
                // Also check terminators for Call results.
                if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
                    && destination.local == current
                {
                    is_call_result = true;
                }
            }
            // Part of #4163: Handle Index projection into arrays.
            // `_N = Copy((*_array_ref)[_idx])` — trace the array local back to
            // its Aggregate(Array, ...) construction and check element locals
            // for subslice_len. This handles the pattern where fat pointers are
            // stored in fixed-size arrays and loaded back via MIR Index projection.
            if source_local.is_none() && !is_call_result {
                if let Some(len) = self.try_resolve_subslice_len_from_index_proj(current) {
                    return Some(len);
                }
            }
            // For Call results, try to compute subslice_len from Range args.
            // This resolves the phase ordering issue where the SliceIndex::index
            // Call block hasn't been encoded yet when PtrMetadata needs the length.
            if is_call_result {
                if let Some(len) = self.try_compute_subslice_len_from_call(current, modified_locals)
                {
                    return Some(len);
                }
                // Part of #4163: For indexing calls that return fat pointer elements
                // (e.g., `my_slice[0]` where elements are `&mut MyStr`), trace through
                // the array aggregate to find the element's subslice_len.
                if let Some(len) = self.try_resolve_subslice_len_from_index_call(current) {
                    return Some(len);
                }
            }
            match source_local {
                Some(src) => {
                    if let Some(len) = self.ref_resolution.subslice_len.get(&src) {
                        return Some(len.clone());
                    }
                    current = src;
                }
                None => break,
            }
        }
        None
    }

    /// Compute subslice length from a Call terminator's Range arguments.
    ///
    /// When a Call terminator targeting `current_local` has a `Range<usize>` or
    /// `RangeInclusive<usize>` argument, extract start/end fields from the
    /// flattened state and compute the subslice length.
    ///
    /// Part of #3495: Resolves phase ordering where PtrMetadata blocks are
    /// encoded before the SliceIndex::index Call block that would normally
    /// set subslice_len[dest_local].
    fn try_compute_subslice_len_from_call(
        &self,
        current_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use rustc_public::ty::{RigidTy, TyKind};

        for block in &self.body.blocks {
            let TerminatorKind::Call { args, destination, .. } = &block.terminator.kind else {
                continue;
            };
            if destination.local != current_local {
                continue;
            }
            // Check each argument for Range/RangeInclusive type.
            for arg in args {
                let Ok(ty) = arg.ty(self.body.locals()) else {
                    continue;
                };
                let (is_range, is_inclusive) = match ty.kind() {
                    TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                        let name = def.trimmed_name();
                        (name == "Range" || name == "RangeInclusive", name == "RangeInclusive")
                    }
                    _ => (false, false),
                };
                if !is_range {
                    continue;
                }
                // Extract the Range local index.
                let range_local = match arg {
                    Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                        place.local
                    }
                    _ => continue,
                };
                // Get start (field 0) and end (field 1) from flattened state.
                // Inlined from flattened_local_field_expr (call/ pub(crate)
                // not accessible from stmt/).
                let get_field = |field_idx: usize| -> Option<Expr> {
                    if let Some(expr) =
                        self.encode.flattened_field_env.get(&(range_local, field_idx))
                    {
                        return Some(expr.clone());
                    }
                    let base_idx = self.try_state_idx_for_local(range_local)?;
                    let slot = base_idx + field_idx;
                    let vars = if modified_locals.contains(&range_local) {
                        &self.state_var_mgr.output_state_vars
                    } else {
                        &self.state_var_mgr.state_vars
                    };
                    vars.get(slot).map(|(name, sort)| Expr::var(&**name, sort.clone()))
                };
                let start = get_field(0)?;
                let end = get_field(1)?;
                // Coerce to pointer width bitvector.
                let coerce = |expr: Expr| -> Option<Expr> {
                    match expr.sort().bitvec_width() {
                        Some(w) if w == POINTER_WIDTH => Some(expr),
                        Some(w) if w < POINTER_WIDTH => Some(expr.zero_extend(POINTER_WIDTH - w)),
                        Some(_) => Some(expr.extract(POINTER_WIDTH - 1, 0)),
                        None => None,
                    }
                };
                let start_bv = coerce(start)?;
                let end_bv = coerce(end)?;
                let len = if is_inclusive {
                    end_bv.bvsub(start_bv).bvadd(Expr::bitvec_const(1, POINTER_WIDTH))
                } else {
                    end_bv.bvsub(start_bv)
                };
                debug!(
                    fn_name = %self.fn_name,
                    current_local,
                    range_local,
                    is_inclusive,
                    "PtrMetadata: computed subslice_len from Call Range args (phase ordering fix)"
                );
                return Some(len);
            }
        }
        None
    }

    /// Part of #4163: Resolve subslice_len from an indexing Call.
    ///
    /// When a Call result is produced by an indexing operation
    /// (e.g., `my_slice[0]` → `Index::index(my_slice, 0)`), trace back through
    /// the array/slice to find the element's subslice_len.
    fn try_resolve_subslice_len_from_index_call(&self, result_local: usize) -> Option<Expr> {
        // Find the Call terminator for result_local.
        let mut call_args = None;
        for block in &self.body.blocks {
            if let TerminatorKind::Call { args, destination, .. } = &block.terminator.kind
                && destination.local == result_local
            {
                call_args = Some(args.clone());
                break;
            }
        }
        let args = call_args?;
        if args.is_empty() {
            return None;
        }

        // The first arg is typically the collection reference (&[T] or &[T; N]).
        let collection_local = match &args[0] {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };
        let array_local = self.trace_local_to_referent(collection_local)?;
        let element_locals = self.find_array_aggregate_elements(array_local);
        if element_locals.is_empty() {
            return None;
        }

        self.uniform_subslice_len_from_elements(&element_locals)
    }

    /// Trace a local through Ref/AddressOf/Use to find the referent local.
    fn trace_local_to_referent(&self, local: usize) -> Option<usize> {
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                    && lhs.local == local
                    && lhs.projection.is_empty()
                {
                    match rvalue {
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            return Some(place.local);
                        }
                        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                            if place.projection.is_empty() =>
                        {
                            return Some(place.local);
                        }
                        _ => {}
                    }
                }
            }
        }
        None
    }

    /// Find element locals from an `Aggregate(Array, ...)` assignment.
    fn find_array_aggregate_elements(&self, array_local: usize) -> Vec<usize> {
        let mut elements = Vec::new();
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                    && lhs.local == array_local
                    && lhs.projection.is_empty()
                {
                    if let Rvalue::Aggregate(AggregateKind::Array(_), operands) = rvalue {
                        for op in operands {
                            if let Operand::Copy(p) | Operand::Move(p) = op {
                                if p.projection.is_empty() {
                                    elements.push(p.local);
                                }
                            }
                        }
                    }
                }
            }
        }
        elements
    }

    /// Return the uniform subslice_len shared by all elements, or None.
    fn uniform_subslice_len_from_elements(&self, elements: &[usize]) -> Option<Expr> {
        let mut found_len: Option<Expr> = None;
        for &elem_local in elements {
            if let Some(len) = self.ref_resolution.subslice_len.get(&elem_local) {
                if let Some(ref existing) = found_len {
                    if existing != len {
                        return None;
                    }
                } else {
                    found_len = Some(len.clone());
                }
            }
        }
        found_len
    }

    // Array-aggregate subslice resolution methods extracted to
    // codegen_stmt_ptr_metadata_subslice_array.rs per #4130.
}
