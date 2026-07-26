// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Subslice length tracing through MIR Copy/Move chains.
//! Extracted from `codegen_stmt_ptr_metadata.rs` per #4130.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{
    AggregateKind, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;
use tracing::debug;

use super::ChcCtx;
use crate::codegen_ay::types::POINTER_WIDTH;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #3495: trace subslice_len through Copy/Move chains. Phase
    /// ordering fix: when the chain reaches a Call result, compute the
    /// subslice length directly from the Call's Range arguments.
    pub(super) fn trace_subslice_len_through_copies(
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
                            // Part of #4163: Also trace through Ref/AddressOf with
                            // Deref-prefixed projections. Covers:
                            //   `_N = &mut (*_M)` — custom DST reborrows
                            //   `_N = &((*_M).field)` — reference to unsized field
                            // Taking a reference to a field of an unsized struct
                            // preserves the subslice_len metadata from the base.
                            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                                if place.projection.is_empty()
                                    || (place.projection.first()
                                        == Some(&ProjectionElem::Deref)) =>
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

    /// Part of #3495: compute subslice length from a Call's Range/RangeInclusive
    /// arguments, resolving phase ordering where PtrMetadata encodes before the
    /// SliceIndex::index Call that would normally set subslice_len.
    fn try_compute_subslice_len_from_call(
        &self,
        current_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
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

    /// Trace a local through Ref/AddressOf/Use/Cast to find the referent local.
    /// Part of #4163: Uses multi-hop tracing (up to 4 hops) and handles Cast
    /// (PtrToPtr, Unsize) to resolve through unsize coercions like
    /// `&[T; N]` → `&[T]` that appear between array construction and indexing.
    fn trace_local_to_referent(&self, local: usize) -> Option<usize> {
        let mut current = local;
        let mut visited = HashSet::new();
        while visited.len() < 4 && visited.insert(current) {
            let mut next = None;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                        && lhs.local == current
                        && lhs.projection.is_empty()
                    {
                        match rvalue {
                            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                                if place.projection.is_empty()
                                    || (place.projection.len() == 1
                                        && matches!(place.projection[0], ProjectionElem::Deref))
                                {
                                    next = Some(place.local);
                                }
                            }
                            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                                if place.projection.is_empty() =>
                            {
                                next = Some(place.local);
                            }
                            // Part of #4163: Trace through Cast (PtrToPtr, Unsize).
                            // `_slice_ref = Cast(Unsize, _ref, &[T])` — follow to _ref.
                            Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                                if src.projection.is_empty() =>
                            {
                                next = Some(src.local);
                            }
                            _ => {}
                        }
                    }
                }
            }
            match next {
                Some(n) => current = n,
                None => break,
            }
        }
        // Return the final traced local if we moved at all.
        if current != local { Some(current) } else { None }
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

    /// Part of #4163: Resolve subslice_len from a MIR Index projection.
    ///
    /// When `_N = Copy((*_array_ref)[_idx])` or `_N = Copy(_array[_idx])`,
    /// find the array local, look up its `Aggregate(Array, ...)` construction,
    /// and return the shared subslice_len from the aggregate elements.
    fn try_resolve_subslice_len_from_index_proj(&self, dest_local: usize) -> Option<Expr> {
        // Find the assignment to dest_local with an Index projection in the source.
        let mut array_local = None;
        let mut index_local = None;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                    && lhs.local == dest_local
                    && lhs.projection.is_empty()
                {
                    let source_place = match rvalue {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => Some(p),
                        Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p) => Some(p),
                        _ => None,
                    };
                    if let Some(place) = source_place {
                        // Look for Index projection in the place.
                        // Patterns: _array[_idx], (*_ref)[_idx]
                        for proj in &place.projection {
                            if let ProjectionElem::Index(idx) = proj {
                                let base = place.local;
                                array_local = Some(base);
                                index_local = Some(*idx);
                                break;
                            }
                        }
                    }
                }
            }
        }
        let array_local = array_local?;

        // Trace through Ref/Deref to find the actual array storage local.
        // Pattern: _ref = &_array, then (*_ref)[_idx] — resolve _ref → _array.
        let storage_local = self.trace_ref_to_storage(array_local);

        // Find the Aggregate(Array, ...) that created the storage local.
        self.resolve_subslice_len_from_array_aggregate(storage_local, index_local)
    }

    /// Trace a reference local through Ref/AddressOf/Cast to find the storage local.
    /// Part of #4163: Also handles Cast (PtrToPtr, Unsize) to trace through
    /// unsize coercions (`&[T; N]` -> `&[T]`) that sit between the array Ref
    /// and the index projection.
    fn trace_ref_to_storage(&self, start: usize) -> usize {
        let mut current = start;
        let mut visited = HashSet::new();
        while visited.len() < 4 && visited.insert(current) {
            let mut next = None;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                        && lhs.local == current
                        && lhs.projection.is_empty()
                    {
                        match rvalue {
                            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                                if place.projection.is_empty()
                                    || (place.projection.len() == 1
                                        && matches!(place.projection[0], ProjectionElem::Deref))
                                {
                                    next = Some(place.local);
                                }
                            }
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                                if p.projection.is_empty() =>
                            {
                                next = Some(p.local);
                            }
                            // Part of #4163: Trace through Cast (PtrToPtr, Unsize).
                            Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                                if src.projection.is_empty() =>
                            {
                                next = Some(src.local);
                            }
                            _ => {}
                        }
                    }
                }
            }
            match next {
                Some(n) => current = n,
                None => break,
            }
        }
        current
    }

    /// Given an array local, find its Aggregate construction and resolve
    /// subslice_len from the element locals. If all elements share the same
    /// expression, returns it directly. If they differ, builds an ITE chain
    /// over the index variable (when available) to select the correct length.
    fn resolve_subslice_len_from_array_aggregate(
        &self,
        array_local: usize,
        index_local: Option<usize>,
    ) -> Option<Expr> {
        let mut element_locals: Vec<usize> = Vec::new();
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
                                    element_locals.push(p.local);
                                }
                            }
                        }
                    }
                }
            }
        }
        if element_locals.is_empty() {
            return None;
        }

        // Collect subslice_len for each element position.
        let mut element_lens: Vec<Option<Expr>> = Vec::new();
        let mut any_found = false;
        let mut all_same = true;
        let mut first_len: Option<Expr> = None;
        for &elem_local in &element_locals {
            if let Some(len) = self.ref_resolution.subslice_len.get(&elem_local) {
                if let Some(ref first) = first_len {
                    if first != len {
                        all_same = false;
                    }
                } else {
                    first_len = Some(len.clone());
                }
                element_lens.push(Some(len.clone()));
                any_found = true;
            } else {
                element_lens.push(None);
                all_same = false;
            }
        }
        if !any_found {
            return None;
        }

        // Fast path: all elements have the same subslice_len.
        if all_same {
            debug!(
                array_local,
                element_count = element_locals.len(),
                "PtrMetadata: resolved uniform subslice_len from array aggregate"
            );
            return first_len;
        }

        // Slow path: elements have different subslice_len. Build ITE chain
        // over the index variable: ite(idx == 0, len0, ite(idx == 1, len1, ...))
        let idx_local = index_local?;
        // Resolve the index local to a AY expression using input state vars.
        let idx_expr = {
            let empty_modified = HashSet::new();
            self.try_resolve_local_expr(idx_local, &empty_modified)?
        };
        // Coerce index to pointer width for ITE comparisons.
        let idx_bv = match idx_expr.sort().bitvec_width() {
            Some(w) if w == POINTER_WIDTH => idx_expr,
            Some(w) if w < POINTER_WIDTH => idx_expr.zero_extend(POINTER_WIDTH - w),
            Some(_) => idx_expr.extract(POINTER_WIDTH - 1, 0),
            None => return None,
        };

        // Build ITE chain from last to first.
        let fallback = first_len?;
        let mut result = fallback;
        for (i, elem_len) in element_lens.iter().enumerate().rev() {
            if let Some(len) = elem_len {
                let cond = idx_bv.clone().eq(Expr::bitvec_const(i as i64, POINTER_WIDTH));
                result = Expr::ite(cond, len.clone(), result);
            }
        }
        debug!(
            array_local,
            idx_local,
            element_count = element_locals.len(),
            "PtrMetadata: resolved heterogeneous subslice_len via ITE over array index"
        );
        Some(result)
    }
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
#[path = "codegen_stmt_ptr_metadata_copy_trace_test.rs"]
mod test_wrappers;
