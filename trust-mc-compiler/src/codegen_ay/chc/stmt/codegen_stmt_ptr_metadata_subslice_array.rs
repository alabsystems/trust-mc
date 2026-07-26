// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Array-aggregate subslice length resolution helpers.
//!
//! Extracted from `codegen_stmt_ptr_metadata_subslice.rs` per #4130 to keep
//! files under 500 lines.
//! Contains: try_resolve_subslice_len_from_index_proj, trace_ref_to_storage,
//! resolve_subslice_len_from_array_aggregate.

use std::collections::HashSet;

use rustc_public::mir::{AggregateKind, Operand, ProjectionElem, Rvalue, StatementKind};
use tracing::debug;
use ay_bindings::Expr;

use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #4163: Resolve subslice_len from a MIR Index projection.
    ///
    /// When `_N = Copy((*_array_ref)[_idx])` or `_N = Copy(_array[_idx])`,
    /// find the array local, look up its `Aggregate(Array, ...)` construction,
    /// and return the shared subslice_len from the aggregate elements.
    pub(in crate::codegen_ay::chc) fn try_resolve_subslice_len_from_index_proj(
        &self,
        dest_local: usize,
    ) -> Option<Expr> {
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

    /// Trace a reference local through Ref/AddressOf to find the storage local.
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
