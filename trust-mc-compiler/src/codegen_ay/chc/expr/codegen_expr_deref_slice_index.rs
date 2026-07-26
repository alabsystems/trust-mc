// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Slice Deref+Index look-ahead for unsized `[T]` pointees.
//!
//! Part of #4099: When a fat pointer to `[T]` is dereferenced and immediately
//! indexed (`(*slice_ref)[idx]`), the generic `load_from_memory` path fails
//! because slices are unsized — it returns a scalar element instead of the
//! backing array, causing the subsequent Index projection to bail.
//!
//! This module provides `try_slice_deref_index` which detects the pattern and
//! resolves it via pointer arithmetic + element-level memory load, matching the
//! existing `slice_index_via_memory_model` strategy from the call-stub path.
//!
//! Extracted to its own file to keep `codegen_expr_deref_projection.rs` under
//! the 500 LOC threshold.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use tracing::debug;

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::ChcCtx;
use super::constant_index_offset;

/// Result of the slice Deref+Index look-ahead.
pub(in crate::codegen_ay::chc) enum SliceDerefIndexResult {
    /// Successfully resolved the combined Deref+Index to an element expression.
    /// The caller should advance `proj_idx` by 2 (skip both Deref and Index).
    Resolved { elem_expr: Expr, elem_ty: rustc_public::ty::Ty },
    /// Look-ahead not applicable (not a slice pointee, no following Index, etc.).
    /// Caller should fall through to the normal Deref path.
    NotApplicable,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Try the slice Deref+Index look-ahead at the current projection index.
    ///
    /// Checks whether `pointee_ty` is `[T]` and the next projection is Index
    /// or ConstantIndex. If so, extracts the data pointer from the fat pointer,
    /// computes the element address, and loads from the typed memory array.
    pub(in crate::codegen_ay::chc) fn try_slice_deref_index(
        &mut self,
        place: &Place,
        proj_idx: usize,
        current_expr: &Expr,
        pointee_ty: rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
        local_idx: usize,
    ) -> SliceDerefIndexResult {
        // Only applicable when the pointee is an unsized slice type.
        let elem_ty = match pointee_ty.kind() {
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Slice(elem_ty)) => elem_ty,
            _ => return SliceDerefIndexResult::NotApplicable,
        };

        let Some(next_proj) = place.projection.get(proj_idx + 1) else {
            return SliceDerefIndexResult::NotApplicable;
        };

        let result = match next_proj {
            ProjectionElem::Index(idx_local) => self.try_slice_deref_index_via_memory(
                current_expr,
                elem_ty,
                Some(*idx_local),
                None,
                modified_locals,
                local_idx,
            ),
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                let actual_offset = constant_index_offset(*offset, *min_length, *from_end);
                self.try_slice_deref_index_via_memory(
                    current_expr,
                    elem_ty,
                    None,
                    Some(actual_offset),
                    modified_locals,
                    local_idx,
                )
            }
            _ => None,
        };

        match result {
            Some(elem_expr) => SliceDerefIndexResult::Resolved { elem_expr, elem_ty },
            None => SliceDerefIndexResult::NotApplicable,
        }
    }

    /// Resolve `(*slice_ref)[index]` via const_ref_values array select or
    /// pointer arithmetic + memory element load.
    ///
    /// First checks if the slice local has a backing array registered in
    /// `const_ref_values` (from Range-based slice indexing). If so, performs a
    /// direct array select with `subslice_offset` adjustment — this is the
    /// precise path that avoids the SFB from unseeded typed memory.
    ///
    /// Falls back to extracting the data pointer from the BV128 fat pointer
    /// (lower 64 bits), computing the element address as
    /// `data_ptr + index * sizeof(T)`, and loading from the typed memory array.
    fn try_slice_deref_index_via_memory(
        &mut self,
        fat_ptr_expr: &Expr,
        elem_ty: rustc_public::ty::Ty,
        idx_local: Option<usize>,
        const_offset: Option<u64>,
        modified_locals: &HashSet<usize>,
        local_idx: usize,
    ) -> Option<Expr> {
        // Resolve the index expression (needed by both paths).
        let idx_expr = if let Some(idx_local) = idx_local {
            let raw = self.resolve_local_expr(idx_local, modified_locals)?;
            coerce_bitvec_width_safe(raw, POINTER_WIDTH, SignExtension::ZeroExtend)
        } else if let Some(offset) = const_offset {
            Expr::bitvec_const(offset as u128, POINTER_WIDTH)
        } else {
            return None;
        };

        // Part of #4099: Try const_ref_values array select before memory model.
        // When the slice was produced by Range-based indexing (e.g., &array[2..5]),
        // const_ref_values[local] holds the backing array and subslice_offset[local]
        // holds the accumulated start offset. Direct array select is precise and
        // avoids the SFB that load_from_memory produces when typed memory is unseeded.
        if let Some(elem) = self.try_slice_deref_index_via_const_ref(local_idx, &idx_expr) {
            debug!(local_idx, "CHC: slice deref+index resolved via const_ref_values array select");
            return Some(elem);
        }

        // Extract the data pointer from the fat pointer.
        // Fat pointers are BV128 = concat(len:BV64, data:BV64), data in bits [63:0].
        let data_ptr = if fat_ptr_expr.sort().bitvec_width() == Some(2 * POINTER_WIDTH) {
            fat_ptr_expr.clone().extract(POINTER_WIDTH - 1, 0)
        } else if fat_ptr_expr.sort().bitvec_width() == Some(POINTER_WIDTH) {
            // Already a thin pointer (e.g., after extract_pointer_expr).
            fat_ptr_expr.clone()
        } else {
            debug!(
                sort = ?fat_ptr_expr.sort(),
                local_idx,
                "CHC: slice deref+index: unexpected pointer sort (#4099)"
            );
            return None;
        };

        // Compute element address: data_ptr + idx * sizeof(elem).
        // Split-add keeps the obj_id lane intact for symbolic indices (#3921):
        // whole-width bvadd smears the index across the id bits and the load's
        // heap bounds check gets dropped for non-foldable obj_ids.
        let elem_size = self.get_type_size(elem_ty).unwrap_or(1) as u64;
        let byte_offset = if elem_size <= 1 {
            idx_expr
        } else {
            idx_expr.bvmul(Expr::bitvec_const(elem_size as u128, POINTER_WIDTH))
        };
        let elem_addr =
            crate::codegen_ay::chc::pointer_step::step_split_pointer(data_ptr, byte_offset).result;

        // Raw-alloc route: strict element-access bound for a slice whose base
        // local walk-resolves to a stack or `__rust_alloc` allocation (e.g.
        // `from_raw_parts(alloc_ptr, CLAIMED_LEN)[i]` — the fat pointer's
        // claimed length is a caller assertion, NOT the allocation extent;
        // `load_from_memory`'s heap_access_checks fail-open on the opaque
        // obj_id lane, so without this the claimed length is the only bound).
        let bound_checks = self.provenance_deref_bound_checks(&elem_addr, elem_ty, local_idx);
        self.heap_state.pending_checks.extend(bound_checks);

        debug!(local_idx, ?elem_size, "CHC: slice deref+index via memory model (#4099)");
        self.load_from_memory(elem_addr, elem_ty)
    }

    /// Try to resolve a slice element access via `const_ref_values` array select.
    ///
    /// Looks up the backing array in `const_ref_values` for the given local,
    /// following `ref_targets` one level if the direct lookup fails (handles
    /// MIR reborrow chains like `_y = &(*_x)` where `_x` has the entries).
    /// Applies `subslice_offset` adjustment to produce the effective index.
    fn try_slice_deref_index_via_const_ref(
        &self,
        local_idx: usize,
        idx_expr: &Expr,
    ) -> Option<Expr> {
        let (backing, offset) = self.lookup_const_ref_backing(local_idx)?;

        if !backing.sort().is_array() {
            return None;
        }

        let effective_idx =
            if let Some(off) = offset { idx_expr.clone().bvadd(off) } else { idx_expr.clone() };

        Some(backing.select(effective_idx))
    }

    /// Look up the backing array and subslice offset for a local, following
    /// `ref_targets` one level if the direct lookup misses.
    fn lookup_const_ref_backing(&self, local: usize) -> Option<(Expr, Option<Expr>)> {
        // Direct lookup.
        if let Some(backing) = self.ref_resolution.const_ref_values.get(&local) {
            let offset = self.ref_resolution.subslice_offset.get(&local).cloned();
            return Some((backing.clone(), offset));
        }

        // Follow ref_targets: if `_y = &(*_x)`, look up _x's entries.
        if let Some(referent) = self.ref_resolution.ref_targets.get(&local) {
            if referent.projections.is_empty() {
                if let Some(backing) = self.ref_resolution.const_ref_values.get(&referent.local) {
                    let offset = self.ref_resolution.subslice_offset.get(&referent.local).cloned();
                    return Some((backing.clone(), offset));
                }
            }
        }

        None
    }
}
