// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Byte-span heap access checks for the copy-family intrinsics.
//!
//! `copy` / `copy_nonoverlapping` / `write_bytes` touch a whole range
//! `[addr, addr + count * size_of::<T>())`, not a single sized access, so
//! the per-access checks in `codegen_expr_heap.rs` do not apply directly.
//! Extracted from `codegen_expr_heap.rs` to stay under the 500-line limit.

use ay_bindings::Expr;

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Generates heap bounds/alignment checks for a byte-span access —
    /// `copy` / `copy_nonoverlapping` / `write_bytes` style: the whole range
    /// `[addr, addr + count * size_of::<T>())` must lie within `addr`'s
    /// allocation, and `addr` must be aligned for `T`.
    ///
    /// Only emits when the address splits and its obj_id lane const-folds.
    /// Genuinely-unknown provenance keeps the historical skip — the
    /// allocation size is a caller contract we cannot invent (memory-model
    /// precision plan, Step 5). Returned conditions must HOLD (same contract
    /// as `heap_access_checks`).
    pub(in crate::codegen_ay::chc) fn heap_span_access_checks(
        &mut self,
        addr: &Expr,
        elem_ty: rustc_public::ty::Ty,
        count: &Expr,
    ) -> Vec<Expr> {
        let Some((obj_id, offset)) = self.split_pointer(addr) else {
            return Vec::new();
        };

        let mut checks = Vec::new();

        // Alignment is well-defined for ANY 64-bit pointer, independent of
        // whether its obj_id const-folds: the offset lane (`addr` bits 31:0)
        // is transition-constrained to the real byte offset, so `offset %
        // align == 0` is a sound obligation even when the dst obj_id is a
        // symbolic OffsetModel state var. This must precede the const-obj_id
        // early-return below, otherwise an unaligned copy dst whose provenance
        // is symbolic is proved SAFE (copy-unaligned false proof).
        if let Some(align) = self.get_type_align(elem_ty) {
            if align > 1 {
                let align_expr = Expr::bitvec_const(align as i128, 32);
                let rem = offset.clone().bvurem(align_expr);
                checks.push(rem.eq(Expr::bitvec_const(0, 32)));
            }
        }

        // The size/bounds/no-wrap/fit-alloc checks below need a const-folded
        // obj_id to resolve the allocation size — a caller contract we cannot
        // invent for genuinely-unknown provenance (memory-model precision
        // plan, Step 5). Return the alignment check alone in that case.
        let Some(const_obj_id) = Self::const_obj_id_u32(&obj_id) else {
            return checks;
        };
        let Some(elem_size) = self.get_type_size(elem_ty) else {
            return checks;
        };

        // ZST spans touch no memory — alignment is the only obligation.
        if elem_size == 0 || u32::try_from(elem_size).is_err() {
            return checks;
        }

        let count64 =
            coerce_bitvec_width_safe(count.clone(), POINTER_WIDTH, SignExtension::ZeroExtend);
        let span64 = if elem_size == 1 {
            count64
        } else {
            let size_expr = Expr::bitvec_const(elem_size as u128, POINTER_WIDTH);
            checks.push(count64.clone().bvmul_no_overflow_unsigned(size_expr.clone()));
            count64.bvmul(size_expr)
        };

        // A span that does not fit the 32-bit offset lane cannot fit any
        // allocation (obj_size is bv32): the hi lane must be zero.
        checks.push(span64.clone().extract(63, 32).eq(Expr::bitvec_const(0u128, 32)));
        let span32 = span64.extract(31, 0);

        let end_offset = offset.clone().bvadd(span32);
        checks.push(end_offset.clone().bvuge(offset));

        if let Some(alloc_size) = self.alloc_size_expr_for_const_obj_id(const_obj_id, &obj_id) {
            let zero = Expr::bitvec_const(0u64, 32);
            let is_zero_size = alloc_size.clone().eq(zero);
            checks.push(Expr::or(is_zero_size, end_offset.bvule(alloc_size)));
        }

        checks
    }

    /// Resolves the allocation size for a const-folded obj_id: stack-local
    /// layout first, then tracked heap allocations, then the `obj_size`
    /// metadata array. Mirrors the resolution order in `heap_access_checks`.
    /// Shared with the pointer-offset bound check
    /// (`ptr_offset_alloc_bound_check` in `codegen_stmt_rvalue_offset.rs`).
    pub(in crate::codegen_ay::chc) fn alloc_size_expr_for_const_obj_id(
        &mut self,
        const_obj_id: u32,
        obj_id: &Expr,
    ) -> Option<Expr> {
        if let Some(size) = self
            .heap_state
            .local_idx_for_obj_id(const_obj_id)
            .and_then(|local_idx| self.body.locals().get(local_idx))
            .and_then(|local_decl| self.get_type_size(local_decl.ty))
            .and_then(|size| u32::try_from(size).ok())
        {
            return Some(Expr::bitvec_const(size as i128, 32));
        }
        if let Some(size) = self.heap_state.heap_alloc_size(const_obj_id) {
            return Some(Expr::bitvec_const(size as i128, 32));
        }
        self.mark_heap_metadata_read();
        Some(self.current_obj_size_array().select(obj_id.clone()))
    }
}
