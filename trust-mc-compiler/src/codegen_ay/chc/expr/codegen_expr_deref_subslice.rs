// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Subslice expression building for MIR Subslice projections.
//!
//! `build_subslice_expr` constructs a new AY array expression from a contiguous
//! sub-range of a source array: `result[i] = source[start + i]` for
//! `i` in `0..result_len`.
//!
//! Shared by multiple deref/projection paths:
//! - `codegen_expr_deref.rs` (deref chain Subslice arm)
//! - `codegen_expr_deref_projection.rs` (projection chain Subslice arm)
//! - `codegen_expr_deref_field.rs` (ref-target field resolution)
//! - `codegen_expr_deref_static.rs` (static-ref resolution)
//! - `codegen_expr.rs` (non-deref place translation)
//!
//! Extracted from `codegen_expr_deref.rs` per #4125 (500 LOC threshold).

use ay_bindings::{Expr, Sort};

use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;
use super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::codegen_types::CodegenTypes;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Build a subslice array expression via select chain.
    ///
    /// Given a source array and Subslice parameters, constructs a new AY array where
    /// `result[i] = source[start + i]` for `i` in `0..result_len`.
    ///
    /// Part of #3306: Shared helper for deref chain and arg-ref paths.
    pub(in crate::codegen_ay::chc) fn build_subslice_expr(
        &self,
        source: &Expr,
        source_ty: rustc_public::ty::Ty,
        from: u64,
        to: u64,
        from_end: bool,
    ) -> Option<Expr> {
        if !source.sort().is_array() {
            return None;
        }
        // Identity only for `from_end=true`: `[0..len-0]`. With
        // `from_end=false`, `[0..0]` is EMPTY and returning the source would
        // grant access to cells that are not in the subslice.
        if from == 0 && to == 0 && from_end {
            return Some(source.clone());
        }
        let array_len = self.get_array_length(source_ty)?;
        let end = if from_end { array_len.checked_sub(to as usize)? } else { to as usize };
        let start = from as usize;
        if end <= start || end > array_len {
            return None;
        }
        let result_len = end - start;
        let elem_ty = self.get_array_element_ty(source_ty)?;
        let elem_sort = Self::translate_ty(elem_ty)?;
        let result_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort);
        // Part of #3447: base array unconstrained beyond copied range.
        self.record_aggregate_gap("deref_subslice_unconstrained");
        let name = chc_fresh_name("__subslice_arr");
        let mut result = declare_pending_var(name, result_sort);
        for i in 0..result_len {
            let src_idx = Expr::bitvec_const((start + i) as u128, POINTER_WIDTH);
            let dst_idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            let elem = source.clone().select(src_idx);
            // Part of #4212: coerce source element to match result array sort.
            let elem = Self::coerce_store_value(result.sort(), elem, false, &self.diagnostics);
            result = result.store(dst_idx, elem);
        }
        Some(result)
    }
}
