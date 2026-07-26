// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Synthetic memory-bridge helpers for statement codegen.
//!
//! These writes synchronize CHC's abstract typed memory with register-state
//! assignments and reference creation. They are not real program dereferences,
//! so they must not emit heap-access safety errors for packed-field offsets.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Place, Rvalue};

use super::ChcCtx;
use crate::codegen_ay::chc::call::codegen_call_result_mem::try_decompose_flattened_enum_field_stores;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Mirror a local assignment into abstract memory without emitting heap
    /// safety checks for the synthetic store itself.
    ///
    /// Part of #3930: packed locals legitimately mirror fields at unaligned
    /// offsets (for example `char` at `base + 1`). These bridge stores are an
    /// internal model synchronization step, not a real dereference in user code.
    pub(in crate::codegen_ay::chc) fn mirror_local_assignment_to_memory(
        &mut self,
        lhs_local: usize,
        rhs: &Rvalue,
        local_ty: rustc_public::ty::Ty,
        coerced_rhs: &Expr,
        modified_locals: &HashSet<usize>,
        constraints: &mut Vec<Expr>,
    ) {
        let local_place = Place { local: lhs_local, projection: vec![] };
        let Some(addr_expr) = self.translate_ref_to_address(&local_place, modified_locals) else {
            return;
        };
        let prev_suppress = self.suppress_heap_store_checks;
        self.suppress_heap_store_checks = true;
        if let Some(store_constraint) =
            self.build_memory_store(addr_expr.clone(), coerced_rhs.clone(), local_ty)
        {
            constraints.push(store_constraint);
        }
        self.mirror_aggregate_field_stores_to_memory(
            rhs,
            local_ty,
            modified_locals,
            addr_expr.clone(),
            constraints,
        );
        self.mirror_array_elements_to_flat_memory(coerced_rhs, local_ty, &addr_expr, constraints);
        // Part of #3963: For Move/Copy of flattened enum locals (e.g.,
        // `_2 = Move(_1)` where _1 is CAS Result), mirror_aggregate_field_stores
        // bails because the RHS is not Rvalue::Aggregate. Decompose flattened
        // enum fields to typed memory so subsequent reference-based reads
        // (PartialEq::eq) see constrained values.
        try_decompose_flattened_enum_field_stores(
            self,
            lhs_local,
            &addr_expr,
            local_ty,
            modified_locals,
            constraints,
        );
        self.suppress_heap_store_checks = prev_suppress;
    }

    /// Mirror the value behind a newly-created reference into typed memory
    /// without treating the bridge store as a checked heap write.
    ///
    /// Part of #3930: `Ref`/`AddressOf` bridge stores for packed locals must not
    /// emit unaligned-store error rules for synthetic field mirrors.
    pub(in crate::codegen_ay::chc) fn mirror_ref_value_to_memory(
        &mut self,
        addr_expr: &Expr,
        value_expr: &Expr,
        value_ty: rustc_public::ty::Ty,
        ref_local_idx: usize,
        modified_locals: &HashSet<usize>,
        constraints: &mut Vec<Expr>,
    ) {
        let prev_suppress = self.suppress_heap_store_checks;
        self.suppress_heap_store_checks = true;
        if let Some(store_constraint) =
            self.build_memory_store(addr_expr.clone(), value_expr.clone(), value_ty)
        {
            constraints.push(store_constraint);
        }
        if value_expr.sort().is_datatype() {
            self.try_decompose_struct_store(addr_expr, value_expr, value_ty, constraints);
        }
        // Part of #3963: Always try flattened enum decomposition for
        // multi-constructor enum locals (Result, Option), regardless of
        // value_expr sort. Same fix as codegen_call_result_mem.rs — when
        // aggregate reconstruction returns BV (not Datatype), the is_datatype()
        // gate above skips struct decomposition, leaving typed memory fields
        // unconstrained for PartialEq reads.
        try_decompose_flattened_enum_field_stores(
            self,
            ref_local_idx,
            addr_expr,
            value_ty,
            modified_locals,
            constraints,
        );
        self.suppress_heap_store_checks = prev_suppress;
    }
}
