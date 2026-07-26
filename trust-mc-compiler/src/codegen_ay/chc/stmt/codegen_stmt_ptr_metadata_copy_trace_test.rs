// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test-only wrappers for ptr_metadata copy-trace helpers.
//!
//! Separated from codegen_stmt_ptr_metadata_copy_trace.rs to keep the main
//! file under 500 lines. Part of #4127.

use std::collections::HashSet;

use ay_bindings::Expr;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Test-only: trace subslice_len through Copy/Move chains.
    pub(in crate::codegen_ay::chc) fn test_trace_subslice_len_through_copies(
        &self,
        start_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        self.trace_subslice_len_through_copies(start_local, modified_locals)
    }

    /// Test-only: trace a local through Ref/AddressOf/Use to find the referent.
    pub(in crate::codegen_ay::chc) fn test_trace_local_to_referent(
        &self,
        local: usize,
    ) -> Option<usize> {
        self.trace_local_to_referent(local)
    }

    /// Test-only: find element locals from an Aggregate(Array, ...) assignment.
    pub(in crate::codegen_ay::chc) fn test_find_array_aggregate_elements(
        &self,
        array_local: usize,
    ) -> Vec<usize> {
        self.find_array_aggregate_elements(array_local)
    }
}
