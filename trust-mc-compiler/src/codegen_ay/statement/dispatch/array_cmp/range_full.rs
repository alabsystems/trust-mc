// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! RangeFull identity handling for array/slice comparison dispatch.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};

use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Handle `Index::index(slice, RangeFull)` as identity.
    pub(super) fn try_codegen_range_full_index(
        &mut self,
        source: &Operand,
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let value = self.get_value_through_ref(source).or_else(|| self.codegen_operand(source))?;
        let dest_base = self.ssa_base_name(destination);
        // A full view is a VIEW: record it so `bmc_subslice_consumer_fail_closed`
        // sees it reach a model that reads the source array (defect M5/D6).
        self.shifted_subslice_views.insert(std::sync::Arc::from(dest_base.as_str()));
        self.env_update(dest_base, value);
        target
    }
}
