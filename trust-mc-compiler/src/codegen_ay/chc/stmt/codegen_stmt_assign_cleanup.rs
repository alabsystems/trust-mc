// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cleanup helpers for assignment fallback paths.

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Clear destination-local side tables when an assignment falls back before
    /// producing an output-state update.
    pub(in crate::codegen_ay::chc) fn clear_untracked_assignment_metadata(
        &mut self,
        local_idx: usize,
    ) {
        self.encode.local_expr_env.remove(&local_idx);
        self.encode.local_signedness.remove(&local_idx);
        self.encode.flattened_field_env.retain(|&(field_local, _), _| field_local != local_idx);

        self.ref_resolution.ref_targets.remove(&local_idx);
        self.ref_resolution.call_forwarded_raw_ptrs.remove(&local_idx);
        self.ref_resolution.const_ref_values.remove(&local_idx);
        self.ref_resolution.subslice_len.remove(&local_idx);
        self.ref_resolution.subslice_offset.remove(&local_idx);
        self.ref_resolution.alloc_result_locals.remove(&local_idx);

        self.known_alloc_ids.remove(&local_idx);
        self.known_stack_addr_exprs.remove(&local_idx);
        self.clear_known_vtable_discriminant(local_idx);
    }
}
