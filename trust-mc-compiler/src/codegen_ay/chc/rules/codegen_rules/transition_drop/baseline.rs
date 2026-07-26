// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::chc::heap_state::HeapTransientRuleState;

pub(super) fn restore_dyn_drop_d2_candidate_baseline(
    ctx: &mut ChcCtx<'_, '_>,
    baseline_modified: &HashSet<usize>,
    baseline_heap: &HeapTransientRuleState,
) {
    ctx.encode.modified_state_indices = baseline_modified.clone();
    ctx.heap_state.restore_transient_rule_state(baseline_heap);
}
