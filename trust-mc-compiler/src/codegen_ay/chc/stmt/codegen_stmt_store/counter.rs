// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Counter for silently dropped store transitions.
//!
//! Part of #2236: store operations were silently dropped when projections couldn't
//! be translated, leaving the CHC model without the memory mutation. Non-zero means
//! verification results may be unsound (stale reads possible).
//!
//! Counter storage consolidated into GLOBAL_COUNTERS (Part of #2906).

use std::sync::atomic::Ordering;

use super::super::codegen_ctx::diagnostics::GLOBAL_COUNTERS;

/// Get the current number of dropped store transitions.
pub(in crate::codegen_ay) fn get_chc_store_dropped_transition_count() -> usize {
    GLOBAL_COUNTERS.store_dropped_transition.load(Ordering::Relaxed)
}
