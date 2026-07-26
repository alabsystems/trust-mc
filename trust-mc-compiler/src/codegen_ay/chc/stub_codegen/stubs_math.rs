// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC stub dispatch for BigInt/BigRational math operations.
//!
//! Converted from include!() to proper module per #2595.
//! Counter storage consolidated into GLOBAL_COUNTERS (Part of #2906).

use std::sync::atomic::Ordering;

use super::codegen_ctx::diagnostics::GLOBAL_COUNTERS;

/// Get the current CHC BigInt unsoundness skip count (#1989).
/// Delegates to GLOBAL_COUNTERS (Part of #2906).
pub(in crate::codegen_ay) fn get_chc_bigint_unsound_skip_count() -> usize {
    GLOBAL_COUNTERS.bigint_unsound_skip.load(Ordering::Relaxed)
}
