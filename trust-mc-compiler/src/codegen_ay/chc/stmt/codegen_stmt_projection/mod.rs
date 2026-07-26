// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Projection and field operations for CHC statement encoding.
//!
//! Extracted from codegen_stmt.rs per #2036.
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

mod bv_projection;
mod constructor_guards;
mod field_access;
mod field_select_coercion;
mod projection_path;

use std::sync::atomic::Ordering;

use super::codegen_ctx::diagnostics::GLOBAL_COUNTERS;
pub(in crate::codegen_ay) use constructor_guards::collect_constructor_guards;
pub(in crate::codegen_ay::chc) use projection_path::{
    FieldProjection, UnknownProjectionPolicy, collect_field_projections, constant_index_offset,
};

/// Returns and resets unsupported-projection drops for metadata emission.
/// Delegates to GLOBAL_COUNTERS (Part of #2906).
pub(in crate::codegen_ay) fn take_unsupported_field_projection_count() -> usize {
    GLOBAL_COUNTERS.unsupported_field_projection.swap(0, Ordering::Relaxed)
}

#[cfg(test)]
pub(in crate::codegen_ay) fn set_unsupported_field_projection_count_for_test(count: usize) {
    GLOBAL_COUNTERS.unsupported_field_projection.store(count, Ordering::Relaxed);
}
