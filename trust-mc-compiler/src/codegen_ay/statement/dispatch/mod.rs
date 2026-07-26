// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Call dispatch logic for statement codegen.
//!
//! This module handles:
//! - Standard library intrinsic dispatch (`try_codegen_std_intrinsic`)
//! - Stub registry dispatch (`try_codegen_stdlib_stub_call`)
//! - Closure call handling (`codegen_closure_call`)
//! - Callee path resolution (`resolve_callee_path`)
//! - Abstracted function fallback (`try_codegen_abstracted_fallback`)
//!
//! Extracted from codegen.rs per #1354 to improve reviewability.
//! Split into sub-modules per #2027 to replace the monolithic if-chain
//! with per-family grouped dispatch and reduce file size.

mod apply_closure;
mod array_cmp;
mod call_outcome;
mod closure_call;
mod fn_inline;
mod fn_ptr;
mod helpers;
mod inline_body;
mod intrinsic;
mod math_unary;
mod pow;
mod precheck;
mod ptr_arithmetic;
mod stub_dispatch;
mod stub_dispatch_memory;
mod stub_dispatch_option_result;
mod stub_dispatch_simple;
mod stub_dispatch_table;
mod virtual_dispatch;

use std::sync::atomic::{AtomicUsize, Ordering};

pub(in crate::codegen_ay::statement) use call_outcome::CallDispatchOutcome;
pub(in crate::codegen_ay::statement) use inline_body::InlineArgValue;

/// Telemetry counter for pre-inlined collection internal hits (#1662).
/// This tracks when rustc pre-inlines collection internals (BTree, RawVec, etc.) before trust_mc
/// can abstract them at reachability level. Each hit represents an unsound
/// workaround where we return a symbolic result instead of proper modeling.
/// Includes BTree, RawVec, and other collection internal workarounds.
pub(super) static INTERNAL_WORKAROUND_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Reset the internal workaround counter, returning the previous value (Part of #2360).
pub(in crate::codegen_ay) fn take_internal_workaround_count() -> usize {
    INTERNAL_WORKAROUND_COUNT.swap(0, Ordering::Relaxed)
}

/// Non-destructive read of the internal workaround counter (Part of #3080).
pub(in crate::codegen_ay) fn get_internal_workaround_count() -> usize {
    INTERNAL_WORKAROUND_COUNT.load(Ordering::Relaxed)
}

/// Set internal workaround counter for test isolation (Part of #3369).
#[cfg(test)]
#[allow(dead_code)]
pub(in crate::codegen_ay) fn set_internal_workaround_count_for_test(count: usize) {
    INTERNAL_WORKAROUND_COUNT.store(count, Ordering::Relaxed);
}

/// Telemetry counter for abstracted fallback hits (Part of #1691).
/// This tracks when pre-inlined UTF8/Cow/String internals are caught by
/// the codegen-level fallback. Each hit represents a symbolic approximation
/// of stdlib code that wasn't intercepted at reachability level.
pub(super) static ABSTRACTED_FALLBACK_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Reset the abstracted fallback counter, returning the previous value (Part of #2360).
pub(in crate::codegen_ay) fn take_abstracted_fallback_count() -> usize {
    ABSTRACTED_FALLBACK_COUNT.swap(0, Ordering::Relaxed)
}

/// Non-destructive read of the abstracted fallback counter (Part of #3080).
pub(in crate::codegen_ay) fn get_abstracted_fallback_count() -> usize {
    ABSTRACTED_FALLBACK_COUNT.load(Ordering::Relaxed)
}

/// Set abstracted fallback counter for test isolation (Part of #3369).
#[cfg(test)]
#[allow(dead_code)]
pub(in crate::codegen_ay) fn set_abstracted_fallback_count_for_test(count: usize) {
    ABSTRACTED_FALLBACK_COUNT.store(count, Ordering::Relaxed);
}
