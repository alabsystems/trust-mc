// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for mirrored diagnostic counters (MirroredUsizeCounter, MirroredU64Counter)
//! and the CellCounter trait.
//!
//! W2:3133 introduced the mirrored-counter pattern (local Cell + global Atomic)
//! with zero test coverage. These tests verify the dual-write invariant:
//! every `.inc()` / `.inc_get()` must update both the per-context local Cell
//! and the process-global AtomicUsize/AtomicU64.
//!
//! Part of #2949: regression gate for counter infrastructure.

use std::cell::Cell;
use std::sync::atomic::Ordering;

use crate::codegen_ay::chc::codegen_ctx::ChcDiagnostics;
use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;

use super::super::GLOBAL_COUNTERS;

/// MirroredUsizeCounter.inc() updates both local Cell and global AtomicUsize.
///
/// Uses ChcDiagnostics::default() to construct via the real production path,
/// then tests place_translation_drop as the representative MirroredUsizeCounter.
/// Snapshot-delta pattern avoids cross-test interference on GLOBAL_COUNTERS.
#[test]
fn test_mirrored_usize_counter_inc_updates_both_local_and_global() {
    let global_before = GLOBAL_COUNTERS.place_translation_drop.load(Ordering::Relaxed);
    let diag = ChcDiagnostics::default();

    assert_eq!(diag.place_translation_drop.get(), 0);

    diag.place_translation_drop.inc();
    assert_eq!(diag.place_translation_drop.get(), 1, "local must increment");
    assert_eq!(
        GLOBAL_COUNTERS.place_translation_drop.load(Ordering::Relaxed),
        global_before + 1,
        "global must increment"
    );

    diag.place_translation_drop.inc();
    assert_eq!(diag.place_translation_drop.get(), 2);
    assert_eq!(GLOBAL_COUNTERS.place_translation_drop.load(Ordering::Relaxed), global_before + 2,);
}

/// MirroredUsizeCounter.inc_get() returns the new local value and mirrors globally.
#[test]
fn test_mirrored_usize_counter_inc_get_returns_new_value() {
    let global_before = GLOBAL_COUNTERS.unhandled_call.load(Ordering::Relaxed);
    let diag = ChcDiagnostics::default();

    let v1 = diag.unhandled_call.inc_get();
    assert_eq!(v1, 1, "inc_get must return 1 after first increment");
    assert_eq!(diag.unhandled_call.get(), 1);
    assert_eq!(GLOBAL_COUNTERS.unhandled_call.load(Ordering::Relaxed), global_before + 1,);

    let v2 = diag.unhandled_call.inc_get();
    assert_eq!(v2, 2, "inc_get must return 2 after second increment");
    assert_eq!(GLOBAL_COUNTERS.unhandled_call.load(Ordering::Relaxed), global_before + 2,);
}

/// MirroredU64Counter.inc() updates both local Cell<usize> and global AtomicU64.
///
/// Uses range_spec_next_datatype_path as the representative MirroredU64Counter.
#[test]
fn test_mirrored_u64_counter_inc_updates_both_local_and_global() {
    let global_before = GLOBAL_COUNTERS.range_spec_next_datatype_path.load(Ordering::Relaxed);
    let diag = ChcDiagnostics::default();

    assert_eq!(diag.range_spec_next_datatype_path.inc_get(), 1);
    assert_eq!(
        GLOBAL_COUNTERS.range_spec_next_datatype_path.load(Ordering::Relaxed),
        global_before + 1,
        "global AtomicU64 must increment"
    );

    diag.range_spec_next_datatype_path.inc();
    assert_eq!(
        GLOBAL_COUNTERS.range_spec_next_datatype_path.load(Ordering::Relaxed),
        global_before + 2,
    );
}

/// GLOBAL_COUNTERS.reset_all() zeroes all AtomicUsize and AtomicU64 counters.
///
/// Exercises the session-reset path used by process-reuse (Part of #2906).
/// Uses large sentinel values so concurrent test increments (+1, +2) cannot
/// produce false passes or false failures. If reset_all works, the post-reset
/// value will be far below the sentinel; if it doesn't, it will be above.
/// Part of #3075: fix shared-state test race condition.
#[test]
fn test_global_counters_reset_all_clears_atomics() {
    // Use large sentinel values that concurrent tests cannot reach via small increments.
    let sentinel: usize = 1_000_000;
    let sentinel_u64: u64 = 1_000_000;

    let prev_signedness =
        crate::codegen_ay::shared::replace_signedness_fallback_count_for_test(sentinel);
    GLOBAL_COUNTERS.place_translation_drop.fetch_add(sentinel, Ordering::Relaxed);
    GLOBAL_COUNTERS.unhandled_call.fetch_add(sentinel, Ordering::Relaxed);
    GLOBAL_COUNTERS.range_spec_next_datatype_path.fetch_add(sentinel_u64, Ordering::Relaxed);

    GLOBAL_COUNTERS.reset_all();

    // After reset, counters should be near zero. Concurrent tests may have added
    // small values (1-10) between reset and this check, so allow a margin.
    let max_concurrent_noise: usize = 100;
    let max_concurrent_noise_u64: u64 = 100;

    assert!(
        GLOBAL_COUNTERS.place_translation_drop.load(Ordering::Relaxed) < max_concurrent_noise,
        "reset_all must zero AtomicUsize counters (got {}, expected < {})",
        GLOBAL_COUNTERS.place_translation_drop.load(Ordering::Relaxed),
        max_concurrent_noise,
    );
    assert!(
        GLOBAL_COUNTERS.unhandled_call.load(Ordering::Relaxed) < max_concurrent_noise,
        "reset_all must zero AtomicUsize counters (got {}, expected < {})",
        GLOBAL_COUNTERS.unhandled_call.load(Ordering::Relaxed),
        max_concurrent_noise,
    );
    assert!(
        GLOBAL_COUNTERS.range_spec_next_datatype_path.load(Ordering::Relaxed)
            < max_concurrent_noise_u64,
        "reset_all must zero AtomicU64 counters (got {}, expected < {})",
        GLOBAL_COUNTERS.range_spec_next_datatype_path.load(Ordering::Relaxed),
        max_concurrent_noise_u64,
    );
    assert!(
        crate::codegen_ay::shared::get_signedness_fallback_count() < max_concurrent_noise,
        "reset_all must zero the shared signedness fallback counter (got {}, expected < {})",
        crate::codegen_ay::shared::get_signedness_fallback_count(),
        max_concurrent_noise,
    );

    crate::codegen_ay::shared::replace_signedness_fallback_count_for_test(prev_signedness);
}

/// CellCounter trait impl on plain Cell<usize> increments correctly.
///
/// This is the base case — Cell<usize> counters (type_sort_fallback,
/// signedness_fallback, diverging_call_drop) use the trait without mirroring.
#[test]
fn test_cell_counter_trait_on_plain_cell() {
    let cell = Cell::new(0usize);
    cell.inc();
    assert_eq!(cell.get(), 1);
    let v = cell.inc_get();
    assert_eq!(v, 2);
    assert_eq!(cell.get(), 2);
}
