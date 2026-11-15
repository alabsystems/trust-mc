// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Diagnostics tracking for stub coverage validation.
//!
//! Phase 2 of stub coverage validation (Part of #1685):
//! - Track unstubbed abstractions per session
//! - Provide summary at end of compilation
//! - Track call frequency for prioritization
//!
//! See `designs/archive/2026-02-01-stub-coverage-validation.md` for design.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard, OnceLock};
use tracing::{info, warn};

/// Global diagnostics state for the current compilation session.
static DIAGNOSTICS: OnceLock<Mutex<StubDiagnostics>> = OnceLock::new();

/// Monotonic count of unresolved unstubbed-abstraction encounters (D1).
///
/// Deliberately SEPARATE from [`StubDiagnostics::unstubbed_abstractions`], which
/// `reset_stub_diagnostics` clears between compilation sessions and which keys
/// by path: the per-harness accumulator reads this counter as a monotone delta
/// across one harness's `codegen_items` call. Pending reachability events are
/// finalized at that boundary after exact callsite reconciliation; aborted
/// scopes finalize all events. Early coverage remains in `StubDiagnostics`.
/// (`unsoundness_per_harness::snapshot_counters`), so it must not be reset
/// mid-compilation, and it counts events, not distinct paths.
static UNSTUBBED_ABSTRACTION_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Non-destructive read of the unstubbed-abstraction counter.
pub(in crate::codegen_ay) fn get_unstubbed_abstraction_count() -> usize {
    UNSTUBBED_ABSTRACTION_COUNT.load(Ordering::Relaxed)
}

/// Drain the unstubbed-abstraction counter (crate-total collection).
pub(in crate::codegen_ay) fn take_unstubbed_abstraction_count() -> usize {
    UNSTUBBED_ABSTRACTION_COUNT.swap(0, Ordering::Relaxed)
}

/// Tracking state for stub coverage diagnostics.
#[derive(Debug, Default)]
struct StubDiagnostics {
    /// Functions that were abstracted without a stub, mapped to call count.
    /// Key: function path, Value: number of times encountered
    unstubbed_abstractions: HashMap<String, usize>,
    /// Whether summary has been printed for this session.
    summary_printed: bool,
}

impl StubDiagnostics {
    /// Create a new diagnostics tracker.
    ///
    /// REQUIRES: (no preconditions)
    /// ENSURES: Returned tracker has empty unstubbed_abstractions map.
    /// ENSURES: Returned tracker has summary_printed == false.
    fn new() -> Self {
        Self::default()
    }

    /// Record an unstubbed abstraction.
    ///
    /// Call this when reachability abstracts a standard-library function
    /// (`kani_middle::std_abstraction`) for which no stub exists in the registry.
    ///
    /// REQUIRES: `path` is a non-empty function path string.
    /// ENSURES: Entry for `path` exists in unstubbed_abstractions.
    /// ENSURES: Call count for `path` is incremented by 1.
    fn record_unstubbed(&mut self, path: &str) {
        // Fast path: avoid allocating a new String when the key already exists.
        if let Some(count) = self.unstubbed_abstractions.get_mut(path) {
            *count += 1;
        } else {
            self.unstubbed_abstractions.insert(path.to_owned(), 1);
        }
    }

    /// Get the number of unique unstubbed abstractions.
    ///
    /// REQUIRES: (no preconditions)
    /// ENSURES: Returns the number of distinct function paths recorded.
    fn unstubbed_count(&self) -> usize {
        self.unstubbed_abstractions.len()
    }

    /// Get the total number of unstubbed abstraction calls.
    ///
    /// REQUIRES: (no preconditions)
    /// ENSURES: Returns sum of all call counts across all recorded paths.
    fn unstubbed_call_count(&self) -> usize {
        self.unstubbed_abstractions.values().sum()
    }

    /// Get unstubbed abstractions sorted by call frequency (most frequent first).
    ///
    /// REQUIRES: (no preconditions)
    /// ENSURES: Returned Vec is sorted in descending order by call count.
    /// ENSURES: All entries from unstubbed_abstractions are included.
    fn unstubbed_by_frequency(&self) -> Vec<(&str, usize)> {
        let mut entries: Vec<_> =
            self.unstubbed_abstractions.iter().map(|(k, v)| (k.as_str(), *v)).collect();
        entries.sort_by(|a, b| b.1.cmp(&a.1));
        entries
    }

    /// Print summary of unstubbed abstractions.
    ///
    /// Should be called at end of compilation to provide visibility into
    /// methods that were abstracted without explicit stubs.
    ///
    /// REQUIRES: (no preconditions)
    /// ENSURES: If called twice, second call is no-op (idempotent).
    /// ENSURES: After return, summary_printed == true.
    fn print_summary(&mut self) {
        if self.summary_printed {
            return;
        }
        self.summary_printed = true;

        let count = self.unstubbed_count();
        if count == 0 {
            return;
        }

        let call_count = self.unstubbed_call_count();
        info!("Stub coverage: {} methods abstracted without stubs ({} calls)", count, call_count);

        // Show top 5 most frequently called unstubbed methods
        let top_entries = self.unstubbed_by_frequency();
        let mut top_iter = top_entries.iter().take(5).peekable();
        if top_iter.peek().is_some() {
            info!("Top unstubbed methods by call frequency:");
            for (path, freq) in top_iter {
                info!("  {} ({} calls)", path, freq);
            }
        }
    }
}

/// Get the global diagnostics tracker.
///
/// REQUIRES: (no preconditions, thread-safe initialization via OnceLock)
/// ENSURES: Returns reference to the same Mutex on every call.
/// ENSURES: If first call, initializes with empty StubDiagnostics.
fn get_diagnostics() -> &'static Mutex<StubDiagnostics> {
    DIAGNOSTICS.get_or_init(|| Mutex::new(StubDiagnostics::new()))
}

fn lock_diagnostics(diagnostics: &Mutex<StubDiagnostics>) -> MutexGuard<'_, StubDiagnostics> {
    match diagnostics.lock() {
        Ok(guard) => guard,
        Err(poisoned) => {
            warn!("diagnostics lock poisoned; continuing with inner state");
            poisoned.into_inner()
        }
    }
}

/// Record an unstubbed abstraction in the global tracker.
///
/// Reachability (`Boundary::abstracts` in reachability.rs) calls this when a
/// standard-library function is abstracted but has no corresponding stub.
///
/// REQUIRES: `path` is a non-empty function path string.
/// ENSURES: Global diagnostics tracker has entry for `path`.
/// ENSURES: Call count for `path` is incremented by 1.
pub(crate) fn record_unstubbed_abstraction(path: &str) {
    add_unstubbed_semantic_events(1);
    record_unstubbed_coverage(path);
}

/// Early reachability coverage is preserved even if later exact modeling succeeds.
pub(super) fn record_unstubbed_coverage(path: &str) {
    lock_diagnostics(get_diagnostics()).record_unstubbed(path);
}

/// Only append finalized unresolved events; never decrement a monotone counter.
pub(super) fn add_unstubbed_semantic_events(count: usize) {
    UNSTUBBED_ABSTRACTION_COUNT.fetch_add(count, Ordering::Relaxed);
}

/// Reset the global diagnostics state for a new compilation session.
///
/// Clears accumulated unstubbed abstraction data and resets the summary
/// flag so diagnostics can be collected fresh. Prevents unbounded memory
/// growth across harnesses within a compilation. Part of #3075.
pub(in crate::codegen_ay) fn reset_stub_diagnostics() {
    let diagnostics = get_diagnostics();
    let mut diag = lock_diagnostics(diagnostics);
    diag.unstubbed_abstractions.clear();
    diag.summary_printed = false;
}

/// Print the compilation summary for stub coverage.
///
/// Should be called at the end of compilation to show coverage statistics.
///
/// REQUIRES: (no preconditions)
/// ENSURES: Summary printed at most once per process (idempotent).
pub(in crate::codegen_ay) fn print_stub_coverage_summary() {
    let diagnostics = get_diagnostics();
    let mut diag = lock_diagnostics(diagnostics);
    diag.print_summary();
}

#[cfg(test)]
mod tests {
    use super::*;

    /// D1 (2026-09-14): `record_unstubbed_abstraction` must move the monotone
    /// counter the per-harness accumulator reads, not only the path map.
    ///
    /// Asserted as a DELTA, not an absolute: the counter is process-global and
    /// deliberately never reset (see its docs), and the engine's test binary
    /// runs tests in parallel, so any absolute expectation is a flake.
    #[test]
    fn test_record_unstubbed_abstraction_increments_the_monotone_counter() {
        let before = get_unstubbed_abstraction_count();
        record_unstubbed_abstraction("std::sync::MutexGuard::<T>::deref");
        record_unstubbed_abstraction("std::sync::MutexGuard::<T>::deref");
        assert!(
            get_unstubbed_abstraction_count() >= before + 2,
            "every encounter counts, including repeats of one path: the warning is \
             deduplicated, the unsoundness event is not"
        );
    }

    #[test]
    fn test_diagnostics_new() {
        let diag = StubDiagnostics::new();
        assert_eq!(diag.unstubbed_count(), 0);
        assert_eq!(diag.unstubbed_call_count(), 0);
    }

    #[test]
    fn test_record_unstubbed() {
        let mut diag = StubDiagnostics::new();
        diag.record_unstubbed("std::collections::BTreeSet::iter");
        diag.record_unstubbed("std::collections::BTreeSet::iter");
        diag.record_unstubbed("std::collections::BTreeMap::values");

        assert_eq!(diag.unstubbed_count(), 2);
        assert_eq!(diag.unstubbed_call_count(), 3);
    }

    #[test]
    fn test_unstubbed_by_frequency() {
        let mut diag = StubDiagnostics::new();
        diag.record_unstubbed("low_freq");
        diag.record_unstubbed("high_freq");
        diag.record_unstubbed("high_freq");
        diag.record_unstubbed("high_freq");
        diag.record_unstubbed("med_freq");
        diag.record_unstubbed("med_freq");

        let sorted = diag.unstubbed_by_frequency();
        assert_eq!(sorted[0].0, "high_freq");
        assert_eq!(sorted[0].1, 3);
        assert_eq!(sorted[1].0, "med_freq");
        assert_eq!(sorted[1].1, 2);
        assert_eq!(sorted[2].0, "low_freq");
        assert_eq!(sorted[2].1, 1);
    }

    #[test]
    #[allow(clippy::panic)]
    fn test_lock_diagnostics_recovers_from_poison() {
        let diagnostics = Mutex::new(StubDiagnostics::new());
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _guard = diagnostics.lock().expect("lock acquired");
            panic!("poison diagnostics lock");
        }));

        let mut recovered = lock_diagnostics(&diagnostics);
        recovered.record_unstubbed("poison_recovery");
        assert_eq!(recovered.unstubbed_call_count(), 1);
    }
}

#[cfg(test)]
pub(super) fn coverage_count_for_test(path: &str) -> usize {
    lock_diagnostics(get_diagnostics()).unstubbed_abstractions.get(path).copied().unwrap_or(0)
}
