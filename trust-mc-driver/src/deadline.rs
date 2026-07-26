// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-harness wall-clock deadline.
//!
//! `--harness-timeout` was historically honored only at individual AY
//! solver call boundaries. Retries, secondary cover-check queries, and
//! in-process solving could each independently consume a full timeout, so
//! one harness could occupy the whole driver budget in a multi-harness
//! run — and paths with hardwired constants (`run_ay_direct`'s 600s, the
//! 600s compiler/tool default) ignored the harness budget entirely.
//!
//! A [`Deadline`] is created once per harness in
//! `KaniSession::check_harness` and threaded through `run_ay` into every
//! solver path (external `ay` subprocess, native CHC portfolio, direct
//! linking). Each path computes its budget as
//! `min(tool_timeout, deadline.remaining())` via [`Deadline::clamp`], so
//! the sum of all attempts for one harness can never exceed the per-harness
//! wall budget (the same `5x + grace` retry-ladder formula used by the
//! process-wide watchdog — see [`crate::wall_clock_watchdog::budget_for`]).
//!
//! The process-wide complement lives in `session::process`, where every
//! subprocess timeout is additionally clamped to
//! `wall_clock_watchdog::remaining()`.

use std::time::{Duration, Instant};

use crate::args::Timeout;

/// Cap budgets so `Instant + budget` can never overflow/panic.
/// Ten years is far beyond any meaningful verification budget.
const MAX_BUDGET: Duration = Duration::from_secs(10 * 365 * 24 * 3600);

/// Headroom kept between a per-harness deadline and the process watchdog's
/// fire time: enough for the harness to bail to an honest bounded UNKNOWN
/// and flush its markers/summary through the normal result pipeline before
/// the watchdog hard-exits the process.
const WATCHDOG_HEADROOM: Duration = Duration::from_secs(10);

/// An `Instant`-based wall-clock deadline for a single harness.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Deadline {
    end: Instant,
}

impl Deadline {
    /// A deadline `budget` from now.
    pub(crate) fn after(budget: Duration) -> Self {
        Self { end: Instant::now() + budget.min(MAX_BUDGET) }
    }

    /// The per-harness deadline for a harness with the given
    /// `--harness-timeout`: the per-call solver budget (default 120s when
    /// no harness timeout is set — see `call_ay::solver_timeout_duration`)
    /// times the retry-ladder multiplier, plus grace.
    ///
    /// Additionally clamped to strictly inside the process watchdog's
    /// remaining budget (minus [`WATCHDOG_HEADROOM`]): the
    /// watchdog is armed at process start while this deadline starts after
    /// compilation, so without the clamp the watchdog always fires FIRST on
    /// a hung harness — a hard `_exit` with raw markers instead of an honest
    /// per-harness UNKNOWN through the result pipeline (the DriverTimeout
    /// wall-kill class). Fail-closed: this only ever SHRINKS a budget, which
    /// can convert results into honest bounded UNKNOWNs, never mint a proof.
    pub(crate) fn for_harness(harness_timeout: Option<Timeout>) -> Self {
        let per_call = crate::call_ay::solver_timeout_duration(harness_timeout);
        let mut budget = crate::wall_clock_watchdog::budget_for(per_call);
        if let Some(watchdog_remaining) = crate::wall_clock_watchdog::remaining() {
            budget = budget.min(watchdog_remaining.saturating_sub(WATCHDOG_HEADROOM));
        }
        Self::after(budget)
    }

    /// Time left before the deadline (zero once expired; never negative).
    pub(crate) fn remaining(&self) -> Duration {
        self.end.saturating_duration_since(Instant::now())
    }

    /// True once no budget remains.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn is_expired(&self) -> bool {
        self.remaining().is_zero()
    }

    /// Effective budget for one tool/solver invocation:
    /// `min(tool_timeout, remaining)`.
    ///
    /// Returns `Duration::ZERO` when the deadline has expired — callers
    /// pass this straight to the timeout machinery, which then fails the
    /// invocation immediately (fail-closed: an exhausted harness budget
    /// yields a timeout-shaped UNKNOWN, never an unbounded wait).
    pub(crate) fn clamp(&self, tool_timeout: Duration) -> Duration {
        tool_timeout.min(self.remaining())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn remaining_decreases_and_clamp_takes_min() {
        let d = Deadline::after(Duration::from_secs(3600));
        let r = d.remaining();
        assert!(r <= Duration::from_secs(3600));
        assert!(r > Duration::from_secs(3590), "fresh deadline should be ~1h, got {r:?}");
        assert!(!d.is_expired());

        // Tool timeout smaller than remaining: tool timeout wins.
        assert_eq!(d.clamp(Duration::from_secs(10)), Duration::from_secs(10));
        // Tool timeout larger than remaining: remaining wins.
        assert!(d.clamp(Duration::from_secs(7200)) <= Duration::from_secs(3600));
    }

    #[test]
    fn zero_budget_is_immediately_expired() {
        let d = Deadline::after(Duration::ZERO);
        assert!(d.is_expired());
        assert_eq!(d.remaining(), Duration::ZERO);
        assert_eq!(d.clamp(Duration::from_secs(600)), Duration::ZERO);
    }

    #[test]
    fn expired_deadline_clamps_everything_to_zero() {
        let d = Deadline { end: Instant::now() - Duration::from_secs(5) };
        assert!(d.is_expired());
        assert_eq!(d.clamp(Duration::from_secs(600)), Duration::ZERO);
        assert_eq!(d.remaining(), Duration::ZERO);
    }

    #[test]
    fn huge_budget_does_not_panic() {
        let d = Deadline::after(Duration::from_secs(u64::MAX));
        assert!(!d.is_expired());
        // Clamp still behaves: a small tool timeout passes through.
        assert_eq!(d.clamp(Duration::from_secs(1)), Duration::from_secs(1));
    }

    #[test]
    fn for_harness_uses_retry_ladder_budget() {
        // No harness timeout → 120s default per-call budget → 5*120+5 = 605s
        // (default watchdog mult/grace; CI does not set the env overrides).
        let d = Deadline::for_harness(None);
        let r = d.remaining();
        assert!(r <= Duration::from_secs(605), "expected <= 605s, got {r:?}");
        assert!(r > Duration::from_secs(600), "expected ~605s, got {r:?}");
    }
}
