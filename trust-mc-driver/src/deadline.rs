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
//! Post-solve stages (the acyclic-BMC shortcut, the portfolio, the BMC
//! cross-check, the external-ay fallback, the BMC-lane probes, the two-lane
//! loop-contract retry) budget themselves through [`Deadline::stage_budget`]
//! instead: `min(cap, remaining)`, or `None` — the stage skips itself and
//! says so with a typed marker — when less than
//! [`MIN_USEFUL_STAGE_BUDGET`] is left. Before that discipline each stage
//! took its own full budget after the deadline, so an undecided harness
//! cost 2-6x the per-call timeout and ended at the watchdog's hard exit
//! instead of a typed UNKNOWN.
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

/// The least budget a solver stage can do anything useful with. Below it a
/// stage is skipped outright rather than started and killed: a spawn, a
/// parse and a first SMT call already cost this much, so a sub-second run
/// could only ever return "unknown" after wasting the time — and, run
/// after the deadline, push the harness into the watchdog.
pub(crate) const MIN_USEFUL_STAGE_BUDGET: Duration = Duration::from_secs(1);

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
    /// remaining budget (minus [`WATCHDOG_HEADROOM`]): the watchdog is
    /// restarted when codegen completes (`wall_clock_watchdog::
    /// rearm_after_codegen`) and every harness of the file shares it, so
    /// without the clamp the watchdog always fires FIRST on a hung
    /// later harness — a hard `_exit` with raw markers instead of an honest
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

    /// The instant the deadline falls due.
    #[cfg_attr(not(feature = "ay-chc-native"), allow(dead_code))]
    pub(crate) fn instant(&self) -> Instant {
        self.end
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

    /// Budget for one post-solve stage: `min(cap, remaining)`, or `None`
    /// when less than `min_useful` is left — the stage must then skip
    /// itself (with a typed marker) instead of starting work it cannot
    /// finish. Never returns a budget below `min_useful`, and never one
    /// past the deadline.
    pub(crate) fn stage_budget(&self, cap: Duration, min_useful: Duration) -> Option<Duration> {
        let budget = self.clamp(cap);
        if budget < min_useful { None } else { Some(budget) }
    }

    /// The marker line a stage prints when [`Self::stage_budget`] returned
    /// `None`:
    ///
    /// ```text
    /// [AY:STAGE_SKIPPED:<stage>:BudgetExhausted] <left>s of the per-harness deadline left, <needed>s needed
    /// ```
    ///
    /// One format for every stage, so a corpus run can grep the family and
    /// read which stage was forfeited on which harness. The stage may append
    /// what the skip means for the verdict.
    pub(crate) fn stage_skipped_marker(&self, stage: &str, needed: Duration) -> String {
        format!(
            "[AY:STAGE_SKIPPED:{stage}:BudgetExhausted] {:.1}s of the per-harness deadline \
             left, {:.0}s needed",
            self.remaining().as_secs_f64(),
            needed.as_secs_f64()
        )
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
        let end = Instant::now()
            .checked_sub(Duration::from_secs(5))
            .expect("five seconds must fit in the monotonic clock range");
        let d = Deadline { end };
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
    fn stage_budget_takes_min_and_skips_below_the_useful_floor() {
        let d = Deadline::after(Duration::from_secs(3600));
        // Cap smaller than remaining: the cap.
        assert_eq!(
            d.stage_budget(Duration::from_secs(15), MIN_USEFUL_STAGE_BUDGET),
            Some(Duration::from_secs(15))
        );
        // Cap larger than remaining: the remainder, never past the deadline.
        let got = d.stage_budget(Duration::from_secs(7200), MIN_USEFUL_STAGE_BUDGET).unwrap();
        assert!(got <= Duration::from_secs(3600) && got > Duration::from_secs(3590));
        // Less than the floor left: skip, even though a little time remains.
        let nearly = Deadline::after(Duration::from_millis(400));
        assert_eq!(nearly.stage_budget(Duration::from_secs(15), MIN_USEFUL_STAGE_BUDGET), None);
        // A cap below the floor is also a skip: the floor is the stage's
        // minimum, not the deadline's.
        assert_eq!(d.stage_budget(Duration::from_millis(200), MIN_USEFUL_STAGE_BUDGET), None);
        // Expired: skip.
        let expired = Deadline::after(Duration::ZERO);
        assert_eq!(expired.stage_budget(Duration::from_secs(15), MIN_USEFUL_STAGE_BUDGET), None);
        // Exactly the floor is usable.
        let floor = Deadline::after(Duration::from_secs(3600));
        assert_eq!(
            floor.stage_budget(MIN_USEFUL_STAGE_BUDGET, MIN_USEFUL_STAGE_BUDGET),
            Some(MIN_USEFUL_STAGE_BUDGET)
        );
    }

    #[test]
    fn stage_skipped_marker_is_one_typed_family() {
        let d = Deadline::after(Duration::from_millis(400));
        let marker = d.stage_skipped_marker("bmc-crosscheck", MIN_USEFUL_STAGE_BUDGET);
        assert!(
            marker.starts_with("[AY:STAGE_SKIPPED:bmc-crosscheck:BudgetExhausted] "),
            "{marker}"
        );
        assert!(marker.contains("s of the per-harness deadline left, 1s needed"), "{marker}");
        // The reason segment is the enum's own label, so the marker family and
        // the UNKNOWN_REASON table cannot drift apart.
        assert!(marker.contains(
            crate::verification_provenance::SolverUnknownReason::BudgetExhausted.label()
        ));
        // A stage with a bigger floor says so.
        let retry = d.stage_skipped_marker("two-lane-retry", Duration::from_secs(10));
        assert!(retry.contains("10s needed"), "{retry}");
    }

    /// The arithmetic a harness runs on: the watchdog restarted with 5T+5,
    /// the harness deadline sits WATCHDOG_HEADROOM inside it, and the
    /// stages a harness can chain (T each) fit inside the deadline with the
    /// headroom untouched — a normal harness ends by a typed UNKNOWN before
    /// the watchdog can fire.
    #[test]
    fn harness_stages_fit_inside_the_deadline_with_watchdog_headroom() {
        let t = Duration::from_secs(15);
        let watchdog = crate::wall_clock_watchdog::budget_for(t);
        assert_eq!(watchdog, Duration::from_secs(80));
        let deadline = watchdog - WATCHDOG_HEADROOM;
        // acyclic shortcut (T + 5s guard + 3s drain) + portfolio (T + 5s batch
        // grace) + cross-check (min(T, 30s)) = 3T + 13s = 58s < 70s.
        let chain = t
            + Duration::from_secs(5)
            + Duration::from_secs(3)
            + t
            + Duration::from_secs(5)
            + t.min(Duration::from_secs(30));
        assert!(chain < deadline, "{chain:?} must fit inside {deadline:?}");
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
