// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-harness translation deadline.
//!
//! Codegen of one harness (reachability, MIR transforms, MIR→CHC translation,
//! emit-time optimization) had no budget of its own. A translation that looped
//! or blew up ran until the DRIVER's process watchdog fired, which hard-exits
//! the whole process: every other harness in the file lost its verdict too, and
//! the row was filed as `DriverTimeout` with no hint of where the time went.
//!
//! This module gives each harness a wall-clock budget derived from the harness
//! timeout the driver forwards (`--translation-timeout`). Hot translation loops
//! call [`check`]. Once the budget is spent, `check` unwinds with a typed
//! [`TranslationTimeout`] payload (via `resume_unwind`, so no panic hook fires
//! and nothing is reported as an ICE). The per-harness boundary in
//! `compiler_interface` catches it, writes a fail-closed artifact carrying a
//! `; TRANSLATION_TIMEOUT:` marker, and moves on to the next harness. The
//! driver reports that harness UNKNOWN with
//! `[AY:UNKNOWN_REASON:TranslationTimeout]`.
//!
//! Soundness: the deadline can only turn a harness into UNKNOWN. The artifact
//! written for a timed-out harness is an unconditionally reachable error
//! relation, so even a consumer that ignores the marker gets FAILURE, never a
//! proof.
//!
//! Every `catch_unwind` boundary inside the compiler that can see a
//! translation panic must hand this payload back with [`resume_if_timeout`];
//! otherwise the timeout would be misreported as a codegen panic.

use std::any::Any;
use std::cell::Cell;
use std::time::{Duration, Instant};

thread_local! {
    static DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
    static BUDGET: Cell<Duration> = const { Cell::new(Duration::ZERO) };
    static TICKS: Cell<u32> = const { Cell::new(0) };
}

/// How many [`check`] calls pass between clock reads. `Instant::now` is cheap
/// but the walker calls `check` per statement; sampling keeps it off profiles
/// while bounding overshoot to a few hundred statements.
const CLOCK_SAMPLE_EVERY: u32 = 64;

/// Opt-in phase timing: `TRUST_MC_PHASE_TIMING=1` prints one
/// `[trust_mc:phase] <name> <ms> ms` line per timed translation phase to stderr,
/// so a slow harness shows where its translation time went. Off by default and
/// read once.
pub(crate) fn phase_timing_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("TRUST_MC_PHASE_TIMING").is_ok_and(|v| v == "1"))
}

/// Times `f` as phase `name` when phase timing is enabled; runs it plainly
/// otherwise. Also a deadline check point at both ends.
pub(crate) fn timed_phase<T>(name: &'static str, f: impl FnOnce() -> T) -> T {
    check_now(name);
    if !phase_timing_enabled() {
        let out = f();
        check_now(name);
        return out;
    }
    let start = Instant::now();
    let out = f();
    eprintln!("[trust_mc:phase] {name} {} ms", start.elapsed().as_millis());
    check_now(name);
    out
}

/// Unwind payload for a harness whose translation exceeded its budget.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TranslationTimeout {
    /// The translation phase whose check point observed the expiry.
    pub phase: &'static str,
    /// The budget that was exceeded.
    pub budget: Duration,
}

impl TranslationTimeout {
    /// The comment line the per-harness artifact carries. The driver matches
    /// the `; TRANSLATION_TIMEOUT:` prefix.
    pub(crate) fn marker_line(&self) -> String {
        format!(
            "; TRANSLATION_TIMEOUT: phase={} budget_ms={}\n",
            self.phase,
            self.budget.as_millis()
        )
    }
}

/// Disarms the deadline when dropped (also on unwind).
#[must_use = "the deadline is disarmed when the guard is dropped"]
pub(crate) struct DeadlineGuard {
    _private: (),
}

impl Drop for DeadlineGuard {
    fn drop(&mut self) {
        DEADLINE.with(|d| d.set(None));
        TICKS.with(|t| t.set(0));
    }
}

/// Arm the deadline for the harness about to be translated.
pub(crate) fn arm(budget: Duration) -> DeadlineGuard {
    let end = Instant::now().checked_add(budget);
    DEADLINE.with(|d| d.set(end));
    BUDGET.with(|b| b.set(budget));
    TICKS.with(|t| t.set(0));
    DeadlineGuard { _private: () }
}

/// Is a deadline armed and already past? Reads the clock unconditionally.
pub(crate) fn expired() -> bool {
    DEADLINE.with(|d| d.get()).is_some_and(|end| Instant::now() >= end)
}

/// Cooperative check point. Unwinds with [`TranslationTimeout`] once the armed
/// budget is spent; a no-op when no deadline is armed.
pub(crate) fn check(phase: &'static str) {
    let tick = TICKS.with(|t| {
        let n = t.get().wrapping_add(1);
        t.set(n);
        n
    });
    if tick % CLOCK_SAMPLE_EVERY != 0 {
        return;
    }
    check_now(phase);
}

/// Like [`check`] but reads the clock on every call. For coarse phase
/// boundaries, where sampling would skip the only check.
pub(crate) fn check_now(phase: &'static str) {
    if expired() {
        let budget = BUDGET.with(|b| b.get());
        // Disarm first: the unwind passes through `Drop` impls and other
        // cleanup that may itself reach a check point.
        DEADLINE.with(|d| d.set(None));
        std::panic::resume_unwind(Box::new(TranslationTimeout { phase, budget }));
    }
}

/// Is this unwind payload a translation timeout?
pub(crate) fn is_timeout_payload(payload: &(dyn Any + Send)) -> bool {
    payload.is::<TranslationTimeout>()
}

/// For `catch_unwind` boundaries that turn panics into fallbacks: re-raise a
/// translation timeout, hand every other payload back to the caller.
pub(crate) fn resume_if_timeout(payload: Box<dyn Any + Send>) -> Box<dyn Any + Send> {
    if is_timeout_payload(payload.as_ref()) {
        std::panic::resume_unwind(payload);
    }
    payload
}

/// The budget for harness number `index` (0-based) of `harness_count`, given
/// the per-harness base budget `base` the driver derived from the harness
/// timeout and the time `elapsed` since the codegen stage began.
///
/// One harness may use up to `2 * base`. The whole stage is capped at
/// `(harness_count + 1) * base`, so a file whose harnesses all hang still
/// leaves the driver's watchdog (`5T + grace + (n - 1)T`) time to solve. A
/// harness that starts after the stage cap is spent still gets `base / 2`,
/// enough for an ordinary harness to translate.
pub(crate) fn per_harness_budget(base: Duration, harness_count: usize, elapsed: Duration) -> Duration {
    let count = u32::try_from(harness_count.max(1)).unwrap_or(u32::MAX);
    let stage_cap = base.saturating_mul(count.saturating_add(1));
    let stage_left = stage_cap.saturating_sub(elapsed);
    stage_left.min(base.saturating_mul(2)).max(base / 2)
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::panic)]
    use super::*;

    const S: fn(u64) -> Duration = Duration::from_secs;

    #[test]
    fn single_harness_gets_twice_the_base() {
        assert_eq!(per_harness_budget(S(15), 1, Duration::ZERO), S(30));
    }

    #[test]
    fn stage_cap_shrinks_later_harnesses_to_a_floor() {
        // 5 harnesses, base 15 s: stage cap 90 s.
        assert_eq!(per_harness_budget(S(15), 5, S(0)), S(30));
        assert_eq!(per_harness_budget(S(15), 5, S(60)), S(30));
        assert_eq!(per_harness_budget(S(15), 5, S(75)), S(15));
        // Past the cap an ordinary harness still gets half the base.
        assert_eq!(per_harness_budget(S(15), 5, S(200)), Duration::from_millis(7_500));
    }

    #[test]
    fn worst_case_stage_fits_inside_the_driver_watchdog() {
        // Driver watchdog for n harnesses at timeout T: 5T + 5 + (n - 1)T.
        for n in 1..=12usize {
            let base = S(15);
            let mut elapsed = Duration::ZERO;
            for _ in 0..n {
                elapsed += per_harness_budget(base, n, elapsed);
            }
            let watchdog = S(15 * 5 + 5 + 15 * (n as u64 - 1));
            assert!(elapsed + S(10) < watchdog, "n={n}: stage {elapsed:?} vs watchdog {watchdog:?}");
        }
    }

    #[test]
    fn zero_count_is_treated_as_one() {
        assert_eq!(per_harness_budget(S(10), 0, Duration::ZERO), S(20));
    }

    #[test]
    fn check_is_a_no_op_when_disarmed() {
        for _ in 0..1000 {
            check("disarmed");
        }
        check_now("disarmed");
        assert!(!expired());
    }

    #[test]
    fn expired_budget_unwinds_with_a_typed_payload() {
        let guard = arm(Duration::ZERO);
        let caught = std::panic::catch_unwind(|| check_now("unit_test_phase")).unwrap_err();
        drop(guard);
        let timeout = caught.downcast_ref::<TranslationTimeout>().expect("typed payload");
        assert_eq!(timeout.phase, "unit_test_phase");
        assert_eq!(timeout.budget, Duration::ZERO);
        // The unwind disarmed the deadline: cleanup code may reach check points.
        check_now("after_unwind");
    }

    #[test]
    fn sampled_check_fires_within_one_sample_window() {
        let guard = arm(Duration::ZERO);
        let caught = std::panic::catch_unwind(|| {
            for _ in 0..=CLOCK_SAMPLE_EVERY {
                check("sampled");
            }
        });
        drop(guard);
        assert!(caught.is_err_and(|p| is_timeout_payload(p.as_ref())));
    }

    #[test]
    fn guard_drop_disarms() {
        {
            let _guard = arm(Duration::ZERO);
            assert!(expired());
        }
        assert!(!expired());
        check_now("after_guard");
    }

    #[test]
    fn generous_budget_does_not_fire() {
        let _guard = arm(S(3600));
        for _ in 0..10_000 {
            check("generous");
        }
        check_now("generous");
    }

    #[test]
    fn resume_if_timeout_passes_ordinary_panics_through() {
        let payload: Box<dyn Any + Send> = Box::new("ordinary panic");
        let back = resume_if_timeout(payload);
        assert_eq!(back.downcast_ref::<&str>(), Some(&"ordinary panic"));
    }

    #[test]
    fn resume_if_timeout_re_raises_a_timeout() {
        let caught = std::panic::catch_unwind(|| {
            let payload: Box<dyn Any + Send> =
                Box::new(TranslationTimeout { phase: "p", budget: S(1) });
            let _ = resume_if_timeout(payload);
        })
        .unwrap_err();
        assert!(is_timeout_payload(caught.as_ref()));
    }

    #[test]
    fn marker_line_names_phase_and_budget() {
        let t = TranslationTimeout { phase: "chc_inline_walker", budget: Duration::from_millis(30_000) };
        assert_eq!(t.marker_line(), "; TRANSLATION_TIMEOUT: phase=chc_inline_walker budget_ms=30000\n");
    }
}
