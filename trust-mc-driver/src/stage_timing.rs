// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-stage wall-clock markers for one driver run.
//!
//! A harness passes through up to a dozen stages after codegen — the exact
//! acyclic-witness search, the acyclic-BMC shortcut, the per-property batch,
//! the BMC cross-check, the CHC vacuity probe, the cover check, the external
//! `ay` fallback, the two-lane loop-contract retry — and a corpus row only
//! records the process total. To see which stage a 50s row spent its time in,
//! set `TRUST_MC_STAGE_TIMINGS=1` and every stage prints one line on STDERR:
//!
//! ```text
//! [AY:STAGE_MS:<stage>:<milliseconds>:<outcome>]
//! ```
//!
//! Off by default, and stderr only, so no verdict line, expected-output match
//! or marker a scorer reads can change with it. The line is written when the
//! stage ENDS; a stage the watchdog kills prints nothing, and the missing line
//! is itself the signal.

use std::sync::OnceLock;
use std::time::{Duration, Instant};

/// The variable that turns the markers on (`1`, `true`, `yes`, `on`).
pub(crate) const STAGE_TIMINGS_ENV: &str = "TRUST_MC_STAGE_TIMINGS";

static PROCESS_START: OnceLock<Instant> = OnceLock::new();
static ENABLED: OnceLock<bool> = OnceLock::new();

/// Record the process start. Called first thing in `main`; later calls keep
/// the first instant.
pub(crate) fn mark_process_start() {
    let _ = PROCESS_START.get_or_init(Instant::now);
}

/// Wall clock since [`mark_process_start`] (zero if it was never called).
pub(crate) fn since_process_start() -> Duration {
    PROCESS_START.get().map(Instant::elapsed).unwrap_or_default()
}

fn flag_is_on(value: &str) -> bool {
    matches!(value.trim().to_ascii_lowercase().as_str(), "1" | "true" | "yes" | "on")
}

/// Whether the markers are on for this process.
pub(crate) fn enabled() -> bool {
    *ENABLED.get_or_init(|| {
        std::env::var(STAGE_TIMINGS_ENV).ok().as_deref().is_some_and(flag_is_on)
    })
}

/// The marker text for one finished stage.
pub(crate) fn marker(stage: &str, elapsed: Duration, outcome: &str) -> String {
    format!("[AY:STAGE_MS:{stage}:{}:{outcome}]", elapsed.as_millis())
}

/// Print the marker for a stage that started at `started`, when enabled.
pub(crate) fn record(stage: &str, started: Instant, outcome: &str) {
    record_elapsed(stage, started.elapsed(), outcome);
}

/// Print the marker for a stage that took `elapsed`, when enabled.
pub(crate) fn record_elapsed(stage: &str, elapsed: Duration, outcome: &str) {
    if enabled() {
        eprintln!("{}", marker(stage, elapsed, outcome));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn marker_is_one_parseable_line() {
        let line = marker("bmc-crosscheck", Duration::from_millis(1234), "skipped-validated");
        assert_eq!(line, "[AY:STAGE_MS:bmc-crosscheck:1234:skipped-validated]");
        assert!(!line.contains('\n'));
    }

    #[test]
    fn only_affirmative_values_turn_the_markers_on() {
        for on in ["1", "true", "YES", " on "] {
            assert!(flag_is_on(on), "{on:?}");
        }
        for off in ["", "0", "false", "no", "off", "2"] {
            assert!(!flag_is_on(off), "{off:?}");
        }
    }

    #[test]
    fn process_start_is_set_once() {
        mark_process_start();
        let first = since_process_start();
        mark_process_start();
        assert!(since_process_start() >= first, "a second call must not reset the clock");
    }
}
