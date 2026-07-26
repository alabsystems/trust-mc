// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Driver-side wall-clock watchdog (#bug: translation-time infinite loops).
//!
//! Some MIR→CHC translation paths and post-AY cleanup paths can hang
//! indefinitely. The existing `--harness-timeout` is honored only at the
//! AY-solver call boundary, so a translation-time loop never triggers it
//! and the test runner ends up SIGKILL'ing the driver — which produces
//! `execution_state=missing_verdict` (no final marker) and a spurious
//! ERROR verdict.
//!
//! This module installs a single watchdog thread very early in `main()`.
//! When the budget elapses, the watchdog prints a clean UNKNOWN final
//! marker (so the test runner classifies the harness as a real UNKNOWN
//! verdict, not an ERROR), then forcibly exits. Any tracked child
//! subprocesses are also reaped via `SubprocessTracker::cleanup_all`
//! (after the markers are emitted, so marker output cannot be lost to a
//! cleanup failure).
//!
//! Why a hard exit and not unwinding via `Err`? Because the hang may be in
//! foreign code (rustc, trust-mc-compiler) that we cannot unwind out of, or
//! in a blocking syscall that no `Result` propagation can interrupt. The
//! watchdog runs in its own thread so it can tear the entire process down
//! regardless of where the main thread is blocked.
//!
//! The fire path is deliberately lock-free and allocation-free (raw
//! `libc::write` on fds 1/2 via [`crate::raw_io`], then `libc::_exit`):
//! the hung thread may be holding the Rust stdout/stderr locks or the
//! allocator lock, and `println!`/`process::exit` could deadlock on them.
//!
//! ## Arming
//!
//! The watchdog is armed in two stages:
//!
//! 1. [`install_from_argv`] very early in `main()`, parsing
//!    `--harness-timeout` from raw argv (before clap or any TOML merge —
//!    covers hangs in `cargo locate-project` and arg processing itself).
//! 2. [`rearm`] after the final argument values are known (clap parse over
//!    `args_toml::join_args` output, and again after autoharness
//!    `add_default_bounds`). This catches `--harness-timeout` values that
//!    come from `Cargo.toml` config or autoharness defaults — those never
//!    appear in argv and previously left the watchdog unarmed.
//!
//! Budget formula:
//!   driver_wall_clock = harness_timeout * 5 + grace
//!
//! The 5× multiplier matches `scripts/ay-compiletest.sh`'s
//! `shell_timeout_seconds`, which itself reflects ay-chc's retry ladder
//! (engine portfolio 1× + retry ladder 4× = 5× the per-harness budget).
//! Grace defaults to 5s so the watchdog fires before the shell-level
//! SIGKILL at `5 * harness_timeout + 10s`.
//!
//! Multi-harness files: [`extend_for_extra_harnesses`] adds one raw
//! `harness_timeout` per harness beyond the first. This mirrors the outer
//! runners' per-extra-harness scaling (`tools/kani-domination`
//! `RunConfig::outer_timeout` = base + `harness_timeout * (count - 1)`,
//! with a 30s grace vs our 5s), so a multi-harness file is no longer killed
//! mid-run after a single-harness budget while this watchdog still fires —
//! with honest UNKNOWN markers — before the outer SIGKILL.
//!
//! The extension is armed TWICE, idempotently (P5.2): first PRE-codegen
//! from a `#[kani::proof` source scan (standalone projects; codegen cost is
//! per-harness, so an N-harness file must finish N codegens — a
//! post-codegen-only extension left slow-but-finite multi-harness files to
//! hard-kill inside the single-harness budget), then post-codegen from the
//! authoritative metadata harness count, which only tops up any scan
//! undercount (macro-generated harnesses, cargo units).
//!
//! Tunable via env vars:
//!   TRUST_MC_DRIVER_WATCHDOG_MULT     (default: 5)
//!   TRUST_MC_DRIVER_WATCHDOG_GRACE_S  (default: 5)
//!   TRUST_MC_DRIVER_WATCHDOG_DISABLE  (any non-empty value disables)

use std::ffi::OsString;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use once_cell::sync::Lazy;

use crate::raw_io;
use crate::subprocess_tracker::SubprocessTracker;

/// Default per-harness-timeout multiplier (matches shell-script retry-ladder budget).
const DEFAULT_MULT: u64 = 5;

/// Default grace period in seconds (fire before shell-level SIGKILL).
const DEFAULT_GRACE_SECS: u64 = 5;

/// Exit code for verification failure (matches `result_summary::print_final_summary`).
const EXIT_VERIFICATION_FAIL: i32 = 1;

/// Sleep slice for the watchdog loop. Bounds rearm-detection latency:
/// a rearm that *shrinks* the deadline is observed within one slice.
const POLL_SLICE: Duration = Duration::from_millis(250);

/// Monotonic anchor used to encode the deadline as a u64.
static ANCHOR: Lazy<Instant> = Lazy::new(Instant::now);

/// Armed deadline in "milliseconds since [`ANCHOR`]". 0 = unarmed.
static DEADLINE_MS: AtomicU64 = AtomicU64::new(0);

/// Budget seconds of the most recent arm, for the fire message.
static BUDGET_SECS: AtomicU64 = AtomicU64::new(0);

/// Extra harnesses already credited to the CURRENTLY ARMED budget by
/// [`extend_for_extra_harnesses`]. Makes the extension idempotent: the
/// driver arms it once from the pre-codegen source scan (codegen cost is
/// per-harness, so the extension must exist BEFORE the compiler runs — see
/// `project::StandaloneProjectBuilder::build`) and again from the
/// authoritative post-codegen metadata count, which only tops up the
/// difference when the scan undercounted. Reset on every (re)arm/disarm —
/// credits apply to one armed budget, never carried across rearms.
static EXTRA_HARNESSES_CREDITED: AtomicU64 = AtomicU64::new(0);

/// Whether the watchdog thread has been spawned (spawn exactly once).
static THREAD_SPAWNED: AtomicBool = AtomicBool::new(false);

fn anchor_elapsed_ms() -> u64 {
    u64::try_from(ANCHOR.elapsed().as_millis()).unwrap_or(u64::MAX)
}

fn watchdog_disabled() -> bool {
    std::env::var_os("TRUST_MC_DRIVER_WATCHDOG_DISABLE").is_some()
}

/// Compute the driver wall-clock budget for a per-harness timeout:
/// `per_harness * MULT + GRACE` (env-tunable, see module docs).
///
/// Also used by [`crate::deadline`] so the per-harness deadline and the
/// process-wide watchdog agree on the retry-ladder budget shape.
pub(crate) fn budget_for(per_harness: Duration) -> Duration {
    let mult = env_u64("TRUST_MC_DRIVER_WATCHDOG_MULT").unwrap_or(DEFAULT_MULT).max(1);
    let grace = env_u64("TRUST_MC_DRIVER_WATCHDOG_GRACE_S").unwrap_or(DEFAULT_GRACE_SECS);
    per_harness
        .checked_mul(mult.try_into().unwrap_or(u32::MAX))
        .unwrap_or(Duration::from_secs(u64::MAX / 2))
        .saturating_add(Duration::from_secs(grace))
}

/// Install a wall-clock watchdog thread from raw argv.
///
/// Returns silently and does nothing when:
/// - `TRUST_MC_DRIVER_WATCHDOG_DISABLE` is set
/// - `--harness-timeout=<N>{s|m|h}` is absent from `argv`
/// - the parsed timeout is zero
pub(crate) fn install_from_argv(argv: &[OsString]) {
    if watchdog_disabled() {
        return;
    }
    let Some(per_harness) = extract_harness_timeout(argv) else {
        return;
    };
    if per_harness.is_zero() {
        return;
    }
    arm(budget_for(per_harness));
}

/// Re-arm (or arm, or disarm) the watchdog with the authoritative
/// per-harness timeout, restarting the budget clock from "now".
///
/// Called after the final `--harness-timeout` value is known:
/// - after clap parses the `args_toml::join_args`-merged argument list
///   (catches values injected from `Cargo.toml` config), and
/// - after autoharness `add_default_bounds` (catches the autoharness
///   default timeout).
///
/// Semantics:
/// - `Some(t)` with `t > 0`: arm with `budget_for(t)` from now (replaces
///   any previous deadline, longer or shorter).
/// - `Some(0)` or `None`: disarm — no harness timeout is in effect, so a
///   stale argv-derived deadline must not fire.
/// - `TRUST_MC_DRIVER_WATCHDOG_DISABLE`: no-op (never arms; an existing
///   arm cannot exist because install respects the same flag).
pub(crate) fn rearm(per_harness: Option<Duration>) {
    if watchdog_disabled() {
        return;
    }
    match per_harness {
        Some(t) if !t.is_zero() => arm(budget_for(t)),
        _ => disarm(),
    }
}

/// Extend the armed deadline by one raw per-harness timeout per harness
/// beyond the first, once the file's harness COUNT is known (metadata is
/// parsed long after the argv/session arms, which assume one harness).
///
/// The driver budgets `--harness-timeout` PER HARNESS
/// (`Deadline::for_harness`), so a multi-harness file can never complete
/// within the single-harness budget the watchdog was armed with. The
/// scaling shape mirrors the outer runners (`tools/kani-domination`
/// `RunConfig::outer_timeout` = base + `harness_timeout * (count - 1)`);
/// their grace (30s) exceeds ours (5s), so this watchdog still fires first
/// and emits honest UNKNOWN markers instead of being SIGKILLed.
///
/// EXTENDS the existing deadline in place — no clock restart — so the
/// budget stays anchored at the original arm time, exactly like the outer
/// runners' spawn-anchored watchdogs. No-op when the watchdog is disabled,
/// unarmed, the timeout is absent/zero, or the file has <= 1 harness.
/// Never shrinks a deadline. Timeout/completeness-only: verdicts still come
/// from the solver and the demotion nets, so this cannot mint a false Safe.
///
/// IDEMPOTENT (residual-775 Wall-1 P5.2): each call credits only the extra
/// harnesses BEYOND those already credited to the armed budget
/// ([`EXTRA_HARNESSES_CREDITED`]). The driver calls this twice — once
/// pre-codegen from a source scan (codegen cost is per-harness, so a
/// multi-harness file must have its extension BEFORE codegen or it is
/// hard-killed inside the single-harness budget), once post-codegen from
/// the authoritative metadata count (top-up only). A scan OVERCOUNT is
/// never corrected downward (the deadline never shrinks) — the scan
/// mirrors the outer runners' own `#[kani::proof` count, so the driver's
/// budget stays <= theirs and still fires first with honest markers.
pub(crate) fn extend_for_extra_harnesses(per_harness: Option<Duration>, harness_count: usize) {
    if watchdog_disabled() {
        return;
    }
    let Some(per_harness) = per_harness else {
        return;
    };
    let extra_harnesses = u64::try_from(harness_count.saturating_sub(1)).unwrap_or(u64::MAX);
    if per_harness.is_zero() || extra_harnesses == 0 {
        return;
    }
    let deadline_ms = DEADLINE_MS.load(Ordering::SeqCst);
    if deadline_ms == 0 {
        return; // unarmed — no harness timeout is in effect
    }
    // Idempotent top-up: only the not-yet-credited extras extend the deadline.
    let already = EXTRA_HARNESSES_CREDITED.fetch_max(extra_harnesses, Ordering::SeqCst);
    if extra_harnesses <= already {
        return;
    }
    let extra_ms = u64::try_from(per_harness.as_millis())
        .unwrap_or(u64::MAX)
        .saturating_mul(extra_harnesses - already);
    DEADLINE_MS.store(deadline_ms.saturating_add(extra_ms).max(1), Ordering::SeqCst);
    BUDGET_SECS.store(
        BUDGET_SECS.load(Ordering::SeqCst).saturating_add(extra_ms / 1000),
        Ordering::SeqCst,
    );
}

/// Remaining time before the watchdog fires, or `None` when unarmed.
///
/// Subprocess timeout chokepoints (`session::process`) clamp their budgets
/// to this value so no child process can be granted a timeout extending
/// past the watchdog's planned fire time — hung children then surface as
/// ordinary subprocess-timeout errors instead of watchdog hard-exits.
pub(crate) fn remaining() -> Option<Duration> {
    let deadline_ms = DEADLINE_MS.load(Ordering::SeqCst);
    if deadline_ms == 0 {
        return None;
    }
    Some(Duration::from_millis(deadline_ms.saturating_sub(anchor_elapsed_ms())))
}

/// Set the deadline to `now + budget` and ensure the watchdog thread runs.
fn arm(budget: Duration) {
    if budget.is_zero() {
        return;
    }
    // A fresh arm restarts the budget clock with a single-harness budget, so
    // any per-extra-harness credits belong to the PREVIOUS budget and must
    // not suppress a re-extension of this one.
    EXTRA_HARNESSES_CREDITED.store(0, Ordering::SeqCst);
    BUDGET_SECS.store(budget.as_secs(), Ordering::SeqCst);
    let deadline_ms = anchor_elapsed_ms()
        .saturating_add(u64::try_from(budget.as_millis()).unwrap_or(u64::MAX))
        .max(1); // 0 means "unarmed"
    DEADLINE_MS.store(deadline_ms, Ordering::SeqCst);
    ensure_thread();
}

fn disarm() {
    EXTRA_HARNESSES_CREDITED.store(0, Ordering::SeqCst);
    DEADLINE_MS.store(0, Ordering::SeqCst);
}

/// Spawn the watchdog thread exactly once. The thread is detached (never
/// joined) — when the deadline elapses it tears the whole process down.
fn ensure_thread() {
    if THREAD_SPAWNED.swap(true, Ordering::SeqCst) {
        return;
    }
    thread::Builder::new().name("trust-mc-driver-watchdog".into()).spawn(watchdog_loop).ok();
}

/// Watchdog loop: sleep in slices so rearms (extensions, shrinks, and
/// disarms) take effect without restarting the thread.
fn watchdog_loop() -> ! {
    loop {
        let deadline_ms = DEADLINE_MS.load(Ordering::SeqCst);
        if deadline_ms == 0 {
            // Disarmed; poll for a future rearm.
            thread::sleep(POLL_SLICE);
            continue;
        }
        let now_ms = anchor_elapsed_ms();
        if now_ms >= deadline_ms {
            fire(BUDGET_SECS.load(Ordering::SeqCst));
        }
        let remaining = Duration::from_millis(deadline_ms - now_ms);
        thread::sleep(remaining.min(POLL_SLICE));
    }
}

/// Emit the UNKNOWN final markers and exit. Runs only from the watchdog
/// thread in production. Never returns.
///
/// MUST stay lock-free and allocation-free: the process is presumed hung,
/// possibly while holding the Rust stdio locks or the allocator lock.
/// Ordering is deliberate:
/// 1. stderr diagnostic (raw write)
/// 2. stdout final markers (raw write — the load-bearing output)
/// 3. subprocess cleanup (best-effort; AFTER markers so a misbehaving
///    cleanup can no longer suppress the final verdict markers)
/// 4. `_exit` (no atexit handlers/stdio flush — they can take locks)
fn fire(budget_secs: u64) -> ! {
    let mut digits_buf = [0u8; 20];
    let secs = raw_io::u64_decimal(budget_secs, &mut digits_buf);

    raw_io::write_stderr_parts(&[
        b"[trust_mc] driver wall-clock watchdog fired after ",
        secs,
        "s: translation/cleanup hang suspected \u{2014} emitting UNKNOWN and exiting\n".as_bytes(),
    ]);

    // Markers consumed by scripts/ay-compiletest.sh:
    //   - `[AY:UNKNOWN_REASON:DriverTimeout]` makes
    //     `has_unknown_result_markers` true and supplies an
    //     `execution_details=unknown_marker=DriverTimeout` provenance.
    //   - `[AY:UNKNOWN]` is the explicit final-marker form parsed by
    //     `extract_final_verification_outcome`. Emitting both keeps the
    //     parser happy regardless of which path it takes.
    //   - `VERIFICATION:- FAILED` matches the same shape used elsewhere
    //     when an UNKNOWN result causes verification to be reported as
    //     "not successful" (see `verification_result::write_final`).
    raw_io::write_stdout_parts(&[
        b"[AY:UNKNOWN_REASON:DriverTimeout]\n",
        b"[AY:UNKNOWN] driver wall-clock timeout after ",
        secs,
        b"s\nVERIFICATION:- FAILED\n",
    ]);

    // Clean up any tracked subprocesses (rustc, trust-mc-compiler, ay).
    // This avoids leaking child processes that would otherwise survive
    // until the shell's process-group SIGKILL. Runs after marker emission
    // so the final verdict markers cannot be lost to a cleanup hang.
    SubprocessTracker::cleanup_all();

    #[cfg(unix)]
    // SAFETY: _exit is async-signal-safe and takes no locks; it skips
    // atexit handlers and stdio flushing, which could deadlock here.
    unsafe {
        libc::_exit(EXIT_VERIFICATION_FAIL);
    }
    #[cfg(not(unix))]
    std::process::exit(EXIT_VERIFICATION_FAIL);
}

/// Parse `--harness-timeout=<value>` or `--harness-timeout <value>` from
/// raw argv. Recognized suffixes: `s` (default), `m`, `h`. Returns `None`
/// if absent or unparseable — never panics on malformed input.
///
/// Non-UTF8 argv entries are skipped (they cannot be the flag we are
/// looking for, since `--harness-timeout` is pure ASCII).
fn extract_harness_timeout(argv: &[OsString]) -> Option<Duration> {
    let mut iter = argv.iter();
    while let Some(arg) = iter.next() {
        let Some(arg) = arg.to_str() else {
            continue;
        };
        if let Some(rest) = arg.strip_prefix("--harness-timeout=") {
            return parse_timeout_str(rest);
        }
        if arg == "--harness-timeout" {
            let value = iter.next()?.to_str()?;
            return parse_timeout_str(value);
        }
    }
    None
}

/// Parse `<n>[s|m|h]` into a Duration. Default unit is seconds.
fn parse_timeout_str(s: &str) -> Option<Duration> {
    if s.is_empty() {
        return None;
    }
    let last = s.chars().last()?;
    let (digits, unit) = if last.is_ascii_digit() {
        (s, 's')
    } else {
        let (head, _tail) = s.split_at(s.len() - 1);
        (head, last)
    };
    let value: u64 = digits.parse().ok()?;
    let secs = match unit {
        's' => value,
        'm' => value.checked_mul(60)?,
        'h' => value.checked_mul(3600)?,
        _ => return None,
    };
    Some(Duration::from_secs(secs))
}

fn env_u64(name: &str) -> Option<u64> {
    std::env::var(name).ok()?.parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn os(s: &str) -> OsString {
        OsString::from(s)
    }

    #[test]
    fn parse_eq_form_seconds() {
        let argv = vec![os("trust-mc"), os("--harness-timeout=10s"), os("file.rs")];
        assert_eq!(extract_harness_timeout(&argv), Some(Duration::from_secs(10)));
    }

    #[test]
    fn parse_eq_form_default_unit_is_seconds() {
        let argv = vec![os("trust-mc"), os("--harness-timeout=30"), os("file.rs")];
        assert_eq!(extract_harness_timeout(&argv), Some(Duration::from_secs(30)));
    }

    #[test]
    fn parse_eq_form_minutes() {
        let argv = vec![os("trust-mc"), os("--harness-timeout=2m"), os("file.rs")];
        assert_eq!(extract_harness_timeout(&argv), Some(Duration::from_secs(120)));
    }

    #[test]
    fn parse_eq_form_hours() {
        let argv = vec![os("trust-mc"), os("--harness-timeout=1h"), os("file.rs")];
        assert_eq!(extract_harness_timeout(&argv), Some(Duration::from_secs(3600)));
    }

    #[test]
    fn parse_separated_form() {
        let argv = vec![os("trust-mc"), os("--harness-timeout"), os("15s"), os("file.rs")];
        assert_eq!(extract_harness_timeout(&argv), Some(Duration::from_secs(15)));
    }

    #[test]
    fn absent_returns_none() {
        let argv = vec![os("trust-mc"), os("--harness=foo"), os("file.rs")];
        assert_eq!(extract_harness_timeout(&argv), None);
    }

    #[test]
    fn malformed_returns_none() {
        let argv = vec![os("trust-mc"), os("--harness-timeout=abc"), os("file.rs")];
        assert_eq!(extract_harness_timeout(&argv), None);
    }

    #[test]
    fn budget_for_default_is_five_x_plus_grace() {
        // Default env: MULT=5, GRACE=5s (test env must not set the
        // override vars; CI does not).
        assert_eq!(budget_for(Duration::from_secs(10)), Duration::from_secs(55));
    }

    /// rearm semantics, exercised sequentially in ONE test because the
    /// armed deadline is process-global state (parallel test threads
    /// would race). Budgets are hours so the watchdog can never fire
    /// during the test run.
    #[test]
    fn rearm_arm_extend_shrink_disarm() {
        // Arm: 1h harness timeout → ~5h+5s budget.
        rearm(Some(Duration::from_secs(3600)));
        let r1 = remaining().expect("armed after rearm(Some)");
        assert!(r1 > Duration::from_secs(4 * 3600), "expected ~5h, got {r1:?}");

        // Re-arm larger (extend): 2h → ~10h.
        rearm(Some(Duration::from_secs(2 * 3600)));
        let r2 = remaining().expect("still armed");
        assert!(r2 > r1, "rearm must extend the deadline: {r2:?} <= {r1:?}");

        // Re-arm smaller (shrink): back to ~5h.
        rearm(Some(Duration::from_secs(3600)));
        let r3 = remaining().expect("still armed");
        assert!(r3 < r2, "rearm must be able to shrink the deadline");
        assert!(r3 > Duration::from_secs(4 * 3600));

        // Multi-harness extension: 1h timeout, 3 harnesses → +2h on top of ~5h.
        let before = remaining().expect("still armed");
        extend_for_extra_harnesses(Some(Duration::from_secs(3600)), 3);
        let extended = remaining().expect("still armed after extension");
        let gained = extended.saturating_sub(before);
        assert!(
            gained > Duration::from_secs(2 * 3600 - 60) && gained <= Duration::from_secs(2 * 3600),
            "3 harnesses must add ~2 extra harness-timeouts, gained {gained:?}"
        );

        // Idempotency (P5.2): a repeat call with the SAME count is a no-op
        // (the pre-codegen scan and the post-codegen metadata call must not
        // double-extend)...
        let before = remaining().expect("still armed");
        extend_for_extra_harnesses(Some(Duration::from_secs(3600)), 3);
        let after = remaining().expect("still armed");
        assert!(
            after.saturating_sub(before) < Duration::from_secs(60),
            "same-count re-extension must be a no-op"
        );
        // ...and a LARGER count tops up only the difference (3 → 4 = +1h).
        extend_for_extra_harnesses(Some(Duration::from_secs(3600)), 4);
        let topped = remaining().expect("still armed");
        let gained = topped.saturating_sub(before);
        assert!(
            gained > Duration::from_secs(3600 - 60) && gained <= Duration::from_secs(3600),
            "count 3→4 must top up exactly one harness-timeout, gained {gained:?}"
        );
        // ...and a SMALLER count never shrinks.
        extend_for_extra_harnesses(Some(Duration::from_secs(3600)), 2);
        let after_smaller = remaining().expect("still armed");
        assert!(
            topped.saturating_sub(after_smaller) < Duration::from_secs(60),
            "smaller-count re-extension must never shrink the deadline"
        );

        // A fresh rearm resets the per-budget credits: the same count must
        // extend the NEW budget in full again.
        rearm(Some(Duration::from_secs(3600)));
        let before = remaining().expect("armed after rearm");
        extend_for_extra_harnesses(Some(Duration::from_secs(3600)), 3);
        let gained = remaining().expect("still armed").saturating_sub(before);
        assert!(
            gained > Duration::from_secs(2 * 3600 - 60),
            "rearm must reset extension credits, gained {gained:?}"
        );

        // Single-harness (or zero-count) extension is a no-op.
        let before = remaining().expect("still armed");
        extend_for_extra_harnesses(Some(Duration::from_secs(3600)), 1);
        extend_for_extra_harnesses(Some(Duration::from_secs(3600)), 0);
        extend_for_extra_harnesses(None, 10);
        extend_for_extra_harnesses(Some(Duration::ZERO), 10);
        let after = remaining().expect("still armed");
        assert!(
            before.saturating_sub(after) < Duration::from_secs(60),
            "no-op extensions must not change the deadline materially"
        );

        // Zero timeout disarms.
        rearm(Some(Duration::ZERO));
        assert_eq!(remaining(), None, "rearm(Some(0)) must disarm");

        // Extension on an unarmed watchdog is a no-op (stays unarmed).
        extend_for_extra_harnesses(Some(Duration::from_secs(3600)), 6);
        assert_eq!(remaining(), None, "extension must not arm an unarmed watchdog");

        // Re-arm again, then None disarms.
        rearm(Some(Duration::from_secs(3600)));
        assert!(remaining().is_some());
        rearm(None);
        assert_eq!(remaining(), None, "rearm(None) must disarm");
    }
}
