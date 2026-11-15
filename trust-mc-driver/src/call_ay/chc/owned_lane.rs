// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Owned solver lanes: a spawned solve thread whose `JoinHandle` is kept until
//! the thread has EXITED (AY ask R1, `trust_mc_ay_asks_design_resources.md`).
//!
//! # What this replaces
//!
//! The acyclic-BMC shortcut discarded `thread::spawn`'s handle outright, and
//! the forced-engine guard kept it only on the success and disconnect arms. On
//! a guard timeout both cancelled, waited up to three seconds for a MESSAGE,
//! and then moved on — to the next lane of the same harness, to the external
//! `ay` fallback, or to the next harness — whether or not the lane had stopped.
//! Two things were wrong with that, and AY's ask names both:
//!
//! * a received message is not a completed join: the lane's own destructors
//!   (the captured problem, the portfolio, proof scratch) run AFTER `send`, so
//!   "we got the answer" never meant "the lane has stopped using the cores";
//! * a lane that did not wind down inside the drain was abandoned, so the next
//!   lane shared the cores with it — the overlap the drain was meant to bound.
//!
//! # The contract
//!
//! [`OwnedLane::finish_with`] never returns while the lane's thread is alive,
//! on every arm: result received, guard timeout, panic, disconnected channel.
//! Dropping an unfinished lane (an early return or an unwinding caller) cancels
//! it and joins it too, so no path detaches. What the caller learns is the
//! [`LaneJoinReport`]: how the lane ended, whether cancellation was requested,
//! and how long the thread took to exit after that request (or after its
//! result arrived).
//!
//! A cancelled lane that is still alive after the drain limit is a FAILED
//! drain ([`LaneJoinReport::drain_failed`]): AY's acceptance failure, which the
//! caller reports. This module then keeps waiting for the thread to exit —
//! Rust cannot kill a thread, and returning would leave it running beside
//! whatever the caller starts next. Once it has exited and been joined it is
//! gone, so the caller goes on with the rest of the harness on what is left of
//! its deadline: the failed drain is reported, not charged to the harness a
//! second time by forfeiting its remaining lanes.
//!
//! # What "exited" means: after the last thread-local destructor
//!
//! `JoinHandle::is_finished` is NOT that. std flips it when the thread's Rust
//! entry closure drops its result packet, and the thread's thread-local
//! destructors run only after that, at thread exit. The cleanup a lane does
//! after sending its value is exactly those destructors (the work closure's
//! captures drop before `send`; AY keeps term stores and SMT contexts in
//! thread-locals), so polling `is_finished` saw a lane still in cleanup as
//! exited, and the `join` that followed blocked through the rest of it with no
//! bound at all. Measured by
//! `a_lane_that_delivers_then_lingers_past_the_deadline_is_completed_and_quarantined`:
//! against `is_finished` the lane was never abandoned and `finish` returned
//! after the full 60-s linger. Each lane therefore arms a [`ThreadExit`]
//! signal as the FIRST thing its thread does: a thread-local registered before
//! any other the lane touches, so it is destroyed LAST (std runs thread-local
//! destructors in reverse registration order: glibc's
//! `__cxa_thread_atexit_impl` list and std's own fallback list both pop the
//! newest first). Every wait below polls that signal; once it is set, `join`
//! returns promptly. Were the order ever different, the signal would only come
//! early, and the `join` after it would block as it did before — never
//! detach.
//!
//! # Bounded by the harness deadline: the quarantine
//!
//! That wait is bounded by the harness deadline ([`OwnedLane::abandon_at`]).
//! A lane still alive then is ABANDONED into the process-wide
//! [`LANE_QUARANTINE`]: its handle is kept (never dropped, so no timed join is
//! manufactured), [`LaneJoinReport::abandoned`] says so, and the caller ends
//! the harness UNKNOWN. Every later harness first waits on
//! [`LaneQuarantine::wait_clear`] under ITS deadline, joining the lane once it
//! exits, and ends UNKNOWN without starting any work if the lane still lives
//! at that deadline. So a lane that never exits costs each remaining harness
//! an honest UNKNOWN, instead of holding one harness until the process
//! `wall_clock_watchdog` kills the whole file, and it never runs beside a new
//! lane: no harness starts work while it lives. The watchdog stays the outer
//! containment.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError, TryRecvError};
use std::sync::{Arc, Mutex, PoisonError};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

/// How long a cancelled lane may take to exit before the drain counts as
/// failed. AY's T2/B2 acceptance names this three-second driver drain.
pub(super) const LANE_DRAIN_LIMIT: Duration = Duration::from_secs(3);

/// Poll interval while waiting for a lane's thread to exit. `JoinHandle` has
/// no timed join, so the wait polls `is_finished`; the interval only bounds how
/// late an exit is noticed.
const EXIT_POLL: Duration = Duration::from_millis(2);

/// Poll interval once the drain limit has passed (a failed drain waiting for
/// its exit, or for the harness deadline), and in the quarantine gate.
const LATE_EXIT_POLL: Duration = Duration::from_millis(20);

/// Set once a lane's thread has run its last thread-local destructor: the
/// point after which `join` no longer blocks. See the module docs.
#[derive(Clone, Debug)]
struct ThreadExit(Arc<AtomicBool>);

/// The thread-local whose destructor sets [`ThreadExit`].
struct ExitSentinel(Arc<AtomicBool>);

impl Drop for ExitSentinel {
    fn drop(&mut self) {
        self.0.store(true, Ordering::Release);
    }
}

thread_local! {
    static EXIT_SENTINEL: std::cell::RefCell<Option<ExitSentinel>> =
        const { std::cell::RefCell::new(None) };
}

impl ThreadExit {
    fn new() -> Self {
        Self(Arc::new(AtomicBool::new(false)))
    }

    /// Called first thing on the lane's own thread: registers the sentinel
    /// before any other thread-local the lane touches.
    fn arm_on_this_thread(&self) {
        let sentinel = ExitSentinel(Arc::clone(&self.0));
        EXIT_SENTINEL.with(|slot| *slot.borrow_mut() = Some(sentinel));
    }

    fn exited(&self) -> bool {
        self.0.load(Ordering::Acquire)
    }
}

/// A lane's thread: its handle and its exit signal.
struct LaneThread {
    handle: JoinHandle<()>,
    exit: ThreadExit,
}

impl LaneThread {
    /// The thread has run its last thread-local destructor, so `join` returns
    /// promptly. (`is_finished` alone turns true before those destructors.)
    fn exited(&self) -> bool {
        self.exit.exited() && self.handle.is_finished()
    }

    fn join(self) -> std::thread::Result<()> {
        self.handle.join()
    }
}

/// Lanes abandoned at their harness's deadline while still alive, kept until
/// they exit. See the module docs.
pub(super) struct LaneQuarantine {
    lanes: Mutex<Vec<QuarantinedLane>>,
}

struct QuarantinedLane {
    lane: &'static str,
    thread: LaneThread,
    abandoned: Instant,
}

/// What [`LaneQuarantine::wait_clear`] found.
#[derive(Debug, PartialEq, Eq)]
pub(super) enum QuarantineWait {
    /// No abandoned lane is alive. `joined` lists each lane this call joined
    /// and how long after its abandonment the join happened.
    Clear { joined: Vec<(&'static str, Duration)> },
    /// Abandoned lanes still alive when the wait ended, and how long ago the
    /// oldest of them was abandoned.
    Busy { lanes: Vec<&'static str>, oldest: Duration },
}

impl LaneQuarantine {
    pub(super) const fn new() -> Self {
        Self { lanes: Mutex::new(Vec::new()) }
    }

    fn admit(&self, lane: &'static str, thread: LaneThread) {
        let mut lanes = self.lanes.lock().unwrap_or_else(PoisonError::into_inner);
        lanes.push(QuarantinedLane { lane, thread, abandoned: Instant::now() });
    }

    /// Abandoned lanes whose thread has not exited yet.
    pub(super) fn live(&self) -> usize {
        let lanes = self.lanes.lock().unwrap_or_else(PoisonError::into_inner);
        lanes.iter().filter(|q| !q.thread.exited()).count()
    }

    /// Wait until no abandoned lane is alive, or until `until`. Every lane
    /// found exited is joined (and removed). Returns at once when nothing was
    /// ever abandoned.
    pub(super) fn wait_clear(&self, until: Instant) -> QuarantineWait {
        let mut joined = Vec::new();
        loop {
            {
                let mut lanes = self.lanes.lock().unwrap_or_else(PoisonError::into_inner);
                let mut index = 0;
                while index < lanes.len() {
                    if lanes[index].thread.exited() {
                        let exited = lanes.swap_remove(index);
                        let after = exited.abandoned.elapsed();
                        let _ = exited.thread.join();
                        joined.push((exited.lane, after));
                    } else {
                        index += 1;
                    }
                }
                if lanes.is_empty() {
                    return QuarantineWait::Clear { joined };
                }
                if Instant::now() >= until {
                    let oldest =
                        lanes.iter().map(|q| q.abandoned.elapsed()).max().unwrap_or(Duration::ZERO);
                    return QuarantineWait::Busy {
                        lanes: lanes.iter().map(|q| q.lane).collect(),
                        oldest,
                    };
                }
            }
            std::thread::sleep(LATE_EXIT_POLL);
        }
    }
}

/// The process-wide quarantine every production lane is abandoned into, and
/// that `run_ay` waits on before a harness starts any work.
pub(super) static LANE_QUARANTINE: LaneQuarantine = LaneQuarantine::new();

/// How the lane ended, from the caller's side of the guard.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LaneExit {
    /// The lane delivered its result before the guard fired.
    Completed,
    /// The guard fired first; the lane was cancelled and drained.
    TimedOut,
    /// The lane's thread panicked without delivering a result.
    Panicked,
    /// The channel closed without a result and the thread exited normally.
    Disconnected,
}

impl LaneExit {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Completed => "completed",
            Self::TimedOut => "timeout",
            Self::Panicked => "panic",
            Self::Disconnected => "disconnected",
        }
    }
}

/// What the caller gets back besides the lane's value: the join record that
/// the run log carries (`[AY:LANE-JOIN]`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct LaneJoinReport {
    pub(super) lane: &'static str,
    pub(super) exit: LaneExit,
    /// Spawn to the guard's decision (result received, timeout, or disconnect).
    pub(super) waited: Duration,
    /// Whether the guard asked the lane to cancel (timeout arm only).
    pub(super) cancel_requested: bool,
    /// Guard decision (cancellation request, or result/disconnect receipt) to
    /// the thread's exit — the lane's wind-down plus its cleanup. Measured
    /// even when it exceeds the limit, because this module waits it out.
    pub(super) drain: Duration,
    /// The limit `drain` was held to.
    pub(super) drain_limit: Duration,
    /// The lane was still alive at the harness deadline and was abandoned
    /// into the quarantine instead of joined. `drain` then runs to the
    /// abandonment.
    pub(super) abandoned: bool,
}

impl LaneJoinReport {
    /// The lane exited inside the drain limit.
    pub(super) fn drained_within_limit(&self) -> bool {
        self.drain <= self.drain_limit
    }

    /// A CANCELLED lane outlived the drain limit: an acceptance failure under
    /// AY's R1 contract, which the caller reports. Unless [`Self::abandoned`],
    /// the lane has been joined (it is gone), so the caller goes on.
    pub(super) fn drain_failed(&self) -> bool {
        self.cancel_requested && !self.drained_within_limit()
    }

    /// The lane was still alive at the harness deadline: it is in the
    /// quarantine, not joined, and the caller must end the harness.
    pub(super) fn abandoned(&self) -> bool {
        self.abandoned
    }

    /// A lane that delivered (or lost) its result but took longer than the
    /// drain limit to exit: cleanup ran past the limit. Reported, not a
    /// failure — nothing was cancelled, and the lane is gone.
    pub(super) fn slow_cleanup(&self) -> bool {
        !self.cancel_requested && !self.drained_within_limit()
    }

    fn drain_label(&self) -> &'static str {
        if self.abandoned {
            "abandoned"
        } else if self.drain_failed() {
            "failed"
        } else if self.slow_cleanup() {
            "slow-cleanup"
        } else {
            "joined"
        }
    }

    /// One stable, grep-able line per lane for the run log.
    pub(super) fn marker_line(&self) -> String {
        format!(
            "[AY:LANE-JOIN] lane={} exit={} cancel={} drain={} drain_ms={} drain_limit_ms={} \
             waited_ms={}",
            self.lane,
            self.exit.label(),
            if self.cancel_requested { "requested" } else { "none" },
            self.drain_label(),
            self.drain.as_millis(),
            self.drain_limit.as_millis(),
            self.waited.as_millis(),
        )
    }

    /// `stage_timing` outcome label: `<exit>/<drain>`.
    pub(super) fn stage_label(&self) -> String {
        format!("{}/{}", self.exit.label(), self.drain_label())
    }
}

/// The lane's value, by arm.
#[derive(Debug)]
pub(super) enum LaneOutcome<T> {
    /// Delivered before the guard fired.
    Completed(T),
    /// The guard fired. `drained` is a value the lane delivered while winding
    /// down; callers that already decided to discard the lane ignore it.
    TimedOut { drained: Option<T> },
    /// The thread panicked; the payload's message.
    Panicked(String),
    /// The channel closed without a value and the thread exited normally.
    Disconnected,
}

/// A spawned lane whose thread is always joined, or kept in the quarantine
/// past the harness deadline. See the module docs.
pub(super) struct OwnedLane<T> {
    lane: &'static str,
    thread: Option<LaneThread>,
    rx: Receiver<T>,
    started: Instant,
    cancel: Option<Box<dyn FnOnce() + Send>>,
    /// The harness deadline: past it (and past the drain limit) a live lane
    /// is abandoned into `quarantine` instead of waited on. `None` waits for
    /// the exit however long it takes.
    abandon_at: Option<Instant>,
    quarantine: &'static LaneQuarantine,
}

/// How [`OwnedLane::join_after`] ended.
enum JoinEnd {
    /// The thread exited and was joined; `Err` carries a panic's message.
    Joined(Result<(), String>),
    /// The thread was alive at the abandonment bound and is in the quarantine.
    Abandoned,
}

impl<T: Send + 'static> OwnedLane<T> {
    /// Spawn `work` on a named thread. `cancel` is what the guard calls on a
    /// timeout (and what `Drop` calls on an unfinished lane); it must reach
    /// every cancellation token the work observes.
    pub(super) fn spawn<W, C>(lane: &'static str, cancel: C, work: W) -> std::io::Result<Self>
    where
        W: FnOnce() -> T + Send + 'static,
        C: FnOnce() + Send + 'static,
    {
        let (tx, rx) = mpsc::channel();
        let exit = ThreadExit::new();
        let armed = exit.clone();
        let handle =
            std::thread::Builder::new().name(format!("trust-mc-{lane}")).spawn(move || {
                // First, before the work touches any thread-local: the exit
                // signal's destructor then runs after all of the lane's own.
                armed.arm_on_this_thread();
                let value = work();
                let _ = tx.send(value);
            })?;
        Ok(Self {
            lane,
            thread: Some(LaneThread { handle, exit }),
            rx,
            started: Instant::now(),
            cancel: Some(Box::new(cancel)),
            abandon_at: None,
            quarantine: &LANE_QUARANTINE,
        })
    }

    /// Bound every wait for this lane's exit by `at`, the harness deadline
    /// (never earlier than the drain limit after cancellation): a lane still
    /// alive then is abandoned into the quarantine. See the module docs.
    pub(super) fn abandon_at(mut self, at: Instant) -> Self {
        self.abandon_at = Some(at);
        self
    }

    /// Abandon into `quarantine` instead of the process-wide one (tests).
    #[cfg(test)]
    fn quarantine_in(mut self, quarantine: &'static LaneQuarantine) -> Self {
        self.quarantine = quarantine;
        self
    }

    /// Wait up to `guard` for the lane's value; on timeout cancel it and drain
    /// it. Joins the thread on every arm before returning.
    pub(super) fn finish(self, guard: Duration) -> (LaneOutcome<T>, LaneJoinReport) {
        self.finish_with(guard, LANE_DRAIN_LIMIT)
    }

    /// [`Self::finish`] with an explicit drain limit (tests use a short one).
    pub(super) fn finish_with(
        mut self,
        guard: Duration,
        drain_limit: Duration,
    ) -> (LaneOutcome<T>, LaneJoinReport) {
        let received = self.rx.recv_timeout(guard);
        let decided = Instant::now();
        let waited = decided.saturating_duration_since(self.started);
        let mut cancel_requested = false;
        let outcome = match received {
            Ok(value) => LaneOutcome::Completed(value),
            Err(RecvTimeoutError::Timeout) => {
                cancel_requested = true;
                if let Some(cancel) = self.cancel.take() {
                    cancel();
                }
                // Filled in after the join below: a value the lane delivers
                // while winding down is in the channel by the time it exits.
                LaneOutcome::TimedOut { drained: None }
            }
            Err(RecvTimeoutError::Disconnected) => LaneOutcome::Disconnected,
        };
        let joined = self.join_after(decided, drain_limit);
        let abandoned = matches!(joined, JoinEnd::Abandoned);
        let outcome = match (outcome, joined) {
            (LaneOutcome::TimedOut { .. }, _) => {
                let drained = match self.rx.try_recv() {
                    Ok(value) => Some(value),
                    Err(TryRecvError::Empty | TryRecvError::Disconnected) => None,
                };
                LaneOutcome::TimedOut { drained }
            }
            (LaneOutcome::Disconnected, JoinEnd::Joined(Err(message))) => {
                LaneOutcome::Panicked(message)
            }
            (outcome, _) => outcome,
        };
        let exit = match &outcome {
            LaneOutcome::Completed(_) => LaneExit::Completed,
            LaneOutcome::TimedOut { .. } => LaneExit::TimedOut,
            LaneOutcome::Panicked(_) => LaneExit::Panicked,
            LaneOutcome::Disconnected => LaneExit::Disconnected,
        };
        let report = LaneJoinReport {
            lane: self.lane,
            exit,
            waited,
            cancel_requested,
            // Read after `join_after` returned: the full wind-down plus
            // cleanup, including any part past the limit (to the abandonment,
            // for an abandoned lane).
            drain: decided.elapsed(),
            drain_limit,
            abandoned,
        };
        (outcome, report)
    }

    /// Wait for the thread to exit, then join it. Polls up to `drain_limit`
    /// past `from`, then keeps waiting — to the exit, or, when
    /// [`Self::abandon_at`] set a bound, to that bound, where a live lane is
    /// moved into the quarantine. It is never dropped while running.
    fn join_after(&mut self, from: Instant, drain_limit: Duration) -> JoinEnd {
        let Some(thread) = self.thread.take() else {
            return JoinEnd::Joined(Ok(()));
        };
        let drain_end = from + drain_limit;
        let hold_until = self.abandon_at.map(|at| at.max(drain_end));
        while !thread.exited() {
            let now = Instant::now();
            if now < drain_end {
                std::thread::sleep(EXIT_POLL);
                continue;
            }
            match hold_until {
                // No bound: block in `join` below.
                None => break,
                Some(until) if now >= until => {
                    self.quarantine.admit(self.lane, thread);
                    return JoinEnd::Abandoned;
                }
                Some(_) => std::thread::sleep(LATE_EXIT_POLL),
            }
        }
        JoinEnd::Joined(
            thread.join().map_err(|payload| panic_message(payload.as_ref()).to_string()),
        )
    }
}

impl<T> Drop for OwnedLane<T> {
    /// An unfinished lane (the caller returned or unwound without calling
    /// `finish`) is cancelled and JOINED, never detached — or, past its
    /// harness deadline, kept in the quarantine.
    fn drop(&mut self) {
        if let Some(thread) = self.thread.take() {
            if !thread.exited()
                && let Some(cancel) = self.cancel.take()
            {
                cancel();
            }
            let Some(at) = self.abandon_at else {
                let _ = thread.join();
                return;
            };
            let hold_until = at.max(Instant::now() + LANE_DRAIN_LIMIT);
            while !thread.exited() && Instant::now() < hold_until {
                std::thread::sleep(EXIT_POLL);
            }
            if thread.exited() {
                let _ = thread.join();
            } else {
                eprintln!(
                    "[AY:LANE-ABANDONED] lane={} dropped unfinished and still alive at its \
                     harness deadline; quarantined until it exits",
                    self.lane
                );
                self.quarantine.admit(self.lane, thread);
            }
        }
    }
}

fn panic_message(payload: &(dyn std::any::Any + Send)) -> &str {
    payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or("<non-string panic>")
}

/// Budget for re-running a lane's verdict-only BMC after its evidence run
/// failed internally (an AY-classified panic), or `None` when the attempt's
/// authority has closed.
///
/// AY's R1 ask: "remove the `Err(_) => solve_bmc_only(...)` panic retry if
/// attempt cancellation/deadline has closed; failures must not restart full
/// work after the authority boundary". So the retry is refused once the lane
/// was cancelled or less than `min_useful` is left of the lane's own budget or
/// of the per-harness deadline, and when it runs it gets what is LEFT of the
/// lane's budget — never a fresh full one.
pub(super) fn bmc_retry_budget(
    cancelled: bool,
    lane_remaining: Duration,
    harness_remaining: Duration,
    min_useful: Duration,
) -> Option<Duration> {
    if cancelled {
        return None;
    }
    let remaining = lane_remaining.min(harness_remaining);
    (remaining >= min_useful).then_some(remaining)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    /// Counts live lane bodies: incremented when the body starts, decremented
    /// by `Drop` — which runs AFTER the body's value was sent when the sentinel
    /// is captured by the work closure. `finish` must not return while it is
    /// non-zero.
    struct LiveSentinel {
        live: Arc<AtomicUsize>,
        linger: Duration,
    }

    impl LiveSentinel {
        fn new(live: &Arc<AtomicUsize>, linger: Duration) -> Self {
            live.fetch_add(1, Ordering::SeqCst);
            Self { live: Arc::clone(live), linger }
        }
    }

    impl Drop for LiveSentinel {
        fn drop(&mut self) {
            std::thread::sleep(self.linger);
            self.live.fetch_sub(1, Ordering::SeqCst);
        }
    }

    fn wait_for(flag: &AtomicBool, limit: Duration) {
        let start = Instant::now();
        while !flag.load(Ordering::SeqCst) && start.elapsed() < limit {
            std::thread::sleep(Duration::from_millis(1));
        }
    }

    #[test]
    fn a_completed_lane_returns_its_value_and_is_joined() {
        let live = Arc::new(AtomicUsize::new(0));
        let sentinel_live = Arc::clone(&live);
        let lane = OwnedLane::spawn(
            "t-complete",
            || {},
            move || {
                let _sentinel = LiveSentinel::new(&sentinel_live, Duration::ZERO);
                41 + 1
            },
        )
        .unwrap();
        let (outcome, report) = lane.finish_with(Duration::from_secs(10), LANE_DRAIN_LIMIT);
        assert!(matches!(outcome, LaneOutcome::Completed(42)));
        assert_eq!(report.exit, LaneExit::Completed);
        assert!(!report.cancel_requested);
        assert!(!report.drain_failed());
        assert_eq!(live.load(Ordering::SeqCst), 0, "the lane body must be gone on return");
        assert!(report.marker_line().contains("lane=t-complete exit=completed cancel=none"));
    }

    /// "A received message is not a completed join": thread-local state (AY
    /// keeps term stores and SMT contexts in thread-locals) is destroyed AFTER
    /// the lane has sent its value. `finish` waits for that cleanup.
    #[test]
    fn a_result_does_not_end_the_wait_before_the_lanes_cleanup_has_run() {
        thread_local! {
            static HELD: std::cell::RefCell<Option<LiveSentinel>> =
                const { std::cell::RefCell::new(None) };
        }
        let live = Arc::new(AtomicUsize::new(0));
        let sentinel_live = Arc::clone(&live);
        let lane = OwnedLane::spawn(
            "t-cleanup",
            || {},
            move || {
                let sentinel = LiveSentinel::new(&sentinel_live, Duration::from_millis(150));
                HELD.with(|held| *held.borrow_mut() = Some(sentinel));
                7
            },
        )
        .unwrap();
        let (outcome, report) = lane.finish_with(Duration::from_secs(10), LANE_DRAIN_LIMIT);
        assert!(matches!(outcome, LaneOutcome::Completed(7)));
        assert_eq!(live.load(Ordering::SeqCst), 0, "cleanup after send must have finished");
        assert!(report.drain >= Duration::from_millis(100), "{report:?}");
        assert!(!report.drain_failed() && !report.slow_cleanup());
    }

    #[test]
    fn a_timed_out_lane_is_cancelled_and_drained_within_the_limit() {
        let stop = Arc::new(AtomicBool::new(false));
        let observed = Arc::clone(&stop);
        let lane = OwnedLane::spawn(
            "t-cancel",
            {
                let stop = Arc::clone(&stop);
                move || stop.store(true, Ordering::SeqCst)
            },
            move || {
                wait_for(&observed, Duration::from_secs(30));
                "wound-down"
            },
        )
        .unwrap();
        let (outcome, report) = lane.finish_with(Duration::from_millis(20), Duration::from_secs(5));
        assert!(stop.load(Ordering::SeqCst), "the guard must request cancellation");
        match outcome {
            LaneOutcome::TimedOut { drained } => assert_eq!(drained, Some("wound-down")),
            other => panic!("expected a timeout, got {other:?}"),
        }
        assert_eq!(report.exit, LaneExit::TimedOut);
        assert!(report.cancel_requested);
        assert!(report.drained_within_limit());
        assert!(!report.drain_failed());
        assert!(report.marker_line().contains("cancel=requested drain=joined"));
    }

    /// A lane that ignores cancellation past the drain limit is a FAILED drain,
    /// and `finish` still does not return while it lives.
    #[test]
    fn a_lane_that_outlives_the_drain_limit_is_reported_failed_and_still_joined() {
        let live = Arc::new(AtomicUsize::new(0));
        let sentinel_live = Arc::clone(&live);
        let cancelled = Arc::new(AtomicBool::new(false));
        let lane = OwnedLane::spawn(
            "t-stuck",
            {
                let cancelled = Arc::clone(&cancelled);
                move || cancelled.store(true, Ordering::SeqCst)
            },
            move || {
                let _sentinel = LiveSentinel::new(&sentinel_live, Duration::ZERO);
                // Non-cooperative: ignores the cancellation for 300 ms.
                std::thread::sleep(Duration::from_millis(300));
            },
        )
        .unwrap();
        let (outcome, report) =
            lane.finish_with(Duration::from_millis(10), Duration::from_millis(50));
        assert!(cancelled.load(Ordering::SeqCst));
        assert!(matches!(outcome, LaneOutcome::TimedOut { .. }));
        assert!(report.drain_failed(), "{report:?}");
        assert!(report.drain >= Duration::from_millis(200), "{report:?}");
        assert_eq!(live.load(Ordering::SeqCst), 0, "a failed drain must still join the lane");
        assert!(report.marker_line().contains("drain=failed"));
        assert_eq!(report.stage_label(), "timeout/failed");
    }

    fn private_quarantine() -> &'static LaneQuarantine {
        Box::leak(Box::new(LaneQuarantine::new()))
    }

    /// A failed drain that ends INSIDE the harness deadline is joined, not
    /// abandoned: the caller goes on with the rest of the harness.
    #[test]
    fn a_failed_drain_inside_the_harness_deadline_is_joined_not_abandoned() {
        let quarantine = private_quarantine();
        let live = Arc::new(AtomicUsize::new(0));
        let sentinel_live = Arc::clone(&live);
        let lane = OwnedLane::spawn(
            "t-late",
            || {},
            move || {
                let _sentinel = LiveSentinel::new(&sentinel_live, Duration::ZERO);
                std::thread::sleep(Duration::from_millis(300));
            },
        )
        .unwrap()
        .abandon_at(Instant::now() + Duration::from_secs(20))
        .quarantine_in(quarantine);
        let (outcome, report) =
            lane.finish_with(Duration::from_millis(10), Duration::from_millis(50));
        assert!(matches!(outcome, LaneOutcome::TimedOut { .. }));
        assert!(report.drain_failed() && !report.abandoned(), "{report:?}");
        assert_eq!(live.load(Ordering::SeqCst), 0, "the late lane must be joined");
        assert_eq!(quarantine.live(), 0);
        assert!(report.marker_line().contains("drain=failed"));
    }

    /// The wait for a lane's exit is bounded by the harness deadline: a lane
    /// still alive then is abandoned into the quarantine (never dropped), and
    /// the quarantine gate joins it once it exits. Before the bound, `finish`
    /// blocked until the lane exited, however long that took.
    #[test]
    fn a_lane_alive_at_the_harness_deadline_is_quarantined_not_waited_on() {
        let quarantine = private_quarantine();
        let live = Arc::new(AtomicUsize::new(0));
        let sentinel_live = Arc::clone(&live);
        let release = Arc::new(AtomicBool::new(false));
        let released = Arc::clone(&release);
        let lane = OwnedLane::spawn(
            "t-wedged",
            || {},
            move || {
                let _sentinel = LiveSentinel::new(&sentinel_live, Duration::ZERO);
                // Non-cooperative: ignores the cancellation until released.
                wait_for(&released, Duration::from_secs(60));
            },
        )
        .unwrap()
        .abandon_at(Instant::now() + Duration::from_millis(300))
        .quarantine_in(quarantine);
        let started = Instant::now();
        let (outcome, report) =
            lane.finish_with(Duration::from_millis(10), Duration::from_millis(50));
        let returned_after = started.elapsed();
        assert!(matches!(outcome, LaneOutcome::TimedOut { drained: None }));
        assert!(report.abandoned() && report.drain_failed(), "{report:?}");
        assert!(returned_after < Duration::from_secs(5), "finish waited {returned_after:?}");
        assert!(report.marker_line().contains("drain=abandoned"));
        assert_eq!(report.stage_label(), "timeout/abandoned");
        assert_eq!(quarantine.live(), 1, "the abandoned lane is kept, not dropped");
        assert_eq!(live.load(Ordering::SeqCst), 1);

        // A later harness's gate: busy while the lane lives ...
        match quarantine.wait_clear(Instant::now() + Duration::from_millis(50)) {
            QuarantineWait::Busy { lanes, .. } => assert_eq!(lanes, vec!["t-wedged"]),
            other => panic!("expected a busy quarantine, got {other:?}"),
        }
        // ... and clear, with the lane joined, once it exits.
        release.store(true, Ordering::SeqCst);
        match quarantine.wait_clear(Instant::now() + Duration::from_secs(30)) {
            QuarantineWait::Clear { joined } => {
                assert_eq!(joined.len(), 1);
                assert_eq!(joined[0].0, "t-wedged");
            }
            other => panic!("expected a clear quarantine, got {other:?}"),
        }
        assert_eq!(live.load(Ordering::SeqCst), 0, "the gate must have joined the lane");
        assert_eq!(quarantine.live(), 0);
        assert_eq!(
            quarantine.wait_clear(Instant::now()),
            QuarantineWait::Clear { joined: Vec::new() },
            "an empty quarantine answers at once"
        );
    }

    /// Review round 2: a lane that DELIVERS its value and then lingers in
    /// cleanup past the harness deadline. `finish` returns the delivered value
    /// as `Completed` with the lane ABANDONED (quarantined, not waited on),
    /// no cancellation requested, and no failed drain — the state the two
    /// guards used to handle differently (`native::settle_lane` now applies
    /// one rule to it).
    #[test]
    fn a_lane_that_delivers_then_lingers_past_the_deadline_is_completed_and_quarantined() {
        thread_local! {
            static HELD: std::cell::RefCell<Option<LiveSentinel>> =
                const { std::cell::RefCell::new(None) };
        }
        let quarantine = private_quarantine();
        let live = Arc::new(AtomicUsize::new(0));
        let sentinel_live = Arc::clone(&live);
        let cancelled = Arc::new(AtomicBool::new(false));
        let release = Arc::new(AtomicBool::new(false));
        let released = Arc::clone(&release);
        let lane = OwnedLane::spawn(
            "t-deliver-linger",
            {
                let cancelled = Arc::clone(&cancelled);
                move || cancelled.store(true, Ordering::SeqCst)
            },
            move || {
                // Cleanup that runs AFTER the value is sent (a thread-local
                // destructor), and outlives the harness deadline.
                struct Linger(Arc<AtomicBool>, LiveSentinel);
                impl Drop for Linger {
                    fn drop(&mut self) {
                        wait_for(&self.0, Duration::from_secs(60));
                    }
                }
                let sentinel = LiveSentinel::new(&sentinel_live, Duration::ZERO);
                HELD.with(|held| *held.borrow_mut() = Some(sentinel));
                thread_local! {
                    static LINGER: std::cell::RefCell<Option<Linger>> =
                        const { std::cell::RefCell::new(None) };
                }
                let hold = LiveSentinel::new(&sentinel_live, Duration::ZERO);
                LINGER.with(|l| *l.borrow_mut() = Some(Linger(released, hold)));
                "delivered"
            },
        )
        .unwrap()
        .abandon_at(Instant::now() + Duration::from_millis(300))
        .quarantine_in(quarantine);
        let started = Instant::now();
        let (outcome, report) =
            lane.finish_with(Duration::from_secs(10), Duration::from_millis(50));
        let returned_after = started.elapsed();
        assert!(matches!(outcome, LaneOutcome::Completed("delivered")), "{outcome:?}");
        assert_eq!(report.exit, LaneExit::Completed);
        assert!(report.abandoned(), "{report:?}");
        assert!(!report.cancel_requested && !report.drain_failed(), "{report:?}");
        assert!(!cancelled.load(Ordering::SeqCst), "a delivered lane is never cancelled");
        assert!(returned_after < Duration::from_secs(5), "finish waited {returned_after:?}");
        assert_eq!(report.stage_label(), "completed/abandoned");
        assert!(report.marker_line().contains("exit=completed cancel=none drain=abandoned"));
        assert_eq!(quarantine.live(), 1, "the lingering lane is kept, not dropped");
        assert!(live.load(Ordering::SeqCst) >= 1, "its cleanup is still running");

        release.store(true, Ordering::SeqCst);
        match quarantine.wait_clear(Instant::now() + Duration::from_secs(30)) {
            QuarantineWait::Clear { joined } => assert_eq!(joined[0].0, "t-deliver-linger"),
            other => panic!("expected a clear quarantine, got {other:?}"),
        }
        assert_eq!(live.load(Ordering::SeqCst), 0, "the gate must have joined the lane");
    }

    /// The harness deadline never cuts the drain itself short: a lane whose
    /// deadline has already passed still gets the full drain limit to exit.
    #[test]
    fn a_passed_deadline_still_allows_the_drain_limit() {
        let quarantine = private_quarantine();
        let stop = Arc::new(AtomicBool::new(false));
        let observed = Arc::clone(&stop);
        let lane = OwnedLane::spawn(
            "t-drain",
            {
                let stop = Arc::clone(&stop);
                move || stop.store(true, Ordering::SeqCst)
            },
            move || {
                wait_for(&observed, Duration::from_secs(30));
                // Winds down 100 ms after the cancellation: inside the drain.
                std::thread::sleep(Duration::from_millis(100));
            },
        )
        .unwrap()
        .abandon_at(Instant::now())
        .quarantine_in(quarantine);
        let (_, report) = lane.finish_with(Duration::from_millis(10), Duration::from_secs(5));
        assert!(!report.abandoned() && !report.drain_failed(), "{report:?}");
        assert_eq!(quarantine.live(), 0);
    }

    /// Dropping an unfinished lane past its deadline quarantines it too.
    #[test]
    fn dropping_an_unfinished_lane_past_its_deadline_quarantines_it() {
        let quarantine = private_quarantine();
        let release = Arc::new(AtomicBool::new(false));
        let released = Arc::clone(&release);
        let lane = OwnedLane::spawn(
            "t-drop-wedged",
            || {},
            move || {
                wait_for(&released, Duration::from_secs(60));
            },
        )
        .unwrap()
        .abandon_at(Instant::now())
        .quarantine_in(quarantine);
        let started = Instant::now();
        drop(lane);
        assert!(started.elapsed() < LANE_DRAIN_LIMIT + Duration::from_secs(2));
        assert_eq!(quarantine.live(), 1);
        release.store(true, Ordering::SeqCst);
        assert!(matches!(
            quarantine.wait_clear(Instant::now() + Duration::from_secs(30)),
            QuarantineWait::Clear { .. }
        ));
    }

    #[test]
    fn a_panicking_lane_reports_the_panic_and_is_joined() {
        let lane: OwnedLane<u8> = OwnedLane::spawn(
            "t-panic",
            || {},
            || -> u8 {
                panic!("lane exploded");
            },
        )
        .unwrap();
        let (outcome, report) = lane.finish_with(Duration::from_secs(10), LANE_DRAIN_LIMIT);
        match outcome {
            LaneOutcome::Panicked(message) => assert!(message.contains("lane exploded")),
            other => panic!("expected a panic, got {other:?}"),
        }
        assert_eq!(report.exit, LaneExit::Panicked);
        assert!(!report.cancel_requested && !report.drain_failed());
    }

    /// Dropping an unfinished lane (early return, unwinding caller) cancels it
    /// and joins it: no path detaches.
    #[test]
    fn dropping_an_unfinished_lane_cancels_and_joins_it() {
        let live = Arc::new(AtomicUsize::new(0));
        let sentinel_live = Arc::clone(&live);
        let stop = Arc::new(AtomicBool::new(false));
        let observed = Arc::clone(&stop);
        let started = Arc::new(AtomicBool::new(false));
        let started_in_lane = Arc::clone(&started);
        let lane = OwnedLane::spawn(
            "t-drop",
            {
                let stop = Arc::clone(&stop);
                move || stop.store(true, Ordering::SeqCst)
            },
            move || {
                let _sentinel = LiveSentinel::new(&sentinel_live, Duration::ZERO);
                started_in_lane.store(true, Ordering::SeqCst);
                wait_for(&observed, Duration::from_secs(30));
            },
        )
        .unwrap();
        wait_for(&started, Duration::from_secs(10));
        drop(lane);
        assert!(stop.load(Ordering::SeqCst), "drop must request cancellation");
        assert_eq!(live.load(Ordering::SeqCst), 0, "drop must join the lane");
    }

    /// A subsequent lane sees no live work from the previous one.
    #[test]
    fn consecutive_lanes_never_overlap() {
        let live = Arc::new(AtomicUsize::new(0));
        for _ in 0..3 {
            let sentinel_live = Arc::clone(&live);
            let seen = Arc::clone(&live);
            let lane = OwnedLane::spawn(
                "t-seq",
                || {},
                move || {
                    let before = seen.load(Ordering::SeqCst);
                    let _sentinel = LiveSentinel::new(&sentinel_live, Duration::from_millis(20));
                    before
                },
            )
            .unwrap();
            let (outcome, _) = lane.finish_with(Duration::from_secs(10), LANE_DRAIN_LIMIT);
            assert!(matches!(outcome, LaneOutcome::Completed(0)));
        }
        assert_eq!(live.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn the_bmc_retry_is_refused_once_the_attempt_authority_has_closed() {
        let floor = Duration::from_secs(1);
        let s = Duration::from_secs;
        // Cancelled: never retried, whatever is left.
        assert_eq!(bmc_retry_budget(true, s(10), s(10), floor), None);
        // Lane budget spent (or below the floor): refused.
        assert_eq!(bmc_retry_budget(false, Duration::ZERO, s(10), floor), None);
        assert_eq!(bmc_retry_budget(false, Duration::from_millis(999), s(10), floor), None);
        // Harness deadline spent: refused even with lane budget left.
        assert_eq!(bmc_retry_budget(false, s(10), Duration::ZERO, floor), None);
        // Open: the REMAINING budget, the tighter of the two, never a fresh one.
        assert_eq!(bmc_retry_budget(false, s(4), s(10), floor), Some(s(4)));
        assert_eq!(bmc_retry_budget(false, s(9), s(2), floor), Some(s(2)));
    }
}
