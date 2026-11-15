// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The native lanes' HARD wall-clock ceiling, and the cancellation it sends a
//! solve it stops (decision NATIVE-SOLVE-CANCEL, `docs/DECISION_QUEUE.md`).
//!
//! The ay solver does not honor its internal budget during every phase —
//! notably bit-blasting the 128-bit BV multiplies of a mul/div-heavy function —
//! so a hard obligation can spin far past its deadline (a real 23h orca-core
//! survey hang, 2026-06-13). [`run_native_solve_within_deadline`] runs the work
//! on a worker thread and `recv_timeout`s it. Until 2026-11-01 an expired
//! watchdog walked away from the worker without telling it anything ("it exits
//! at process end"), and in one long `trustc` (thousands of functions in one
//! crate) the abandoned PDR workers kept spinning: on Trust main before
//! 2026-11-01 they held 87% of the running samples, 82 distinct workers, one of
//! them alive 510 minutes. Now every call creates an [`ay_chc::CancellationToken`],
//! hands it to the work, and cancels it whenever the call returns without the
//! work's result: the deadline expired, the worker died, or the caller is
//! unwinding.
//!
//! Cancellation is cooperative: Rust cannot stop a thread, so the worker is
//! still detached, and it stops only where the work polls the token. The
//! direct-SMT decision polls it between SMT checks, the IC3 loop lane between
//! its steps and in its explicit re-validation (`PdrConfig::cancellation_token`),
//! the PdrInvariant replay seal in its clause check, and the diagnostic
//! portfolio probe through `solve_with_cancellation`; the SMT-LIB BMC executor
//! gets an interrupt flag of its own, set on expiry. Those lanes have no
//! overall deadline that ends with the watchdog (the direct-SMT decision has
//! only a per-query budget, the IC3 lane gives each of its three steps the
//! full timeout, the BMC executor has no budget unless its script sets one),
//! so the cancellation is what stops them. The strict PDR proof run takes no
//! token: its own solve deadline already stops it 2 s inside the watchdog's
//! wherever a token could, and ay's only way to link one skips its case-split
//! stage (the call site and the decision entry have the measurement). The
//! phases that observe neither a token nor a deadline are listed in the
//! decision entry; this change is not the fix for the concrete enumeration
//! behind the 87%, which polls neither (ay's own change). A solve the watchdog
//! stops is `None`, which every caller maps to an `Unknown` verdict, exactly
//! as before the token existed: SOUND, because a timed-out solve is undecided,
//! never a false proof. A result the worker
//! produces after the deadline is never received, and the receiving end is
//! dropped on return, so nothing a cancelled solve computes is ever used.

use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use ay_chc::CancellationToken;

/// Cancels `token` when dropped, unless the call that owns it received the
/// work's result in time ([`Self::disarm`]). Being a guard, it also cancels
/// when the owning call unwinds.
struct CancelUnlessDelivered {
    token: CancellationToken,
    delivered: bool,
}

impl CancelUnlessDelivered {
    fn disarm(&mut self) {
        self.delivered = true;
    }
}

impl Drop for CancelUnlessDelivered {
    fn drop(&mut self) {
        if !self.delivered {
            self.token.cancel();
        }
    }
}

/// Run `work` on a worker thread under a HARD wall-clock ceiling of `deadline`.
///
/// `work` receives a fresh [`CancellationToken`] that nothing else holds. The
/// call returns `Some` of the work's result when the result arrives within
/// `deadline`; the token is then left uncancelled. Otherwise — the deadline
/// expired, or the worker panicked before sending — the call cancels the token
/// and returns `None`. Callers map `None` to an `Unknown` verdict. The worker
/// is not joined: it ends where the work next polls the token, and a result it
/// sends after the deadline goes to a receiver that no longer exists.
///
/// A token is only ever cancelled after the call has stopped receiving, so a
/// result this call returns was produced by work that was never cancelled.
pub(crate) fn run_native_solve_within_deadline<T, F>(deadline: Duration, work: F) -> Option<T>
where
    F: FnOnce(CancellationToken) -> T + Send + 'static,
    T: Send + 'static,
{
    let token = CancellationToken::new();
    let mut guard = CancelUnlessDelivered { token: token.clone(), delivered: false };
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let _ = tx.send(work(token));
    });
    let delivered = rx.recv_timeout(deadline).ok();
    if delivered.is_some() {
        guard.disarm();
    }
    delivered
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    /// How long a worker that polls its token may take to notice the
    /// cancellation. Generous: the host runs at load 60-120 during gates, and
    /// the work below polls every millisecond.
    const NOTICE_BOUND: Duration = Duration::from_secs(10);

    /// The longest a test worker spins without a cancellation before it gives
    /// up and reports that none came, so a broken watchdog fails the test
    /// instead of leaving a thread spinning for the rest of the test process.
    const SPIN_CAP: Duration = Duration::from_secs(30);

    /// Spin, polling `token`, until it is cancelled or [`SPIN_CAP`] passes.
    /// Returns whether the cancellation came.
    fn spin_until_cancelled(token: &CancellationToken) -> bool {
        let started = Instant::now();
        while !token.is_cancelled() {
            if started.elapsed() >= SPIN_CAP {
                return false;
            }
            thread::sleep(Duration::from_millis(1));
        }
        true
    }

    #[test]
    fn an_expired_watchdog_cancels_its_worker_and_the_worker_exits() {
        // The side channel reports how the worker ended, sent as the worker's
        // LAST act, so receiving it means the work has returned.
        let (exit_tx, exit_rx) = mpsc::channel();
        let deadline = Duration::from_millis(50);
        let started = Instant::now();
        let outcome = run_native_solve_within_deadline(deadline, move |token| {
            let cancelled = spin_until_cancelled(&token);
            let _ = exit_tx.send(cancelled);
            "a value the watchdog must never return"
        });
        assert_eq!(outcome, None, "an expired watchdog returns no result");
        assert!(started.elapsed() >= deadline, "the watchdog waited its full deadline");
        let cancelled = exit_rx
            .recv_timeout(NOTICE_BOUND)
            .expect("the worker exits within the bound after the deadline");
        assert!(cancelled, "the worker ended because its token was cancelled, not at its spin cap");
    }

    #[test]
    fn a_result_sent_after_the_deadline_is_never_returned() {
        // The worker answers only once its token is cancelled — the late
        // result of a cancelled solve. The watchdog must not hand it out, and
        // the worker's send must find the receiver gone.
        let (send_tx, send_rx) = mpsc::channel();
        let outcome = run_native_solve_within_deadline(Duration::from_millis(20), move |token| {
            let cancelled = spin_until_cancelled(&token);
            let _ = send_tx.send(cancelled);
            42_u32
        });
        assert_eq!(outcome, None, "a result produced after the deadline is not used");
        assert_eq!(
            send_rx.recv_timeout(NOTICE_BOUND),
            Ok(true),
            "the late result was produced after the cancellation"
        );
    }

    #[test]
    fn a_late_result_is_dropped_even_when_the_worker_ignores_its_token() {
        // A worker that never polls the token (an ay phase that cannot observe
        // it) still cannot deliver past the deadline.
        let (done_tx, done_rx) = mpsc::channel();
        let outcome = run_native_solve_within_deadline(Duration::from_millis(20), move |_token| {
            thread::sleep(Duration::from_millis(200));
            let _ = done_tx.send(());
            7_u32
        });
        assert_eq!(outcome, None);
        done_rx.recv_timeout(NOTICE_BOUND).expect("the worker finished its late work");
    }

    #[test]
    fn a_fast_result_is_returned_and_its_token_is_not_cancelled() {
        let (token_tx, token_rx) = mpsc::channel();
        let outcome = run_native_solve_within_deadline(Duration::from_secs(60), move |token| {
            let _ = token_tx.send(token);
            7_u32
        });
        assert_eq!(outcome, Some(7), "a result inside the deadline is returned");
        let token = token_rx.recv_timeout(NOTICE_BOUND).expect("the work ran");
        assert!(!token.is_cancelled(), "a delivered solve is not cancelled");
    }

    #[test]
    fn a_worker_that_panics_has_its_token_cancelled_and_yields_none() {
        let (token_tx, token_rx) = mpsc::channel();
        let outcome =
            run_native_solve_within_deadline::<(), _>(Duration::from_secs(60), move |token| {
                let _ = token_tx.send(token);
                panic!("deliberate test panic: the solve died before answering");
            });
        assert_eq!(outcome, None, "a dead worker is undecided");
        let token = token_rx.recv_timeout(NOTICE_BOUND).expect("the work ran");
        assert!(token.is_cancelled(), "no early return leaves the token live");
    }
}
