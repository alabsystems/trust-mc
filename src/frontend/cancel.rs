// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Forwarding termination from the front door to the verification engine.
//!
//! `trust-mc` is a thin front door that execs the engine (`trust-mc-driver`)
//! as a child, which in turn spawns `ay` solver processes. The engine already
//! cleans up its own solver subtree when it is signalled: it isolates each
//! solver in a fresh process group and its SIGTERM/SIGINT handler group-kills
//! everything it tracks.
//!
//! The gap this module closes is that the engine was never *reached*. The
//! front door waited with `Command::status()` and installed no handlers, so a
//! termination aimed at the front-door PID — a CI step timeout,
//! `subprocess.terminate()`, `kill <pid>` — killed only the front door. The
//! engine was reparented to init and kept running, holding its solvers with
//! it. Observed in the wild: five orphaned `ay` pairs on one developer
//! machine, the oldest 68 minutes old, each still burning a core against a
//! build directory nobody was waiting on.
//!
//! Ctrl-C never showed the bug: the terminal delivers SIGINT to the whole
//! foreground process group, so the engine got its own copy directly. Only a
//! PID-targeted signal — exactly what automation sends — exposed it.
//!
//! # Design
//!
//! The child PID lives in an atomic. Handlers for SIGTERM/SIGINT/SIGHUP
//! forward the same signal to that PID, then restore the default disposition
//! and re-raise so the front door dies with the conventional
//! signal-terminated status. The engine's own handler does the group-killing
//! from there.
//!
//! The child is deliberately left in the front door's process group. Moving it
//! to its own group would take it out of the terminal's foreground group,
//! costing job control and risking SIGTTIN on any terminal read, and buys
//! nothing: the engine isolates its solvers into groups itself, so the kill
//! chain already reaches the whole tree.
//!
//! Under Ctrl-C the engine receives two SIGINTs — one from the terminal, one
//! forwarded. The second lands on a process already dying with the default
//! disposition restored, which is harmless.
//!
//! SIGKILL of the front door cannot be intercepted here by definition. The
//! engine covers that case from its own side with a parent-death watchdog.

use std::sync::atomic::{AtomicI32, Ordering};

/// PID of the engine child, or 0 when no child is running.
static ENGINE_PID: AtomicI32 = AtomicI32::new(0);

/// Record the engine child's PID and install the forwarding handlers.
///
/// Idempotent with respect to handler installation; the PID is updated on
/// every call.
pub(crate) fn watch_engine(pid: u32) {
    ENGINE_PID.store(pid as i32, Ordering::SeqCst);
    install();
}

/// Forget the engine child, after it has been reaped.
///
/// Prevents a later signal from being forwarded to a PID the OS may since
/// have recycled onto an unrelated process.
pub(crate) fn forget_engine() {
    ENGINE_PID.store(0, Ordering::SeqCst);
}

#[cfg(unix)]
fn install() {
    use std::sync::atomic::AtomicBool;
    static INSTALLED: AtomicBool = AtomicBool::new(false);
    if INSTALLED.swap(true, Ordering::SeqCst) {
        return;
    }

    extern "C" fn forward(sig: libc::c_int) {
        let pid = ENGINE_PID.load(Ordering::SeqCst);
        // SAFETY: `kill` is async-signal-safe. A stale or already-exited PID
        // fails with ESRCH, which is ignored. `signal`/`raise` restore the
        // default disposition so the front door reports the conventional
        // signal-terminated status rather than a plain exit code.
        unsafe {
            if pid > 0 {
                libc::kill(pid, sig);
            }
            libc::signal(sig, libc::SIG_DFL);
            libc::raise(sig);
        }
    }

    // SAFETY: `signal` with a valid handler address and these signal numbers.
    unsafe {
        let handler: libc::sighandler_t = forward as *const () as usize;
        libc::signal(libc::SIGTERM, handler);
        libc::signal(libc::SIGINT, handler);
        libc::signal(libc::SIGHUP, handler);
    }
}

#[cfg(not(unix))]
fn install() {}
