// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Subprocess tracking and cleanup for memory pressure scenarios.
//!
//! This module provides infrastructure to track active child processes and clean them up
//! when the system experiences memory pressure (OOM signals, SIGTERM, etc.).
//!
//! Part of #1086: Implement subprocess cleanup on OOM signal.
//!
//! # Design
//!
//! - `SubprocessTracker` maintains a thread-safe registry of active child process PIDs
//! - Signal handlers are installed to catch SIGTERM/SIGINT for graceful cleanup
//! - When a signal is received, all tracked subprocesses are terminated
//!
//! # Usage
//!
//! ```text
//! // Register a subprocess
//! SubprocessTracker::register(child_pid);
//!
//! // Unregister when done
//! SubprocessTracker::unregister(child_pid);
//!
//! // Or use the guard pattern
//! let _guard = SubprocessGuard::new(child_pid);
//! // Process is automatically unregistered when guard is dropped
//! ```

use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};

/// Capacity of the lock-free PID table.
///
/// Slots are released on unregister, so this bounds *concurrently live*
/// children, not children over the run. The driver's solver fan-out is
/// bounded by harness count times lane count, orders of magnitude below this.
const PID_SLOTS: usize = 1024;

/// A free slot. Named so the array initializer below stays a const expression
/// (`AtomicU32` is not `Copy`, so `[AtomicU32::new(0); N]` will not compile).
#[allow(clippy::declare_interior_mutable_const)]
const FREE: AtomicU32 = AtomicU32::new(0);

/// Global registry of active subprocess PIDs, as a fixed lock-free table.
///
/// Deliberately NOT a `Mutex<HashSet>`. `cleanup_all` runs from a signal
/// handler, where taking a mutex is not async-signal-safe: the handler can
/// interrupt a thread that already holds the lock, and blocking there
/// deadlocks the process. The previous code avoided the deadlock with
/// `try_lock` — but that traded it for a silent total failure, because losing
/// the race meant returning having killed *nothing*, exactly when cleanup
/// mattered most. Under a corpus run the registry is written constantly, so
/// that race was not hypothetical.
///
/// Plain atomics have no such failure mode: the handler always sees a
/// consistent view and always kills what is there. PID 0 marks a free slot,
/// which is safe because no child is ever pid 0.
static SLOTS: [AtomicU32; PID_SLOTS] = [FREE; PID_SLOTS];

/// Flag indicating whether signal handlers have been installed.
static HANDLERS_INSTALLED: AtomicBool = AtomicBool::new(false);

/// Flag indicating cleanup is in progress (prevents recursive cleanup).
static CLEANUP_IN_PROGRESS: AtomicBool = AtomicBool::new(false);

/// Subprocess tracker for managing active child processes.
///
/// Provides static methods to register and track child processes, enabling cleanup
/// when the parent receives termination signals or OOM conditions.
pub(crate) struct SubprocessTracker;

impl SubprocessTracker {
    /// Register a child process PID for tracking.
    ///
    /// The PID will be tracked until explicitly unregistered or until
    /// `cleanup_all` is called (e.g., on signal).
    pub(crate) fn register(pid: u32) {
        // Ensure signal handlers are installed on first registration
        Self::install_handlers();

        if pid == 0 {
            return;
        }
        for slot in SLOTS.iter() {
            if slot.compare_exchange(0, pid, Ordering::SeqCst, Ordering::Relaxed).is_ok() {
                return;
            }
        }
        // Table full: the child runs untracked rather than silently displacing
        // another entry. Loud, because it means cleanup can now leak.
        crate::raw_io::write_stderr_parts(&[
            b"[trust_mc] subprocess table full; a child will not be tracked for cleanup\n",
        ]);
    }

    /// Unregister a child process PID.
    ///
    /// Call this when a child process has completed normally.
    pub(crate) fn unregister(pid: u32) {
        if pid == 0 {
            return;
        }
        for slot in SLOTS.iter() {
            if slot.compare_exchange(pid, 0, Ordering::SeqCst, Ordering::Relaxed).is_ok() {
                return;
            }
        }
    }

    /// Whether `pid` is currently tracked. Test helper.
    #[cfg(test)]
    pub(crate) fn is_tracked(pid: u32) -> bool {
        SLOTS.iter().any(|s| s.load(Ordering::SeqCst) == pid)
    }

    /// Clean up all tracked subprocesses by sending SIGKILL.
    ///
    /// This is called from signal handlers when memory pressure or termination
    /// signals are received, and from the wall-clock watchdog fire path. All
    /// tracked processes are killed immediately.
    ///
    /// Must stay lock-free w.r.t. Rust stdio and allocation-free on the
    /// message path: both callers (signal handler, watchdog firing into a
    /// presumed-hung process) cannot safely take the stdout/stderr locks.
    ///
    /// # Safety
    ///
    /// Uses SIGKILL which cannot be caught or ignored, ensuring immediate termination.
    pub(crate) fn cleanup_all() {
        // Prevent recursive cleanup
        if CLEANUP_IN_PROGRESS.swap(true, Ordering::SeqCst) {
            return;
        }

        // Claim every occupied slot with an atomic swap. No lock is taken, so
        // unlike the previous `try_lock` this can never bail out having killed
        // nothing; and swapping (rather than reading) means a concurrent
        // cleanup cannot double-kill a PID the OS may have already recycled.
        let mut pids = [0u32; PID_SLOTS];
        let mut n = 0usize;
        for slot in SLOTS.iter() {
            let pid = slot.swap(0, Ordering::SeqCst);
            if pid != 0 {
                pids[n] = pid;
                n += 1;
            }
        }
        let pids = &pids[..n];

        if !pids.is_empty() {
            // Raw write — eprintln! would take the stderr lock, which is
            // not safe from a signal handler or the watchdog fire path.
            let mut digits = [0u8; 20];
            let count = crate::raw_io::u64_decimal(pids.len() as u64, &mut digits);
            crate::raw_io::write_stderr_parts(&[
                b"[trust_mc] Memory pressure cleanup: terminating ",
                count,
                b" subprocess(es)\n",
            ]);
        }

        for pid in pids {
            Self::kill_process(*pid);
        }

        // No registry clear needed: the swap above already emptied every slot.

        CLEANUP_IN_PROGRESS.store(false, Ordering::SeqCst);
    }

    /// Kill a single process by PID (group-aware, see [`kill_pid_or_group`]).
    fn kill_process(pid: u32) {
        kill_pid_or_group(pid);
    }

    /// Install signal handlers for graceful cleanup.
    ///
    /// Handlers are installed for:
    /// - SIGTERM: System termination request (often from memory pressure)
    /// - SIGINT: User interrupt (Ctrl+C)
    fn install_handlers() {
        // Only install once
        if HANDLERS_INSTALLED.swap(true, Ordering::SeqCst) {
            return;
        }

        #[cfg(unix)]
        Self::install_unix_handlers();
    }

    #[cfg(unix)]
    fn install_unix_handlers() {
        // Signal handler that cleans up subprocesses
        extern "C" fn signal_handler(sig: libc::c_int) {
            // Clean up all tracked subprocesses
            SubprocessTracker::cleanup_all();

            // Re-raise the signal with default handler for proper exit behavior
            // SAFETY: signal() and raise() are safe system calls
            unsafe {
                libc::signal(sig, libc::SIG_DFL);
                libc::raise(sig);
            }
        }

        // SAFETY: signal() is safe to call with valid signal numbers
        unsafe {
            let handler: libc::sighandler_t = signal_handler as *const () as usize;

            // Install handler for SIGTERM (common for OOM killer and system shutdown)
            libc::signal(libc::SIGTERM, handler);

            // Install handler for SIGHUP. The front door forwards SIGHUP, and
            // without a handler here the default disposition kills the driver
            // *without* running cleanup, orphaning the solver subtree — the
            // exact leak this module exists to prevent. Installing a handler
            // also overrides an inherited SIG_IGN (e.g. under `nohup`), which
            // would otherwise make the driver ignore the forwarded signal and
            // survive as an orphan.
            libc::signal(libc::SIGHUP, handler);

            // Install handler for SIGINT (Ctrl+C)
            libc::signal(libc::SIGINT, handler);

            // Note: We don't install for SIGKILL (can't be caught) or SIGQUIT (let it dump core)
        }
    }
}

/// SIGKILL a child process, escalating to its whole process group when the
/// child is a process-group leader.
///
/// `session::process` spawns timeout-guarded children with
/// `Command::process_group(0)`, making each child the leader of a fresh
/// group. Killing only the single PID would leak grandchildren (e.g. rustc
/// processes spawned by cargo, or solver helpers): they survive the parent
/// kill, keep the suite's pipes open, and keep burning CPU until the
/// shell-level process-group SIGKILL. Sending the signal to `-pid` reaps
/// the entire tree in that case.
///
/// For PIDs that are NOT group leaders (spawned without `process_group`),
/// this falls back to the single-PID kill — signalling `-pid` there would
/// hit OUR OWN process group, including the driver itself.
///
/// Async-signal-safety: only raw `getpgid`/`kill` syscalls; safe from the
/// SIGTERM/SIGINT handler and the watchdog fire path.
pub(crate) fn kill_pid_or_group(pid: u32) {
    #[cfg(unix)]
    {
        let pid = pid as i32;
        // SAFETY: getpgid/kill are raw syscalls, valid for any pid value;
        // SIGKILL cannot be caught. Worst case the pid is already gone and
        // the calls fail with ESRCH, which we ignore.
        unsafe {
            if libc::getpgid(pid) == pid {
                // Child is a group leader: kill the whole group.
                libc::kill(-pid, libc::SIGKILL);
            } else {
                libc::kill(pid, libc::SIGKILL);
            }
        }
    }
    #[cfg(not(unix))]
    {
        // No-op on non-Unix platforms
        // Windows would need different handling via TerminateProcess
        let _ = pid;
    }
}

/// RAII guard that automatically unregisters a subprocess when dropped.
///
/// Use this to ensure subprocesses are properly unregistered even if the
/// code panics or returns early via `bail!()`.
///
/// # Example
///
/// ```text
/// let child = cmd.spawn()?;
/// let _guard = SubprocessGuard::new(child.id());
/// // ... child is tracked until guard drops
/// ```
pub(crate) struct SubprocessGuard {
    pid: u32,
}

impl SubprocessGuard {
    /// Register and track a child process PID. The PID is automatically
    /// unregistered when this guard is dropped.
    pub(crate) fn new(pid: u32) -> Self {
        SubprocessTracker::register(pid);
        Self { pid }
    }
}

impl Drop for SubprocessGuard {
    fn drop(&mut self) {
        SubprocessTracker::unregister(self.pid);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_unregister() {
        let pid = 12345;
        SubprocessTracker::register(pid);
        assert!(SubprocessTracker::is_tracked(pid));

        SubprocessTracker::unregister(pid);
        assert!(!SubprocessTracker::is_tracked(pid));
    }

    #[test]
    fn test_guard_pattern() {
        let pid = 12346;
        {
            let _guard = SubprocessGuard::new(pid);
            assert!(SubprocessTracker::is_tracked(pid));
        }
        // Guard dropped, PID should be unregistered
        assert!(!SubprocessTracker::is_tracked(pid));
    }

    #[test]
    fn test_multiple_register_unregister() {
        // Use unique PIDs that won't collide with other tests
        let pid1 = 99991;
        let pid2 = 99992;

        // Clean up any leftover state from previous test runs
        SubprocessTracker::unregister(pid1);
        SubprocessTracker::unregister(pid2);

        SubprocessTracker::register(pid1);
        SubprocessTracker::register(pid2);

        // Verify both PIDs are tracked (membership, not count — parallel tests share the table)
        assert!(SubprocessTracker::is_tracked(pid1));
        assert!(SubprocessTracker::is_tracked(pid2));

        SubprocessTracker::unregister(pid1);
        SubprocessTracker::unregister(pid2);

        // Verify PIDs are no longer tracked
        assert!(!SubprocessTracker::is_tracked(pid1));
        assert!(!SubprocessTracker::is_tracked(pid2));
    }
}

/// Environment variable that disables the parent-death watchdog.
///
/// Set this when the driver is intentionally run detached and is expected to
/// outlive whatever launched it.
pub(crate) const NO_PARENT_WATCH: &str = "TRUST_MC_NO_PARENT_WATCH";

/// Terminate the solver subtree if the process that launched us dies.
///
/// Signal forwarding from the front door covers the catchable signals, but
/// SIGKILL cannot be caught, and a front door that dies by panic, crash, or
/// `kill -9` leaves no opportunity to forward anything. In every one of those
/// cases the driver is reparented to init and keeps its solvers running
/// against a build directory nobody is waiting on. Five such orphaned `ay`
/// pairs were found on a single developer machine, the oldest 68 minutes old,
/// which is also enough background CPU load to skew the very timing
/// measurements the suite depends on.
///
/// The watchdog compares the current parent against the one recorded at
/// startup. Reparenting is one-way and unambiguous: once the launching parent
/// exits, `getppid` changes and never changes back.
///
/// Deliberately a no-op when the initial parent is already init (pid 1). A
/// driver started detached — `nohup`, a daemon supervisor, an orphaned CI
/// shell — has no launching parent to outlive, and treating that as a death
/// would kill legitimate runs at startup.
pub(crate) fn watch_parent_death() {
    #[cfg(unix)]
    {
        // SAFETY: getppid takes no arguments and cannot fail.
        let initial = unsafe { libc::getppid() };
        if !should_watch_parent(initial, std::env::var_os(NO_PARENT_WATCH).is_some()) {
            return;
        }

        std::thread::spawn(move || {
            loop {
                std::thread::sleep(std::time::Duration::from_millis(500));
                // SAFETY: as above.
                let current = unsafe { libc::getppid() };
                if current != initial {
                    crate::raw_io::write_stderr_parts(&[
                        b"[trust_mc] parent process exited; terminating solver subprocesses\n",
                    ]);
                    SubprocessTracker::cleanup_all();
                    // 128 + SIGTERM: the conventional status for a run ended by
                    // termination, which is what a cancelled CI step expects.
                    std::process::exit(143);
                }
            }
        });
    }
}

/// Whether the parent-death watchdog should run, given the parent recorded at
/// startup and whether the opt-out is set.
///
/// Split out from [`watch_parent_death`] so the two guards can be tested
/// without spawning processes. Both guards exist to prevent a false positive
/// that would kill a legitimate run:
///
/// * `opted_out` is the explicit escape hatch for intentionally detached runs.
/// * `initial_ppid <= 1` means we were *started* with no launching parent —
///   already reparented to init, or started by init. There is nothing to
///   outlive, and treating that as a parent death would abort at startup.
fn should_watch_parent(initial_ppid: i32, opted_out: bool) -> bool {
    !opted_out && initial_ppid > 1
}

#[cfg(test)]
mod parent_watch_tests {
    use super::should_watch_parent;

    #[test]
    fn watches_a_normal_launching_parent() {
        assert!(should_watch_parent(4321, false));
    }

    #[test]
    fn the_opt_out_disables_the_watchdog() {
        assert!(!should_watch_parent(4321, true));
    }

    #[test]
    fn a_process_started_detached_has_no_parent_to_outlive() {
        // Reparented to (or started by) init: `getppid` is already 1, so a
        // later change cannot signal that our launcher died.
        assert!(!should_watch_parent(1, false));
        assert!(!should_watch_parent(0, false));
    }
}
