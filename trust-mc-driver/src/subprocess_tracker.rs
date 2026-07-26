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

use std::collections::HashSet;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};

use once_cell::sync::Lazy;

/// Global registry of active subprocess PIDs.
static TRACKED_PIDS: Lazy<Mutex<HashSet<u32>>> = Lazy::new(|| Mutex::new(HashSet::new()));

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

        if let Ok(mut pids) = TRACKED_PIDS.lock() {
            pids.insert(pid);
        }
    }

    /// Unregister a child process PID.
    ///
    /// Call this when a child process has completed normally.
    pub(crate) fn unregister(pid: u32) {
        if let Ok(mut pids) = TRACKED_PIDS.lock() {
            pids.remove(&pid);
        }
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

        // Use try_lock to be async-signal-safe: if the mutex is already held
        // (e.g., signal arrived during register/unregister), we cannot safely
        // acquire it. In that case, skip cleanup rather than deadlock.
        // Part of #2137 F2: signal handler must not call Mutex::lock().
        let pids: Vec<u32> = match TRACKED_PIDS.try_lock() {
            Ok(pids) => pids.iter().copied().collect(),
            Err(_) => {
                // Mutex held — cannot safely enumerate PIDs from signal context.
                // Reset flag and return; the holder will complete normally.
                CLEANUP_IN_PROGRESS.store(false, Ordering::SeqCst);
                return;
            }
        };

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
            Self::kill_process(pid);
        }

        // Clear the registry (also try_lock for signal safety)
        if let Ok(mut pids) = TRACKED_PIDS.try_lock() {
            pids.clear();
        }

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
        assert!(TRACKED_PIDS.lock().unwrap().contains(&pid));

        SubprocessTracker::unregister(pid);
        assert!(!TRACKED_PIDS.lock().unwrap().contains(&pid));
    }

    #[test]
    fn test_guard_pattern() {
        let pid = 12346;
        {
            let _guard = SubprocessGuard::new(pid);
            assert!(TRACKED_PIDS.lock().unwrap().contains(&pid));
        }
        // Guard dropped, PID should be unregistered
        assert!(!TRACKED_PIDS.lock().unwrap().contains(&pid));
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

        // Verify both PIDs are tracked (membership, not count — parallel tests share TRACKED_PIDS)
        assert!(TRACKED_PIDS.lock().unwrap().contains(&pid1));
        assert!(TRACKED_PIDS.lock().unwrap().contains(&pid2));

        SubprocessTracker::unregister(pid1);
        SubprocessTracker::unregister(pid2);

        // Verify PIDs are no longer tracked
        assert!(!TRACKED_PIDS.lock().unwrap().contains(&pid1));
        assert!(!TRACKED_PIDS.lock().unwrap().contains(&pid2));
    }
}
