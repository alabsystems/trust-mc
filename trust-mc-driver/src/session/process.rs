// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Process execution with timeout protection.
//!
//! Contains all `run_*` and `wait_*` free functions for subprocess management.
//! These functions take `Command` arguments, not `KaniSession` — the session
//! wrapper methods that delegate here live in the parent `session/mod.rs`.
//!
//! Part of #995: Unified timeout protection.
//! Part of #1086: Subprocess tracking for OOM cleanup.
//! Part of #1092: Memory pressure warnings.

use super::memory::check_memory_pressure;
use crate::args::common::Verbosity;
use crate::util::render_command;
use anyhow::{Context, Result, bail};
use std::process::{Child, Command, Output, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

/// Default timeout for tool processes (10 minutes).
/// This prevents runaway tool processes from running indefinitely.
/// Can be overridden with --tool-timeout.
pub(crate) const DEFAULT_TOOL_TIMEOUT_SECS: u64 = 600;

/// Headroom a subprocess budget keeps under the watchdog's fire time, so
/// the kill, the reap and the caller's reporting of the timeout all happen
/// BEFORE the watchdog hard-exits the process rather than racing it.
const SPAWN_HEADROOM: Duration = Duration::from_secs(1);

/// Stable phrase in the error a refused spawn returns, so callers can file
/// it as `SolverUnknownReason::BudgetExhausted` (`call_ay::
/// solver_error_is_budget_exhausted`). The message also keeps the
/// `timed out after` wording every timeout error carries, so consumers that
/// grep for it (`tools/kani-domination`) read the refusal as a timeout, not
/// a crash.
pub(crate) const BUDGET_EXHAUSTED_BEFORE_SPAWN: &str =
    "not spawned: driver wall-clock budget exhausted";

/// Clamp a subprocess timeout to the wall-clock watchdog's remaining
/// budget: `min(tool_timeout, watchdog_remaining - SPAWN_HEADROOM)`.
///
/// Every timeout-guarded subprocess (compiler, cargo, ay solver) flows
/// through this chokepoint, so no child can be granted a budget extending
/// past the watchdog's planned fire time. A hung child then surfaces as an
/// ordinary subprocess-timeout error (clean UNKNOWN/error reporting)
/// instead of requiring the watchdog's hard `_exit`. When the watchdog is
/// unarmed (no `--harness-timeout` anywhere), the timeout is unchanged.
///
/// An exhausted budget — nothing left under the headroom, or a caller
/// asking for zero — REFUSES the spawn with a typed error instead of
/// starting a child only to kill it: fail-closed, never an unbounded wait,
/// and never a process whose only possible outcome is its own kill.
fn clamp_to_watchdog_deadline(timeout: Duration, program: &str) -> Result<Duration> {
    match clamp_with_remaining(timeout, crate::wall_clock_watchdog::remaining()) {
        Some(timeout) => Ok(timeout),
        None => bail!(
            "{program} {BUDGET_EXHAUSTED_BEFORE_SPAWN}, timed out after 0.0s. \
             Use --tool-timeout to increase the limit."
        ),
    }
}

/// The arithmetic of [`clamp_to_watchdog_deadline`], pure for testing:
/// `None` means "do not spawn".
fn clamp_with_remaining(
    timeout: Duration,
    watchdog_remaining: Option<Duration>,
) -> Option<Duration> {
    let timeout = match watchdog_remaining {
        Some(remaining) => timeout.min(remaining.saturating_sub(SPAWN_HEADROOM)),
        None => timeout,
    };
    if timeout.is_zero() { None } else { Some(timeout) }
}

/// Make the child the leader of a fresh process group so a timeout kill
/// can reap its whole tree (see `subprocess_tracker::kill_pid_or_group`).
/// Only applied to timeout-guarded spawns: untimed terminal-mode children
/// keep the driver's group so terminal job control behaves as before.
#[cfg(unix)]
fn isolate_in_process_group(cmd: &mut Command) {
    use std::os::unix::process::CommandExt;
    cmd.process_group(0);
}

#[cfg(not(unix))]
fn isolate_in_process_group(_cmd: &mut Command) {}

/// SIGKILL the child when the thread that spawned it exits (Linux
/// `PR_SET_PDEATHSIG`).
///
/// A timeout-guarded child leads its OWN process group (see
/// [`isolate_in_process_group`]), so a SIGKILL of this driver's group -- the
/// loop-contract retry parent's timeout (`subprocess_tracker::
/// kill_pid_or_group` signals `-pid`), an outer runner's `killpg` (the dual
/// gate, the corpus runner) -- never reached it, and SIGKILL runs no handler
/// that could forward it. Measured 2026-10-01 on the CHC lane's external `ay`
/// fallback: after its driver's group was SIGKILLed the fallback was
/// reparented and still solving 120 s later at 1.6 GB RSS. With the death
/// signal armed the kernel kills the child the moment its spawner dies.
///
/// The signal follows the spawning THREAD, not the process. Every spawn here
/// is synchronous: the spawning thread blocks until the child is reaped (or,
/// after a timeout kill, for the reap limit), so the thread outlives the child
/// in every path except the one this guards against. A parent that died
/// between `fork` and `prctl` would never deliver the signal, so the child
/// checks for that and refuses to start.
#[cfg(target_os = "linux")]
fn die_with_spawning_thread(cmd: &mut Command) {
    use std::os::unix::process::CommandExt;
    // SAFETY: getpid takes no arguments and cannot fail.
    let parent = unsafe { libc::getpid() };
    // SAFETY: the closure runs in the child between fork and exec and calls
    // only async-signal-safe functions (prctl, getppid); it allocates nothing
    // on the success path.
    unsafe {
        cmd.pre_exec(move || {
            if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL as libc::c_ulong, 0, 0, 0) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            if libc::getppid() != parent {
                return Err(std::io::Error::from_raw_os_error(libc::ESRCH));
            }
            Ok(())
        });
    }
}

/// No `PR_SET_PDEATHSIG` here: a timed-out child still gets SIGTERM first
/// ([`stop_timed_out_group_leader`]), and every solver this driver starts
/// carries its own time limit, which bounds an orphan's life instead.
#[cfg(not(target_os = "linux"))]
fn die_with_spawning_thread(_cmd: &mut Command) {}

/// How long a timed-out child gets to exit on SIGTERM before its group is
/// SIGKILLed. A trust-mc driver child (the loop-contract retry lane) runs its
/// SIGTERM handler, which SIGKILLs every solver group it tracks
/// (`SubprocessTracker::cleanup_all`): the cleanup a bare SIGKILL skips, and
/// the only one a host without `PR_SET_PDEATHSIG` has. Short against the
/// watchdog headroom (`SPAWN_HEADROOM`) the budget already keeps.
const TERM_GRACE: Duration = Duration::from_millis(250);

/// Stop a timed-out child that leads its own process group: SIGTERM the group,
/// give it [`TERM_GRACE`] to exit, then SIGKILL the group and reap the leader.
/// When the leader exits within the grace its group is still swept with
/// SIGKILL, so a member that ignored SIGTERM cannot outlive the call.
fn stop_timed_out_group_leader<T>(
    program: &str,
    pid: u32,
    rx: &mpsc::Receiver<T>,
    reaper: std::thread::JoinHandle<()>,
) {
    crate::subprocess_tracker::terminate_group_leader(pid);
    match rx.recv_timeout(TERM_GRACE) {
        Ok(_) | Err(mpsc::RecvTimeoutError::Disconnected) => {
            let _ = reaper.join();
            crate::subprocess_tracker::kill_group_of_reaped_leader(pid);
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            crate::subprocess_tracker::kill_pid_or_group(pid);
            reap_killed_child(program, rx, reaper);
        }
    }
}

/// Process output strategy used by the unified execution engine.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RunMode {
    Terminal,
    Suppress,
    Piped,
}

/// Timeout policy passed to process execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct RunLimits {
    pub(crate) timeout: Option<Duration>,
}

impl RunLimits {
    pub(crate) const fn no_limits() -> Self {
        Self { timeout: None }
    }

    pub(crate) const fn timeout_only(timeout: Option<Duration>) -> Self {
        Self { timeout }
    }

    pub(crate) const fn default_tool_timeout() -> Self {
        Self { timeout: Some(Duration::from_secs(DEFAULT_TOOL_TIMEOUT_SECS)) }
    }
}

enum CommandResult {
    Completed,
    Child(Child),
}

pub(crate) fn execute_with_limits(
    verbosity: &impl Verbosity,
    cmd: Command,
    mode: RunMode,
    limits: RunLimits,
) -> Result<Option<Child>> {
    match execute_with_mode(verbosity, cmd, mode, limits)? {
        CommandResult::Completed => Ok(None),
        CommandResult::Child(child) => Ok(Some(child)),
    }
}
fn flush_failed_output(output: &Output) -> Result<()> {
    let stdout = std::io::stdout();
    let mut handle = stdout.lock();
    std::io::Write::write_all(&mut handle, &output.stdout)?;
    std::io::Write::write_all(&mut handle, &output.stderr)?;
    Ok(())
}

fn execute_with_mode(
    verbosity: &impl Verbosity,
    mut cmd: Command,
    mode: RunMode,
    limits: RunLimits,
) -> Result<CommandResult> {
    let mode = if mode == RunMode::Suppress && verbosity.is_set() {
        // Keep legacy behavior: explicit quiet/verbose routes suppress mode to terminal policy.
        RunMode::Terminal
    } else {
        mode
    };

    // Timeout helpers perform their own memory-pressure check before spawning.
    if limits.timeout.is_none() || mode == RunMode::Piped {
        check_memory_pressure();
    }

    if verbosity.verbose() {
        println!("[trust_mc] Running: `{}`", render_command(&cmd).to_string_lossy());
    }

    if mode == RunMode::Terminal && verbosity.quiet() {
        cmd.stdout(Stdio::null());
        cmd.stderr(Stdio::null());
    }

    match (mode, limits.timeout) {
        (RunMode::Terminal, Some(timeout)) => {
            let status = command_with_timeout_terminal(cmd, timeout)?;
            if !status.success() {
                bail!("Process exited with status {}", status);
            }
            Ok(CommandResult::Completed)
        }
        (RunMode::Terminal, None) => {
            let program = cmd.get_program().to_string_lossy().to_string();
            let status = with_timer(
                verbosity,
                || {
                    let mut child = cmd.spawn().context(format!(
                        "Failed to invoke {}",
                        cmd.get_program().to_string_lossy()
                    ))?;
                    let child_pid = child.id();
                    crate::subprocess_tracker::SubprocessTracker::register(child_pid);
                    let wait_result = child.wait().context(format!(
                        "Failed to wait for {}",
                        cmd.get_program().to_string_lossy()
                    ));
                    crate::subprocess_tracker::SubprocessTracker::unregister(child_pid);
                    wait_result
                },
                &program,
            )?;
            if !status.success() {
                bail!("{} exited with status {}", cmd.get_program().to_string_lossy(), status);
            }
            Ok(CommandResult::Completed)
        }
        (RunMode::Suppress, Some(timeout)) => {
            let output = run_piped_with_timeout(cmd, timeout)?;
            if !output.status.success() {
                flush_failed_output(&output)?;
                bail!("Process exited with status {}", output.status);
            }
            Ok(CommandResult::Completed)
        }
        (RunMode::Suppress, None) => {
            let child = cmd
                .spawn()
                .context(format!("Failed to invoke {}", cmd.get_program().to_string_lossy()))?;
            let child_pid = child.id();
            crate::subprocess_tracker::SubprocessTracker::register(child_pid);
            let wait_result = child.wait_with_output();
            crate::subprocess_tracker::SubprocessTracker::unregister(child_pid);
            let output = wait_result?;
            if !output.status.success() {
                flush_failed_output(&output)?;
                bail!(
                    "{} exited with status {}",
                    cmd.get_program().to_string_lossy(),
                    output.status
                );
            }
            Ok(CommandResult::Completed)
        }
        (RunMode::Piped, Some(_)) => {
            bail!("Timeout is unsupported when spawning a piped child process")
        }
        (RunMode::Piped, None) => {
            let child = cmd
                .stdout(Stdio::piped())
                .spawn()
                .context(format!("Failed to invoke {}", cmd.get_program().to_string_lossy()))?;
            crate::subprocess_tracker::SubprocessTracker::register(child.id());
            Ok(CommandResult::Child(child))
        }
    }
}

// The below suite of helper functions for executing Commands are meant to be a common handler
// for various cmdline flags like 'verbose' and 'quiet'. These functions are temporary: in the
// longer run we'll switch to a graph-interpreter style of constructing and executing jobs.
// (In other words: higher-level data structures, rather than passing around Commands.)
// (e.g. to support emitting Litani build graphs, or to better parallelize our work)

/// Run a job with timeout protection (standalone version).
///
/// Similar to `run_terminal` but with timeout to prevent runaway processes.
/// Uses default tool timeout. Part of #995.
pub(crate) fn run_terminal_with_default_timeout(
    verbosity: &impl Verbosity,
    cmd: Command,
) -> Result<()> {
    let result =
        execute_with_limits(verbosity, cmd, RunMode::Terminal, RunLimits::default_tool_timeout())?;
    match result {
        None => Ok(()),
        Some(_) => bail!("Internal error: expected completed terminal execution"),
    }
}

/// How long a killed subprocess's reaper thread may take to report the exit
/// before the kill is logged as unconfirmed — the same three-second drain the
/// in-process solver lanes are held to (AY ask R1).
const KILLED_CHILD_REAP_LIMIT: Duration = Duration::from_secs(3);

/// After a timeout kill, WAIT for the child's reaper (the thread blocked in
/// `wait`/`wait_with_output`) instead of returning while the process may still
/// be exiting: the caller's next lane must not share the cores with it. AY's
/// resource design names this "owned subprocess with kill+wait". A SIGKILLed
/// process group exits almost at once, so this costs nothing in practice;
/// past the limit (a child stuck in the kernel) the kill is reported, not
/// silently assumed, and the reaper is left to finish the `wait` it is in.
fn reap_killed_child<T>(
    program: &str,
    rx: &mpsc::Receiver<T>,
    reaper: std::thread::JoinHandle<()>,
) {
    let started = Instant::now();
    match rx.recv_timeout(KILLED_CHILD_REAP_LIMIT) {
        Ok(_) | Err(mpsc::RecvTimeoutError::Disconnected) => {
            let _ = reaper.join();
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            eprintln!(
                "[AY] {program}: killed on timeout, but not reaped within {:.1}s — the exit \
                 is unconfirmed",
                started.elapsed().as_secs_f64()
            );
        }
    }
}

/// Run a command with timeout, capturing output.
///
/// This is the single exported "piped capture" execution path. All callers
/// that need a `Command → Output` with timeout protection should use this
/// function instead of hand-rolling mpsc+kill patterns.
///
/// Part of #995.
/// Updated for #1086: Subprocess tracking for OOM cleanup.
/// Updated for #1092: Memory pressure warning.
pub(crate) fn run_piped_with_timeout(mut cmd: Command, timeout: Duration) -> Result<Output> {
    let program = cmd.get_program().to_string_lossy().to_string();
    let timeout = clamp_to_watchdog_deadline(timeout, &program)?;

    // Check memory pressure before spawning (#1092)
    check_memory_pressure();

    // Fresh process group so the timeout kill below reaps grandchildren, and a
    // death signal so the group dies with this driver.
    isolate_in_process_group(&mut cmd);
    die_with_spawning_thread(&mut cmd);

    let child = cmd
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .context(format!("Failed to spawn {}", program))?;

    // Track subprocess for OOM cleanup (#1086).
    // Guard auto-unregisters on drop, including timeout bail paths (#2137 F3).
    let child_pid = child.id();
    let _guard = crate::subprocess_tracker::SubprocessGuard::new(child_pid);

    let (tx, rx) = mpsc::channel();

    // Spawn a thread to wait for the child process
    let reaper = std::thread::spawn(move || {
        let result = child.wait_with_output();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(timeout) {
        Ok(result) => {
            let _ = reaper.join();
            result.context(format!("Process {} error", program))
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Stop the process (and, as a group leader, its whole tree) on
            // timeout: SIGTERM, then SIGKILL.
            stop_timed_out_group_leader(&program, child_pid, &rx, reaper);
            // _guard drops here, auto-unregistering the killed PID
            bail!(
                "{} timed out after {:.1}s. Use --tool-timeout to increase the limit.",
                program,
                timeout.as_secs_f64()
            )
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            bail!("{} process thread panicked unexpectedly", program)
        }
    }
}

/// Run a command with timeout, leaving it outputting to terminal.
///
/// Internal helper called only by `execute_with_mode`. Not exported.
fn command_with_timeout_terminal(
    mut cmd: Command,
    timeout: Duration,
) -> Result<std::process::ExitStatus> {
    let program = cmd.get_program().to_string_lossy().to_string();
    let timeout = clamp_to_watchdog_deadline(timeout, &program)?;

    // Check memory pressure before spawning (#1092)
    check_memory_pressure();

    // Fresh process group so the timeout kill below reaps grandchildren, and a
    // death signal so the group dies with this driver.
    isolate_in_process_group(&mut cmd);
    die_with_spawning_thread(&mut cmd);

    let mut child = cmd.spawn().context(format!("Failed to spawn {}", program))?;

    // Track subprocess for OOM cleanup (#1086).
    // Guard auto-unregisters on drop, including timeout bail paths (#2137 F3).
    let child_pid = child.id();
    let _guard = crate::subprocess_tracker::SubprocessGuard::new(child_pid);

    let (tx, rx) = mpsc::channel();

    // Spawn a thread to wait for the child process
    let reaper = std::thread::spawn(move || {
        let result = child.wait();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(timeout) {
        Ok(result) => {
            let _ = reaper.join();
            result.context(format!("Process {} error", program))
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Stop the process on timeout: SIGTERM, then SIGKILL, to the
            // group it leads.
            stop_timed_out_group_leader(&program, child_pid, &rx, reaper);
            // _guard drops here, auto-unregistering the killed PID
            bail!(
                "{} timed out after {:.1}s. Use --tool-timeout to increase the limit.",
                program,
                timeout.as_secs_f64()
            )
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            bail!("{} process thread panicked unexpectedly", program)
        }
    }
}

/// Wait for a Child process to complete with timeout protection.
///
/// Part of #995: Prevents hanging on already-spawned processes.
/// Updated for #1086: Subprocess tracking for OOM cleanup.
///
/// # Arguments
/// * `child` - The spawned child process
/// * `timeout` - Maximum duration to wait
/// * `name` - Process name for error messages
///
/// # Returns
/// * `Ok(ExitStatus)` - Process completed within timeout
/// * `Err` - Process timed out
pub(crate) fn wait_with_timeout(
    mut child: Child,
    timeout: Duration,
    name: &str,
) -> Result<std::process::ExitStatus> {
    // An already-spawned child with no budget left is killed right away —
    // the refusal is the same typed error a never-spawned one gets.
    let timeout = match clamp_to_watchdog_deadline(timeout, name) {
        Ok(timeout) => timeout,
        Err(err) => {
            crate::subprocess_tracker::kill_pid_or_group(child.id());
            let _ = child.wait();
            return Err(err);
        }
    };

    // Track subprocess for OOM cleanup (#1086).
    // Note: Child may already be registered by caller, but registration is idempotent.
    // Guard auto-unregisters on drop, including timeout bail paths (#2137 F3).
    let child_pid = child.id();
    let _guard = crate::subprocess_tracker::SubprocessGuard::new(child_pid);

    let (tx, rx) = mpsc::channel();

    let reaper = std::thread::spawn(move || {
        let result = child.wait();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(timeout) {
        Ok(result) => {
            let _ = reaper.join();
            result.context(format!("Process {} error", name))
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Group-aware kill: reaps grandchildren when the child was
            // spawned as a process-group leader.
            crate::subprocess_tracker::kill_pid_or_group(child_pid);
            reap_killed_child(name, &rx, reaper);
            // _guard drops here, auto-unregistering the killed PID
            bail!(
                "{} timed out after {:.1}s. Use --tool-timeout to increase the limit.",
                name,
                timeout.as_secs_f64()
            )
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            bail!("{} process thread panicked unexpectedly", name)
        }
    }
}

/// Execute the provided function and measure the clock time it took for its execution.
/// Print the time with the given description if we are on verbose or debug mode.
pub(crate) fn with_timer<T, F>(verbosity: &impl Verbosity, func: F, description: &str) -> T
where
    F: FnOnce() -> T,
{
    let start = Instant::now();
    let ret = func();
    if verbosity.verbose() {
        let elapsed = start.elapsed();
        println!("Finished {description} in {}s", elapsed.as_secs_f32())
    }
    ret
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestVerbosity {
        quiet: bool,
        verbose: bool,
    }

    impl Verbosity for TestVerbosity {
        fn quiet(&self) -> bool {
            self.quiet
        }

        fn verbose(&self) -> bool {
            self.verbose
        }

        fn is_set(&self) -> bool {
            self.quiet || self.verbose
        }
    }

    #[cfg(unix)]
    fn shell_exit(code: i32) -> Command {
        let mut cmd = Command::new("sh");
        cmd.arg("-c").arg(format!("exit {code}"));
        cmd
    }

    /// The watchdog clamp keeps a headroom under the fire time and refuses
    /// a spawn that could only be killed.
    #[test]
    fn watchdog_clamp_keeps_headroom_and_refuses_exhausted_budgets() {
        let t = Duration::from_secs(15);
        // Unarmed watchdog: the tool timeout stands.
        assert_eq!(clamp_with_remaining(t, None), Some(t));
        // Plenty left: the tool timeout stands.
        assert_eq!(clamp_with_remaining(t, Some(Duration::from_secs(60))), Some(t));
        // Less left than the timeout: the remainder minus the headroom.
        assert_eq!(
            clamp_with_remaining(t, Some(Duration::from_secs(10))),
            Some(Duration::from_secs(10) - SPAWN_HEADROOM)
        );
        // Only the headroom (or less) left: refuse.
        assert_eq!(clamp_with_remaining(t, Some(SPAWN_HEADROOM)), None);
        assert_eq!(clamp_with_remaining(t, Some(Duration::ZERO)), None);
        // A zero tool timeout is a refusal too, armed or not.
        assert_eq!(clamp_with_remaining(Duration::ZERO, None), None);
        assert_eq!(clamp_with_remaining(Duration::ZERO, Some(Duration::from_secs(60))), None);
    }

    /// A refused spawn returns the typed phrase AND the timeout wording, so
    /// both the driver's own classification and outer runners' grep read it
    /// right — and no child is started.
    #[cfg(unix)]
    #[test]
    fn zero_budget_spawn_is_refused_with_the_typed_phrase() {
        let err = run_piped_with_timeout(shell_exit(0), Duration::ZERO)
            .expect_err("a zero budget must not spawn");
        let msg = format!("{err}");
        assert!(msg.contains(BUDGET_EXHAUSTED_BEFORE_SPAWN), "{msg}");
        assert!(msg.contains("timed out after"), "{msg}");
    }

    /// AY ask R1 for subprocess lanes: a timeout kills AND waits. When
    /// `run_piped_with_timeout` returns its timeout error, the child has been
    /// reaped — its pid is gone, not a zombie or a still-exiting process.
    #[cfg(target_os = "linux")]
    #[test]
    fn a_timed_out_child_is_killed_and_reaped_before_the_call_returns() {
        let dir = tempfile::tempdir().expect("tempdir");
        let pid_file = dir.path().join("pid");
        let mut cmd = Command::new("sh");
        cmd.arg("-c").arg(format!("echo $$ > {}; exec sleep 30", pid_file.display()));
        let started = Instant::now();
        let err = run_piped_with_timeout(cmd, Duration::from_millis(300))
            .expect_err("a 30 s child must time out");
        assert!(format!("{err}").contains("timed out after"), "{err}");
        assert!(started.elapsed() < Duration::from_secs(10), "{:?}", started.elapsed());
        let pid = std::fs::read_to_string(&pid_file).expect("child wrote its pid");
        let proc_dir = std::path::Path::new("/proc").join(pid.trim());
        assert!(!proc_dir.exists(), "the killed child {} must be reaped on return", pid.trim());
    }

    /// A timed-out child is asked to stop before it is killed: the group gets
    /// SIGTERM and [`TERM_GRACE`] to exit, so a trust-mc driver child runs its
    /// handler (which kills the solver groups it tracks) instead of dying with
    /// them orphaned. The child's TERM trap must have run when the call
    /// returns; under a bare SIGKILL it never does.
    #[cfg(unix)]
    #[test]
    fn a_timed_out_child_gets_sigterm_before_sigkill() {
        let dir = tempfile::tempdir().expect("tempdir");
        let marker = dir.path().join("term");
        let mut cmd = Command::new("sh");
        cmd.arg("-c").arg(format!(
            "trap 'echo term > {}; exit 0' TERM; while :; do sleep 0.05; done",
            marker.display()
        ));
        let err = run_piped_with_timeout(cmd, Duration::from_millis(300))
            .expect_err("an endless child must time out");
        assert!(format!("{err}").contains("timed out after"), "{err}");
        let got = std::fs::read_to_string(&marker).unwrap_or_default();
        assert_eq!(got.trim(), "term", "the TERM trap must run before the kill");
    }

    /// The role [`a_child_dies_with_its_driver_when_the_driver_group_is_sigkilled`]
    /// re-executes this test binary in: a stand-in driver that starts a long
    /// child through [`run_piped_with_timeout`] and waits on it.
    #[cfg(target_os = "linux")]
    const PDEATH_ROLE_DIR: &str = "TRUST_MC_TEST_PDEATH_ROLE_DIR";

    /// A child started through [`run_piped_with_timeout`] leads its own process
    /// group, so a SIGKILL of its driver's group -- the loop-contract retry
    /// parent's timeout, the dual gate's or the corpus runner's `killpg` --
    /// does not reach it. It must die with the driver anyway (the spawn arms
    /// `PR_SET_PDEATHSIG`): measured 2026-10-01, the CHC lane's external `ay`
    /// fallback outlived its SIGKILLed driver by 120 s and more. This test
    /// re-executes itself as that driver, SIGKILLs the driver's group, and
    /// requires the grandchild gone within seconds.
    #[cfg(target_os = "linux")]
    #[test]
    fn a_child_dies_with_its_driver_when_the_driver_group_is_sigkilled() {
        use std::os::unix::process::CommandExt;
        if let Some(dir) = std::env::var_os(PDEATH_ROLE_DIR) {
            // The stand-in driver: record the child's pid, then wait on it.
            let dir = std::path::PathBuf::from(dir);
            let mut child = Command::new("sh");
            child.arg("-c").arg(format!(
                "echo $$ > {0}/child.tmp && mv {0}/child.tmp {0}/child.pid && exec sleep 300",
                dir.display()
            ));
            let _ = run_piped_with_timeout(child, Duration::from_secs(300));
            return;
        }
        let dir = tempfile::tempdir().expect("tempdir");
        let mut driver = Command::new(std::env::current_exe().expect("test binary"));
        driver
            .args([
                "session::process::tests::a_child_dies_with_its_driver_when_the_driver_group_is_sigkilled",
                "--exact",
                "--test-threads=1",
                "--nocapture",
            ])
            .env(PDEATH_ROLE_DIR, dir.path())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .process_group(0);
        let mut driver = driver.spawn().expect("spawn the stand-in driver");
        let pid_file = dir.path().join("child.pid");
        let started = Instant::now();
        while !pid_file.exists() {
            assert!(started.elapsed() < Duration::from_secs(30), "the stand-in never started");
            std::thread::sleep(Duration::from_millis(20));
        }
        let child: i32 =
            std::fs::read_to_string(&pid_file).expect("pid").trim().parse().expect("pid number");
        // SAFETY: SIGKILL to the stand-in driver's own fresh group.
        unsafe {
            libc::kill(-(driver.id() as i32), libc::SIGKILL);
        }
        let _ = driver.wait();
        // Gone, or a zombie its new parent has not reaped yet: either way it
        // no longer runs.
        let running = |pid: i32| {
            std::fs::read_to_string(format!("/proc/{pid}/stat"))
                .ok()
                .and_then(|stat| {
                    stat.rsplit_once(')').map(|(_, rest)| rest.trim_start().to_string())
                })
                .is_some_and(|rest| !rest.starts_with('Z') && !rest.starts_with('X'))
        };
        let killed = Instant::now();
        while running(child) && killed.elapsed() < Duration::from_secs(5) {
            std::thread::sleep(Duration::from_millis(20));
        }
        let survived = running(child);
        if survived {
            // SAFETY: clean up the orphan this test would otherwise leak.
            unsafe {
                libc::kill(child, libc::SIGKILL);
            }
        }
        assert!(!survived, "child {child} outlived its SIGKILLed driver");
    }

    /// Test DEFAULT_TOOL_TIMEOUT_SECS constant is set to expected 10 minutes.
    #[test]
    fn test_default_tool_timeout_constant() {
        assert_eq!(
            DEFAULT_TOOL_TIMEOUT_SECS, 600,
            "Default tool timeout should be 600 seconds (10 minutes)"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_execute_with_limits_terminal_returns_completed() {
        let verbosity = TestVerbosity { quiet: false, verbose: false };
        let cmd = shell_exit(0);
        let result =
            execute_with_limits(&verbosity, cmd, RunMode::Terminal, RunLimits::no_limits())
                .expect("terminal mode should complete successfully");
        assert!(result.is_none());
    }

    #[cfg(unix)]
    #[test]
    fn test_execute_with_limits_piped_returns_child() {
        let verbosity = TestVerbosity { quiet: false, verbose: false };
        let cmd = shell_exit(0);
        let result = execute_with_limits(&verbosity, cmd, RunMode::Piped, RunLimits::no_limits())
            .expect("piped mode should return child process");
        let mut child = result.expect("piped mode should return Some(child)");
        let status = child.wait().expect("child wait should succeed");
        crate::subprocess_tracker::SubprocessTracker::unregister(child.id());
        assert!(status.success());
    }

    /// Regression for #2747: Suppress mode success path (arm 4) returns Completed.
    #[cfg(unix)]
    #[test]
    fn test_execute_with_limits_suppress_success() {
        let verbosity = TestVerbosity { quiet: false, verbose: false };
        let cmd = shell_exit(0);
        let result =
            execute_with_limits(&verbosity, cmd, RunMode::Suppress, RunLimits::no_limits())
                .expect("suppress mode should complete successfully");
        assert!(result.is_none(), "suppress mode should return None (Completed)");
    }

    /// Regression for #2747: Terminal mode failure path (arm 2) returns error.
    #[cfg(unix)]
    #[test]
    fn test_execute_with_limits_terminal_failure() {
        let verbosity = TestVerbosity { quiet: false, verbose: false };
        let cmd = shell_exit(1);
        let err = execute_with_limits(&verbosity, cmd, RunMode::Terminal, RunLimits::no_limits())
            .expect_err("terminal mode with exit 1 should fail");
        let msg = format!("{err}");
        assert!(msg.contains("exited with status"), "error should mention exit status, got: {msg}");
    }

    /// Regression for #2747: Suppress mode failure path (arm 4) calls flush_failed_output
    /// and returns error.
    #[cfg(unix)]
    #[test]
    fn test_execute_with_limits_suppress_failure() {
        let verbosity = TestVerbosity { quiet: false, verbose: false };
        let cmd = shell_exit(2);
        let err = execute_with_limits(&verbosity, cmd, RunMode::Suppress, RunLimits::no_limits())
            .expect_err("suppress mode with exit 2 should fail");
        let msg = format!("{err}");
        assert!(msg.contains("exited with status"), "error should mention exit status, got: {msg}");
    }

    /// Regression for #2747: Piped mode with timeout (arm 5) rejects immediately.
    #[cfg(unix)]
    #[test]
    fn test_execute_with_limits_piped_timeout_rejected() {
        let verbosity = TestVerbosity { quiet: false, verbose: false };
        let cmd = shell_exit(0);
        let limits = RunLimits::timeout_only(Some(Duration::from_secs(10)));
        let err = execute_with_limits(&verbosity, cmd, RunMode::Piped, limits)
            .expect_err("piped + timeout should be rejected");
        let msg = format!("{err}");
        assert!(
            msg.contains("Timeout is unsupported"),
            "error should say timeout unsupported for piped, got: {msg}"
        );
    }

    /// Regression for #2747: Suppress mode with is_set() upgrades to Terminal behavior.
    #[cfg(unix)]
    #[test]
    fn test_execute_with_limits_suppress_upgrades_to_terminal_when_verbose() {
        // When verbosity.is_set() is true, Suppress should behave like Terminal.
        // A successful exit should still return None (Completed).
        let verbosity = TestVerbosity { quiet: false, verbose: true };
        let cmd = shell_exit(0);
        let result =
            execute_with_limits(&verbosity, cmd, RunMode::Suppress, RunLimits::no_limits())
                .expect("suppress-upgraded-to-terminal should complete successfully");
        assert!(result.is_none(), "upgraded suppress mode should return None (Completed)");
    }
}
