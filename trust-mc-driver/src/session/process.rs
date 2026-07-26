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

/// Clamp a subprocess timeout to the wall-clock watchdog's remaining
/// budget: `min(tool_timeout, watchdog_remaining)`.
///
/// Every timeout-guarded subprocess (compiler, cargo, ay solver) flows
/// through this chokepoint, so no child can be granted a budget extending
/// past the watchdog's planned fire time. A hung child then surfaces as an
/// ordinary subprocess-timeout error (clean UNKNOWN/error reporting)
/// instead of requiring the watchdog's hard `_exit`. When the watchdog is
/// unarmed (no `--harness-timeout` anywhere), the timeout is unchanged.
///
/// A fully exhausted budget clamps to zero: the spawn still happens but
/// times out immediately — fail-closed, never an unbounded wait.
fn clamp_to_watchdog_deadline(timeout: Duration) -> Duration {
    match crate::wall_clock_watchdog::remaining() {
        Some(remaining) => timeout.min(remaining),
        None => timeout,
    }
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
    let timeout = clamp_to_watchdog_deadline(timeout);

    // Check memory pressure before spawning (#1092)
    check_memory_pressure();

    // Fresh process group so the timeout kill below reaps grandchildren.
    isolate_in_process_group(&mut cmd);

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
    std::thread::spawn(move || {
        let result = child.wait_with_output();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(timeout) {
        Ok(result) => result.context(format!("Process {} error", program)),
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Kill the process (and, as a group leader, its whole tree) on timeout
            crate::subprocess_tracker::kill_pid_or_group(child_pid);
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
    let timeout = clamp_to_watchdog_deadline(timeout);

    // Check memory pressure before spawning (#1092)
    check_memory_pressure();

    // Fresh process group so the timeout kill below reaps grandchildren.
    isolate_in_process_group(&mut cmd);

    let mut child = cmd.spawn().context(format!("Failed to spawn {}", program))?;

    // Track subprocess for OOM cleanup (#1086).
    // Guard auto-unregisters on drop, including timeout bail paths (#2137 F3).
    let child_pid = child.id();
    let _guard = crate::subprocess_tracker::SubprocessGuard::new(child_pid);

    let (tx, rx) = mpsc::channel();

    // Spawn a thread to wait for the child process
    std::thread::spawn(move || {
        let result = child.wait();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(timeout) {
        Ok(result) => result.context(format!("Process {} error", program)),
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Kill the process on timeout. Group-aware kill: reaps
            // grandchildren when the child was spawned as a group leader.
            crate::subprocess_tracker::kill_pid_or_group(child_pid);
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
    let timeout = clamp_to_watchdog_deadline(timeout);

    // Track subprocess for OOM cleanup (#1086).
    // Note: Child may already be registered by caller, but registration is idempotent.
    // Guard auto-unregisters on drop, including timeout bail paths (#2137 F3).
    let child_pid = child.id();
    let _guard = crate::subprocess_tracker::SubprocessGuard::new(child_pid);

    let (tx, rx) = mpsc::channel();

    std::thread::spawn(move || {
        let result = child.wait();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(timeout) {
        Ok(result) => result.context(format!("Process {} error", name)),
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Group-aware kill: reaps grandchildren when the child was
            // spawned as a process-group leader.
            crate::subprocess_tracker::kill_pid_or_group(child_pid);
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
