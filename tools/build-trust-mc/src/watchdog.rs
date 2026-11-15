// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The watchdog that bounds every child process this tool waits on.
//!
//! A cargo build is bounded by `TRUST_MC_BUILD_TIMEOUT_SECS` (default 3600 s,
//! `0` disables the watchdog). On timeout the watchdog kills the child AND
//! every descendant: killing only cargo leaves its rustc children running as
//! orphans that keep loading the host after the build has already failed.
//! The child stays in this tool's process group, so Ctrl-C still reaches the
//! whole build exactly as it did before.

use anyhow::{Result, bail, format_err};
use std::ffi::OsStr;
use std::process::{Child, ExitStatus};
use std::time::{Duration, Instant};

/// Overrides the watchdog of every cargo build, in whole seconds; `0` disables it.
pub(crate) const BUILD_TIMEOUT_ENV: &str = "TRUST_MC_BUILD_TIMEOUT_SECS";

/// The cargo-build limit when `TRUST_MC_BUILD_TIMEOUT_SECS` is unset. The
/// former 1200 s limit killed a release bundle build at exactly 20 minutes on
/// a host at load average 40-65.
pub(crate) const DEFAULT_BUILD_TIMEOUT: Duration = Duration::from_secs(3600);

/// How long to wait for the killed child to be reaped before reporting.
const REAP_GRACE: Duration = Duration::from_secs(10);

/// How often a bounded wait polls the child for an exit status.
const POLL_INTERVAL: Duration = Duration::from_millis(50);

/// Where a watchdog's limit came from, so a timeout error can say how to change it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Source {
    /// A constant of this tool (tar, bash helpers).
    Fixed,
    /// `DEFAULT_BUILD_TIMEOUT`, because `TRUST_MC_BUILD_TIMEOUT_SECS` is unset.
    BuildDefault,
    /// `TRUST_MC_BUILD_TIMEOUT_SECS`.
    BuildEnv,
}

/// A time limit on one child process.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Watchdog {
    /// `None` waits without limit.
    limit: Option<Duration>,
    source: Source,
}

impl Watchdog {
    /// A limit that no environment variable overrides.
    pub(crate) const fn fixed(limit: Duration) -> Self {
        Watchdog { limit: Some(limit), source: Source::Fixed }
    }

    /// The cargo-build watchdog, as `TRUST_MC_BUILD_TIMEOUT_SECS` sets it.
    pub(crate) fn cargo_build() -> Result<Self> {
        Self::cargo_build_from(std::env::var_os(BUILD_TIMEOUT_ENV).as_deref())
    }

    /// Parse a `TRUST_MC_BUILD_TIMEOUT_SECS` value: unset is the default, `0`
    /// disables the watchdog, and anything but a whole number of seconds is an
    /// error rather than a silent fallback.
    fn cargo_build_from(value: Option<&OsStr>) -> Result<Self> {
        let Some(raw) = value else {
            return Ok(Watchdog {
                limit: Some(DEFAULT_BUILD_TIMEOUT),
                source: Source::BuildDefault,
            });
        };
        let secs = raw
            .to_str()
            .filter(|text| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit()))
            .and_then(|digits| digits.parse::<u64>().ok())
            .ok_or_else(|| {
                format_err!(
                    "{BUILD_TIMEOUT_ENV}={:?} is not a whole number of seconds \
                     (unset for the default {}s, 0 disables the watchdog)",
                    raw.to_string_lossy(),
                    DEFAULT_BUILD_TIMEOUT.as_secs()
                )
            })?;
        let limit = (secs != 0).then(|| Duration::from_secs(secs));
        Ok(Watchdog { limit, source: Source::BuildEnv })
    }

    /// The limit, `None` when the watchdog is disabled.
    #[cfg(test)]
    pub(crate) fn limit(&self) -> Option<Duration> {
        self.limit
    }

    /// The error for a child that outran the limit, naming the effective limit
    /// and the variable that sets it.
    fn timeout_message(&self, what: &str, limit: Duration, killed_descendants: usize) -> String {
        let secs = limit.as_secs();
        let origin = match self.source {
            Source::Fixed => "a fixed limit".to_string(),
            Source::BuildDefault => format!(
                "the default; set {BUILD_TIMEOUT_ENV} to change it, 0 disables the watchdog"
            ),
            Source::BuildEnv => {
                format!("from {BUILD_TIMEOUT_ENV}={secs}; 0 disables the watchdog")
            }
        };
        format!(
            "{what} timed out after {secs}s (effective timeout {secs}s, {origin}); \
             killed it and {killed_descendants} descendant process(es)"
        )
    }

    /// Wait for `child` under this watchdog. On timeout the child and its whole
    /// descendant tree are killed and an error names the effective limit.
    ///
    /// The child is polled with `try_wait` from this thread, which alone owns it.
    /// A `None` answer means the child is not reaped (running, or a zombie
    /// nobody has collected), so its pid cannot have been reused by the time it
    /// is signalled. A wait thread that reaps the child could not promise that.
    pub(crate) fn wait(&self, mut child: Child, what: &str) -> Result<ExitStatus> {
        let Some(limit) = self.limit else {
            return Ok(child.wait()?);
        };
        if let Some(status) = poll_until(&mut child, Instant::now() + limit)? {
            return Ok(status);
        }
        let killed = kill_process_tree(&mut child);
        let _ = poll_until(&mut child, Instant::now() + REAP_GRACE);
        bail!(self.timeout_message(what, limit, killed))
    }
}

/// Poll `child` until it exits or `deadline` passes; `None` means it is still
/// unreaped at the deadline.
fn poll_until(child: &mut Child, deadline: Instant) -> Result<Option<ExitStatus>> {
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok(Some(status));
        }
        let now = Instant::now();
        if now >= deadline {
            return Ok(None);
        }
        std::thread::sleep(POLL_INTERVAL.min(deadline - now));
    }
}

/// Kill `child`, which must still be unreaped, and every descendant. Each
/// process is stopped before its children are listed, so nothing in the tree
/// can fork or reap a child while the tree is walked; then the tree is killed
/// leaves first. Returns the number of descendants found.
#[cfg(unix)]
fn kill_process_tree(child: &mut Child) -> usize {
    let root = child.id();
    let mut tree = vec![root];
    send_signal(root, libc::SIGSTOP);
    let mut next = 0;
    while next < tree.len() {
        for pid in child_pids(tree[next]) {
            if !tree.contains(&pid) {
                send_signal(pid, libc::SIGSTOP);
                tree.push(pid);
            }
        }
        next += 1;
    }
    for &pid in tree.iter().rev() {
        send_signal(pid, libc::SIGKILL);
    }
    tree.len() - 1
}

/// On non-Unix hosts only the child itself is killed; its descendants are not
/// found and may keep running.
#[cfg(not(unix))]
fn kill_process_tree(child: &mut Child) -> usize {
    let _ = child.kill();
    0
}

/// The direct children of `parent`, as `pgrep -P` lists them.
#[cfg(unix)]
fn child_pids(parent: u32) -> Vec<u32> {
    let Ok(output) = std::process::Command::new("pgrep")
        .arg("-P")
        .arg(parent.to_string())
        .stdin(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .output()
    else {
        return Vec::new();
    };
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| line.trim().parse::<u32>().ok())
        .filter(|&pid| pid > 1)
        .collect()
}

#[cfg(unix)]
fn send_signal(pid: u32, signal: libc::c_int) {
    // Never 0 or 1: kill(0, _) signals our own process group and kill(1, _) init.
    let Ok(pid) = libc::pid_t::try_from(pid) else { return };
    if pid > 1 {
        // SAFETY: kill(2) has no memory-safety preconditions; pid names one process.
        unsafe {
            libc::kill(pid, signal);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(value: Option<&str>) -> Result<Watchdog> {
        Watchdog::cargo_build_from(value.map(OsStr::new))
    }

    #[test]
    fn unset_is_the_default_build_timeout() {
        let watchdog = parse(None).unwrap();
        assert_eq!(watchdog.limit(), Some(Duration::from_secs(3600)));
        assert_eq!(watchdog.source, Source::BuildDefault);
    }

    #[test]
    fn zero_disables_the_watchdog() {
        assert_eq!(parse(Some("0")).unwrap().limit(), None);
        assert_eq!(parse(Some("000")).unwrap().limit(), None);
    }

    #[test]
    fn whole_seconds_set_the_limit() {
        let watchdog = parse(Some("7200")).unwrap();
        assert_eq!(watchdog.limit(), Some(Duration::from_secs(7200)));
        assert_eq!(watchdog.source, Source::BuildEnv);
        assert_eq!(parse(Some("1")).unwrap().limit(), Some(Duration::from_secs(1)));
    }

    #[test]
    fn anything_else_is_an_error_naming_the_variable() {
        for bad in ["", "abc", "20m", "1.5", "-1", "+5", " 90", "90 ", "99999999999999999999999"] {
            let err = parse(Some(bad)).expect_err(bad).to_string();
            assert!(err.contains("TRUST_MC_BUILD_TIMEOUT_SECS"), "{bad:?}: {err}");
            assert!(err.contains("0 disables"), "{bad:?}: {err}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn non_utf8_is_an_error() {
        use std::os::unix::ffi::OsStrExt;
        assert!(Watchdog::cargo_build_from(Some(OsStr::from_bytes(b"\xff"))).is_err());
    }

    #[test]
    fn timeout_message_names_the_effective_limit_and_the_variable() {
        let limit = Duration::from_secs(3600);
        let default = parse(None).unwrap().timeout_message("cargo build", limit, 3);
        assert!(default.contains("timed out after 3600s"), "{default}");
        assert!(default.contains("effective timeout 3600s"), "{default}");
        assert!(default.contains("TRUST_MC_BUILD_TIMEOUT_SECS"), "{default}");
        assert!(default.contains("3 descendant"), "{default}");
        let set =
            parse(Some("90")).unwrap().timeout_message("cargo build", Duration::from_secs(90), 0);
        assert!(set.contains("from TRUST_MC_BUILD_TIMEOUT_SECS=90"), "{set}");
        let fixed = Watchdog::fixed(Duration::from_secs(300)).timeout_message(
            "tar",
            Duration::from_secs(300),
            0,
        );
        assert!(!fixed.contains("TRUST_MC_BUILD_TIMEOUT_SECS"), "{fixed}");
    }

    #[cfg(unix)]
    #[test]
    fn a_child_that_exits_in_time_reports_its_status() {
        let child = std::process::Command::new("sh").args(["-c", "exit 3"]).spawn().unwrap();
        let status = Watchdog::fixed(Duration::from_secs(60)).wait(child, "sh").unwrap();
        assert_eq!(status.code(), Some(3));
        let child = std::process::Command::new("sh").args(["-c", "exit 0"]).spawn().unwrap();
        let disabled = parse(Some("0")).unwrap();
        assert!(disabled.wait(child, "sh").unwrap().success());
    }

    /// The defect this module fixes: a timeout must not leave grandchildren
    /// (rustc under cargo) running as orphans.
    #[cfg(unix)]
    #[test]
    fn timeout_kills_the_whole_descendant_tree() {
        use std::io::{BufRead, BufReader};
        use std::process::{Command, Stdio};
        use std::time::Instant;

        let mut child = Command::new("sh")
            .args(["-c", "sleep 300 & echo $!; wait"])
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let mut line = String::new();
        BufReader::new(child.stdout.take().unwrap()).read_line(&mut line).unwrap();
        let grandchild: libc::pid_t = line.trim().parse().unwrap();
        assert!(grandchild > 1);

        let err =
            Watchdog::fixed(Duration::from_secs(1)).wait(child, "sh").unwrap_err().to_string();
        assert!(err.contains("timed out after 1s"), "{err}");
        assert!(err.contains("1 descendant"), "{err}");

        // The orphaned sleep is reparented and reaped by init once it is dead.
        let deadline = Instant::now() + Duration::from_secs(20);
        // SAFETY: signal 0 only probes whether the pid exists.
        while unsafe { libc::kill(grandchild, 0) } == 0 {
            assert!(Instant::now() < deadline, "grandchild {grandchild} survived the watchdog");
            std::thread::sleep(Duration::from_millis(50));
        }
    }
}
