// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module contains small helper functions for running Commands.
//! We could possibly eliminate this if we find a small-enough dependency.

use std::ffi::OsString;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::Duration;

use anyhow::{Context, Result, bail};

/// Helper trait to fallibly run commands
pub(crate) trait AutoRun {
    /// Run the command without a timeout. Currently unused but kept for API symmetry.
    #[allow(dead_code)]
    fn run(&mut self) -> Result<()>;
    fn run_with_timeout(&mut self, timeout: Duration) -> Result<()>;
}
impl AutoRun for Command {
    fn run(&mut self) -> Result<()> {
        // This can sometimes fail during the set-up of the forked process before exec,
        // for example by setting `current_dir` to a directory that does not exist.
        let status = self.status().with_context(|| {
            format!(
                "Internal failure before invoking command: {}",
                render_command(self).to_string_lossy()
            )
        })?;
        if !status.success() {
            bail!("Failed command: {}", render_command(self).to_string_lossy());
        }
        Ok(())
    }

    /// Run the command with a timeout.
    ///
    /// If the process exceeds the timeout, it is killed and an error is returned.
    /// This prevents setup/build processes from hanging indefinitely on slow
    /// networks or broken toolchains.
    ///
    /// Note: On non-Unix platforms (Windows), the process is not killed on timeout
    /// and may continue running as an orphan. This is acceptable since trust_mc primarily
    /// targets Unix systems (Linux, macOS).
    fn run_with_timeout(&mut self, timeout: Duration) -> Result<()> {
        let cmd_str = render_command(self);

        let mut child =
            self.stdout(Stdio::inherit()).stderr(Stdio::inherit()).spawn().with_context(|| {
                format!("Internal failure before invoking command: {}", cmd_str.to_string_lossy())
            })?;

        // Capture the process ID before moving child into the thread
        #[cfg(unix)]
        let child_pid = child.id();

        let (tx, rx) = mpsc::channel();

        // Spawn a thread to wait for the child process
        // Use wait() since we inherit stdio and don't need output capture
        std::thread::spawn(move || {
            let result = child.wait();
            let _ = tx.send(result);
        });

        match rx.recv_timeout(timeout) {
            Ok(result) => {
                let status = result
                    .with_context(|| format!("Process error for: {}", cmd_str.to_string_lossy()))?;
                if !status.success() {
                    bail!("Failed command: {}", cmd_str.to_string_lossy());
                }
                Ok(())
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                // Kill the process on timeout (Unix only)
                #[cfg(unix)]
                {
                    // SAFETY: Sending SIGKILL to our child process
                    unsafe {
                        libc::kill(child_pid as i32, libc::SIGKILL);
                    }
                }
                bail!(
                    "Command timed out after {:.0}s: {}",
                    timeout.as_secs_f64(),
                    cmd_str.to_string_lossy()
                )
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                bail!("Command thread panicked unexpectedly: {}", cmd_str.to_string_lossy())
            }
        }
    }
}

/// Render a Command as a string, to log it
fn render_command(cmd: &Command) -> OsString {
    let mut str = OsString::new();

    for (k, v) in cmd.get_envs() {
        if let Some(v) = v {
            str.push(k);
            str.push("=\"");
            str.push(v);
            str.push("\" ");
        }
    }

    str.push(cmd.get_program());

    for a in cmd.get_args() {
        str.push(" ");
        if a.to_string_lossy().contains(' ') {
            str.push("\"");
            str.push(a);
            str.push("\"");
        } else {
            str.push(a);
        }
    }

    str
}
