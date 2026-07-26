// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Modifications Copyright Kani Contributors
// See GitHub history for details.

use std::io;
use std::process::{Child, Output};

/// Maximum combined output size (stdout + stderr) before truncation.
/// Prevents OOM from tests that emit massive solver traces.
const MAX_OUTPUT_BYTES: usize = 50 * 1024 * 1024; // 50 MB

pub(crate) fn read2(mut child: Child) -> io::Result<Output> {
    let mut stdout = Vec::new();
    let mut stderr = Vec::new();
    let mut total_bytes: usize = 0;

    drop(child.stdin.take());
    self::imp::read2(
        child.stdout.take().unwrap(),
        child.stderr.take().unwrap(),
        &mut |is_stdout, data, _| {
            if total_bytes < MAX_OUTPUT_BYTES {
                let remaining = MAX_OUTPUT_BYTES - total_bytes;
                let to_copy = data.len().min(remaining);
                let out = if is_stdout { &mut stdout } else { &mut stderr };
                out.extend_from_slice(&data[..to_copy]);
                total_bytes += to_copy;
            }
            data.clear();
        },
    )?;
    let status = child.wait()?;

    Ok(Output { status, stdout, stderr })
}

#[cfg(not(any(unix, windows)))]
mod imp {
    use std::io::{self, Read};
    use std::process::{ChildStderr, ChildStdout};

    pub(super) fn read2(
        out_pipe: ChildStdout,
        err_pipe: ChildStderr,
        data: &mut dyn FnMut(bool, &mut Vec<u8>, bool),
    ) -> io::Result<()> {
        let mut buffer = Vec::new();
        out_pipe.read_to_end(&mut buffer)?;
        data(true, &mut buffer, true);
        buffer.clear();
        err_pipe.read_to_end(&mut buffer)?;
        data(false, &mut buffer, true);
        Ok(())
    }
}

#[cfg(unix)]
mod imp {
    use std::io;
    use std::io::prelude::*;
    use std::mem;
    use std::os::unix::prelude::*;
    use std::process::{ChildStderr, ChildStdout};

    pub(super) fn read2(
        mut out_pipe: ChildStdout,
        mut err_pipe: ChildStderr,
        data: &mut dyn FnMut(bool, &mut Vec<u8>, bool),
    ) -> io::Result<()> {
        unsafe {
            libc::fcntl(out_pipe.as_raw_fd(), libc::F_SETFL, libc::O_NONBLOCK);
            libc::fcntl(err_pipe.as_raw_fd(), libc::F_SETFL, libc::O_NONBLOCK);
        }

        let mut out_done = false;
        let mut err_done = false;
        let mut out = Vec::new();
        let mut err = Vec::new();

        let mut fds: [libc::pollfd; 2] = unsafe { mem::zeroed() };
        fds[0].fd = out_pipe.as_raw_fd();
        fds[0].events = libc::POLLIN;
        fds[1].fd = err_pipe.as_raw_fd();
        fds[1].events = libc::POLLIN;
        let mut nfds = 2;
        let mut errfd = 1;

        // Poll timeout in ms. Using 10s instead of infinite (-1) to prevent
        // hangs when grandchild processes (z3/ay solver) inherit pipe FDs and
        // keep them open after the immediate child is killed.
        const POLL_TIMEOUT_MS: libc::c_int = 10_000;
        let mut consecutive_timeouts: u32 = 0;
        const MAX_CONSECUTIVE_TIMEOUTS: u32 = 6; // 60s total before giving up

        while nfds > 0 {
            let r = unsafe { libc::poll(fds.as_mut_ptr(), nfds, POLL_TIMEOUT_MS) };
            if r == 0 {
                // Poll timed out with no activity on pipes.
                consecutive_timeouts += 1;
                if consecutive_timeouts >= MAX_CONSECUTIVE_TIMEOUTS {
                    // Pipes silent too long — likely orphan grandchild holding
                    // FDs open. Break to avoid infinite hang.
                    let _ = io::Write::write_all(
                        &mut io::stderr(),
                        format!(
                            "read2: poll timed out {}s with no pipe activity, giving up\n",
                            (POLL_TIMEOUT_MS as u64 * MAX_CONSECUTIVE_TIMEOUTS as u64) / 1000
                        )
                        .as_bytes(),
                    );
                    break;
                }
                continue;
            }
            consecutive_timeouts = 0;
            if r == -1 {
                let err = io::Error::last_os_error();
                if err.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(err);
            }

            // Read as much as we can from each pipe, ignoring EWOULDBLOCK or
            // EAGAIN. If we hit EOF, then this will happen because the underlying
            // reader will return Ok(0), in which case we'll see `Ok` ourselves. In
            // this case we flip the other fd back into blocking mode and read
            // whatever's leftover on that file descriptor.
            let handle = |res: io::Result<_>| match res {
                Ok(_) => Ok(true),
                Err(e) => {
                    if e.kind() == io::ErrorKind::WouldBlock {
                        Ok(false)
                    } else {
                        Err(e)
                    }
                }
            };
            if !err_done && fds[errfd].revents != 0 && handle(err_pipe.read_to_end(&mut err))? {
                err_done = true;
                nfds -= 1;
            }
            data(false, &mut err, err_done);
            if !out_done && fds[0].revents != 0 && handle(out_pipe.read_to_end(&mut out))? {
                out_done = true;
                fds[0].fd = err_pipe.as_raw_fd();
                errfd = 0;
                nfds -= 1;
            }
            data(true, &mut out, out_done);
        }
        Ok(())
    }
}
