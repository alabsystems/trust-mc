// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Lock-free, allocation-free output helpers for emergency paths.
//!
//! `println!`/`eprintln!` acquire the Rust stdio handle locks. A watchdog
//! thread (or a signal handler) that fires while another thread is blocked
//! mid-write — or hung while *holding* the stdout lock — would deadlock on
//! those locks and never emit its final markers. The helpers here bypass
//! Rust stdio entirely: messages are assembled into a fixed stack buffer
//! and written with raw `libc::write` calls on fds 1/2.
//!
//! These helpers must remain:
//! - lock-free (no Rust stdio locks, no mutexes)
//! - allocation-free (the hang may be inside the allocator)
//!
//! which also makes them safe to call from signal handlers.

/// Maximum assembled message size. Larger messages are truncated.
const STACK_BUF_LEN: usize = 512;

/// Format a `u64` as decimal digits into `buf`, returning the digit slice.
///
/// Allocation-free; `buf` must be 20 bytes (enough for `u64::MAX`).
pub(crate) fn u64_decimal(value: u64, buf: &mut [u8; 20]) -> &[u8] {
    if value == 0 {
        buf[0] = b'0';
        return &buf[..1];
    }
    let mut i = buf.len();
    let mut v = value;
    while v > 0 {
        i -= 1;
        buf[i] = b'0' + (v % 10) as u8;
        v /= 10;
    }
    &buf[i..]
}

/// Assemble `parts` into one stack buffer and write it to stdout (fd 1)
/// with a single raw `write` call (minimizes interleaving with other
/// writers). Truncates past [`STACK_BUF_LEN`]. Lock- and allocation-free.
pub(crate) fn write_stdout_parts(parts: &[&[u8]]) {
    write_fd_parts(1, parts);
}

/// Like [`write_stdout_parts`] but targets stderr (fd 2).
pub(crate) fn write_stderr_parts(parts: &[&[u8]]) {
    write_fd_parts(2, parts);
}

#[cfg(unix)]
fn write_fd_parts(fd: i32, parts: &[&[u8]]) {
    let mut buf = [0u8; STACK_BUF_LEN];
    let mut len = 0usize;
    for part in parts {
        let take = part.len().min(STACK_BUF_LEN - len);
        buf[len..len + take].copy_from_slice(&part[..take]);
        len += take;
        if len == STACK_BUF_LEN {
            break;
        }
    }
    raw_write(fd, &buf[..len]);
}

/// Raw `write(2)` loop, retrying on EINTR and partial writes.
#[cfg(unix)]
fn raw_write(fd: i32, mut bytes: &[u8]) {
    while !bytes.is_empty() {
        // SAFETY: `bytes` is a valid, live buffer of the given length; fd 1/2
        // are always open. write(2) is async-signal-safe.
        let ret = unsafe { libc::write(fd, bytes.as_ptr().cast::<libc::c_void>(), bytes.len()) };
        if ret > 0 {
            bytes = &bytes[ret as usize..];
        } else if ret == -1
            && std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted
        {
            continue;
        } else {
            // Unrecoverable write error (e.g. EPIPE): give up silently —
            // this is a best-effort emergency path.
            break;
        }
    }
}

#[cfg(not(unix))]
fn write_fd_parts(fd: i32, parts: &[&[u8]]) {
    // Non-Unix fallback: use Rust stdio (locking acceptable — the lock-free
    // requirement is only load-bearing on Unix where the watchdog runs).
    use std::io::Write;
    let assemble = |out: &mut dyn Write| {
        for part in parts {
            let _ = out.write_all(part);
        }
        let _ = out.flush();
    };
    if fd == 1 {
        assemble(&mut std::io::stdout());
    } else {
        assemble(&mut std::io::stderr());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u64_decimal_zero() {
        let mut buf = [0u8; 20];
        assert_eq!(u64_decimal(0, &mut buf), b"0");
    }

    #[test]
    fn u64_decimal_small() {
        let mut buf = [0u8; 20];
        assert_eq!(u64_decimal(605, &mut buf), b"605");
    }

    #[test]
    fn u64_decimal_max() {
        let mut buf = [0u8; 20];
        assert_eq!(u64_decimal(u64::MAX, &mut buf), b"18446744073709551615");
    }
}
