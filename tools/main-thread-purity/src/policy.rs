// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// The checkable rule, encoded as data: a SEED set and a DENY set, plus an
// allowlist escape hatch.

use crate::path::segment_matches;
use std::collections::BTreeSet;

/// A reason a leaf is forbidden on the UI/main thread.
#[derive(Clone, Copy, Debug)]
pub struct DenyEntry {
    /// A path SEGMENT prefix (no trailing `::` needed — boundary is enforced by
    /// `segment_matches`, the collision-guarded matcher).
    pub prefix: &'static str,
    /// Why this leaf is unbounded-blocking.
    pub why: &'static str,
}

pub struct Policy {
    /// UI/main-thread root patterns. A node is a SEED iff its `Instance::name()`
    /// contains any of these. In real trust-mc these roots are enumerated the
    /// way `filter_crate_items` enumerates `#[kani::proof]` harnesses: by
    /// scanning for `impl winit::application::ApplicationHandler for _` methods
    /// and `fn main`. (Substring match, not segment match, because handler
    /// methods render as `<App as …ApplicationHandler<…>>::window_event`.)
    pub seed_patterns: Vec<&'static str>,

    /// Forbidden unbounded-blocking leaf operations.
    pub deny: Vec<DenyEntry>,

    /// Leaves explicitly PROVEN bounded (timeout-wrapped / non-blocking / moved
    /// to a detached thread). Equivalent to a `#[trust::main_thread_safe]`
    /// attribute escape hatch. Matched by exact `Instance::name()`.
    pub allow_exact: BTreeSet<String>,
}

impl Policy {
    /// The policy for the aterm UI-thread-purity invariant.
    pub fn aterm() -> Policy {
        Policy {
            seed_patterns: vec![
                // `fn main` — process entry and the post-`run_app` teardown that
                // drops `App` on the main thread.
                "::main",
                // Every winit handler method. The concrete impl renders as
                // `<App as …::ApplicationHandler<…>>::method`.
                "ApplicationHandler",
            ],
            deny: vec![
                // THE aterm quit-hang: close(2) on a tty/PTY master can block
                // draining the slave and reaping the child (observed: 49s wedge).
                DenyEntry {
                    prefix: "libc::close",
                    why: "close() on a tty/PTY fd can block on slave drain + child teardown",
                },
                // Raw blocking I/O with no timeout.
                DenyEntry { prefix: "libc::read", why: "blocking read() with no timeout" },
                DenyEntry {
                    prefix: "libc::write",
                    why: "blocking write() with no timeout (full kernel buffer wedges)",
                },
                DenyEntry { prefix: "libc::poll", why: "poll() with no timeout" },
                DenyEntry { prefix: "libc::select", why: "select() with no timeout" },
                // Child-process reaping.
                DenyEntry { prefix: "libc::waitpid", why: "waitpid() blocks until the child exits" },
                DenyEntry { prefix: "libc::wait", why: "wait() blocks until a child exits" },
                // Thread join — unbounded if the joined thread is itself blocked.
                DenyEntry {
                    prefix: "std::thread::JoinHandle",
                    why: "JoinHandle::join() blocks until the thread finishes",
                },
                // A lock acquisition that may be held across I/O is unbounded.
                DenyEntry {
                    prefix: "std::sync::Mutex",
                    why: "Mutex::lock() can block unboundedly if the holder is doing I/O",
                },
                DenyEntry {
                    prefix: "std::sync::RwLock",
                    why: "RwLock::read()/write() can block unboundedly",
                },
                // Synchronous channel recv with no deadline.
                DenyEntry {
                    prefix: "std::sync::mpsc::Receiver",
                    why: "Receiver::recv() blocks until a message arrives",
                },
            ],
            allow_exact: BTreeSet::new(),
        }
    }

    /// Mark a leaf as proven-bounded (escape hatch).
    pub fn allow(mut self, exact_path: &str) -> Self {
        self.allow_exact.insert(exact_path.to_string());
        self
    }

    /// Is `path` a UI/main-thread seed root?
    pub fn is_seed(&self, path: &str) -> bool {
        self.seed_patterns.iter().any(|p| path.contains(p))
    }

    /// If `path` is a forbidden, not-proven-safe leaf, return why.
    /// Uses the collision-guarded `segment_matches` so `libc::close` never
    /// swallows `libc::close_range`/`libc::closedir`.
    pub fn classify_leaf(&self, path: &str) -> Option<&'static str> {
        if self.allow_exact.contains(path) {
            return None;
        }
        self.deny
            .iter()
            .find(|d| segment_matches(path, d.prefix))
            .map(|d| d.why)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seeds_match_handlers_and_main() {
        let p = Policy::aterm();
        assert!(p.is_seed("aterm_gui::main"));
        assert!(p.is_seed("<aterm_gui::App as winit::application::ApplicationHandler<Wake>>::window_event"));
        assert!(!p.is_seed("aterm_gui::Session::spawn_reader_thread::{closure#0}"));
    }

    #[test]
    fn close_is_denied_but_close_range_is_not() {
        let p = Policy::aterm();
        assert!(p.classify_leaf("libc::close").is_some());
        // The collision guard in action at the POLICY layer.
        assert!(p.classify_leaf("libc::close_range").is_none());
        assert!(p.classify_leaf("libc::closedir").is_none());
    }

    #[test]
    fn allowlist_clears_a_proven_safe_leaf() {
        let p = Policy::aterm().allow("libc::close");
        assert!(p.classify_leaf("libc::close").is_none());
    }
}
