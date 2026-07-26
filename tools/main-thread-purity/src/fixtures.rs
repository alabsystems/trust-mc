// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Test fixtures: monomorphized call graphs in the `Instance::name()` string form
// trust-mc's reachability collector produces. These model aterm's pre-fix
// quit-hang and the safe teardown that the fix introduced.

use crate::graph::Edge;

/// The aterm quit-hang, modeled on the pre-fix tree:
///   crates/aterm-gui/src/main.rs — `impl Drop for Session` (≈ line 691) closes
///   `self.master` (the PTY master fd) via `libc::close`. `App` owns
///   `Vec<Session>` and is the winit `ApplicationHandler`. When `run_app`
///   returns on the main thread, `App` is dropped -> the `Vec<Session>` is
///   dropped -> each `Session::drop` runs `libc::close` on the PTY master, which
///   blocks draining the slave + reaping the child: the 49s wedge.
pub fn aterm_pre_fix() -> Vec<Edge> {
    vec![
        // ---- Process-exit teardown path (main thread) ----
        // `run_app` returns, then the `App` value is dropped in place.
        Edge::drop("aterm_gui::main", "core::ptr::drop_in_place::<aterm_gui::App>"),
        // Dropping `App` drops its `Vec<Session>` field...
        Edge::drop(
            "core::ptr::drop_in_place::<aterm_gui::App>",
            "core::ptr::drop_in_place::<alloc::vec::Vec<aterm_gui::Session>>",
        ),
        // ...which drops each `Session` in place...
        Edge::drop(
            "core::ptr::drop_in_place::<alloc::vec::Vec<aterm_gui::Session>>",
            "core::ptr::drop_in_place::<aterm_gui::Session>",
        ),
        // ...whose glue runs the user-written `impl Drop for Session`...
        Edge::drop(
            "core::ptr::drop_in_place::<aterm_gui::Session>",
            "<aterm_gui::Session as core::ops::Drop>::drop",
        ),
        // ...which calls `libc::close` on the PTY master fd — THE wedge.
        Edge::call("<aterm_gui::Session as core::ops::Drop>::drop", "libc::close"),

        // ---- Second, independent path: Cmd-W close-tab in a window_event ----
        Edge::call(
            "<aterm_gui::App as winit::application::ApplicationHandler<Wake>>::window_event",
            "aterm_gui::App::close_active_tab",
        ),
        Edge::drop(
            "aterm_gui::App::close_active_tab",
            "core::ptr::drop_in_place::<aterm_gui::Session>",
        ),

        // ---- Benign main-thread control path: bounded GPU work ----
        Edge::call(
            "<aterm_gui::App as winit::application::ApplicationHandler<Wake>>::about_to_wait",
            "aterm_gui::App::render",
        ),
        Edge::call("aterm_gui::App::render", "aterm_gpu::Renderer::present"),

        // ---- Worker thread (NOT seeded): the reader thread legitimately blocks
        // in read(). No seed reaches it, so it must NOT be flagged. ----
        Edge::call(
            "aterm_gui::Session::spawn_reader_thread::{closure#0}",
            "libc::read",
        ),

        // ---- A SIBLING that the collision guard must not confuse with close():
        // a helper that calls close_range(2) to shut a range of inherited fds.
        // It is reachable from a seed, but close_range is the *safe* primitive. ----
        Edge::call(
            "<aterm_gui::Session as core::ops::Drop>::drop",
            "libc::close_range",
        ),
    ]
}

/// The SAFE teardown the fix should introduce: hang up the PTY (SIGHUP via a
/// non-blocking `tcflush` + `kill`), then hand the fd to a DETACHED reaper
/// thread that does the blocking `close`/`waitpid` OFF the main thread. The main
/// thread's `Session::drop` does only bounded, non-blocking work.
///
/// Crucially: the blocking `libc::close`/`libc::waitpid` here live behind
/// `std::thread::Builder::spawn`'s closure, which is NOT reachable from any seed
/// via a synchronous edge — so the checker is GREEN.
pub fn aterm_safe_teardown() -> Vec<Edge> {
    vec![
        // main -> drop App -> drop Vec -> drop Session (same as before)...
        Edge::drop("aterm_gui::main", "core::ptr::drop_in_place::<aterm_gui::App>"),
        Edge::drop(
            "core::ptr::drop_in_place::<aterm_gui::App>",
            "core::ptr::drop_in_place::<alloc::vec::Vec<aterm_gui::Session>>",
        ),
        Edge::drop(
            "core::ptr::drop_in_place::<alloc::vec::Vec<aterm_gui::Session>>",
            "core::ptr::drop_in_place::<aterm_gui::Session>",
        ),
        Edge::drop(
            "core::ptr::drop_in_place::<aterm_gui::Session>",
            "<aterm_gui::Session as core::ops::Drop>::drop",
        ),
        // ...but now Session::drop only: (a) sends SIGHUP (non-blocking) and
        // (b) spawns a DETACHED reaper, then returns. Bounded work only.
        Edge::call("<aterm_gui::Session as core::ops::Drop>::drop", "libc::kill"),
        Edge::call(
            "<aterm_gui::Session as core::ops::Drop>::drop",
            "std::thread::Builder::spawn::<aterm_gui::reap_pty::{closure#0}>",
        ),
        // The blocking close()/waitpid() live INSIDE the detached reaper closure.
        // There is NO edge from the spawn call into the closure body that the
        // checker treats as same-thread: `Builder::spawn` starts a new OS thread,
        // so the closure is a fresh root, not a callee on the main thread.
        // We therefore model the reaper as its own disconnected subgraph.
        Edge::call("aterm_gui::reap_pty::{closure#0}", "libc::close"),
        Edge::call("aterm_gui::reap_pty::{closure#0}", "libc::waitpid"),

        // Benign render path retained as a control.
        Edge::call(
            "<aterm_gui::App as winit::application::ApplicationHandler<Wake>>::about_to_wait",
            "aterm_gui::App::render",
        ),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::{analyze, Severity};
    use crate::graph::{CallGraph, EdgeReason};
    use crate::policy::Policy;

    #[test]
    fn catches_the_aterm_quit_hang_through_drop() {
        let g = CallGraph::from_edges(aterm_pre_fix());
        let findings = analyze(&g, &Policy::aterm());

        let close = findings
            .iter()
            .find(|f| f.leaf == "libc::close")
            .expect("must flag libc::close on the UI/main thread");

        // It must be the high-severity case: reached THROUGH Drop glue.
        assert_eq!(close.severity, Severity::ErrorViaDrop);
        assert!(close.why.contains("PTY"));
        // The witness must actually traverse a Drop edge.
        assert!(close.witness.iter().any(|(_, r)| *r == EdgeReason::Drop));
        // And it must originate from a main-thread root.
        assert!(close.seed.contains("main") || close.seed.contains("ApplicationHandler"));
    }

    #[test]
    fn pre_fix_does_not_flag_worker_thread_read() {
        // The reader thread's blocking read() is fine: no seed reaches it.
        let g = CallGraph::from_edges(aterm_pre_fix());
        let findings = analyze(&g, &Policy::aterm());
        assert!(
            findings.iter().all(|f| f.leaf != "libc::read"),
            "worker-thread read() must NOT be flagged"
        );
    }

    #[test]
    fn pre_fix_does_not_flag_close_range_sibling() {
        // close_range(2) is reachable from a seed but is the SAFE primitive; the
        // collision guard must keep it out of the findings.
        let g = CallGraph::from_edges(aterm_pre_fix());
        let findings = analyze(&g, &Policy::aterm());
        assert!(
            findings.iter().all(|f| f.leaf != "libc::close_range"),
            "close_range() is safe and must NOT be flagged"
        );
    }

    #[test]
    fn pre_fix_render_path_is_clean() {
        let g = CallGraph::from_edges(aterm_pre_fix());
        let findings = analyze(&g, &Policy::aterm());
        assert!(findings.iter().all(|f| !f.leaf.contains("present")));
    }

    #[test]
    fn safe_teardown_is_green() {
        // Hangup-then-detached-close: the main thread's Session::drop does only
        // bounded work; the blocking close/waitpid live in a detached reaper that
        // no seed reaches synchronously. The checker must report NOTHING.
        let g = CallGraph::from_edges(aterm_safe_teardown());
        let findings = analyze(&g, &Policy::aterm());
        assert!(
            findings.is_empty(),
            "safe teardown must be GREEN, got: {:?}",
            findings.iter().map(|f| (&f.seed, &f.leaf)).collect::<Vec<_>>()
        );
    }
}
