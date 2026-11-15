// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The diagnostic counter registry belongs to one compilation
//! (`codegen_ctx/diagnostics_global.rs`, "One registry per compilation").
//!
//! The test build runs thousands of compilations in one process. When the
//! registry was one process-wide instance, a test that drained the per-function
//! maps before its own codegen also removed a concurrent test's records between
//! that test's codegen and its read, so a count test passed or failed with the
//! schedule (`test_vec_resize_shrink_eq_no_translation_drop` passed in suite
//! runs and failed alone). These tests state the ownership rule: a thread's
//! drains reach only its own registry, and a compilation records into the
//! registry of the test that started it.

#![allow(clippy::unwrap_used)]

use std::sync::{Arc, Barrier};

use super::common::*;
use crate::codegen_ay::chc::codegen_ctx::globals::record_translation_drop_for_fn;

/// Red with one process-wide registry: the second thread's drain empties the
/// map the first thread recorded into, between its record and its read.
#[test]
fn a_drain_on_another_thread_leaves_this_threads_records() {
    let both = Arc::new(Barrier::new(2));
    let recorder_side = Arc::clone(&both);
    let recorder = std::thread::spawn(move || {
        let _ = take_translation_drop_by_fn();
        record_translation_drop_for_fn("compilation_counters_probe", 3);
        recorder_side.wait(); // recorded
        recorder_side.wait(); // the other thread has drained
        take_translation_drop_by_fn().get("compilation_counters_probe").copied()
    });
    both.wait();
    let drained_here = take_translation_drop_by_fn();
    both.wait();
    assert_eq!(
        drained_here.get("compilation_counters_probe"),
        None,
        "a drain must not see another thread's records"
    );
    assert_eq!(
        recorder.join().unwrap(),
        Some(3),
        "a thread must read back what it recorded, whatever another thread drains"
    );
}

/// The compilation runs on rustc's own thread. Its records land in the
/// registry of the test that started it, so they are visible on the test
/// thread after the callback returns. Red when the harness does not hand its
/// registry to the compilation thread: the records then land in that thread's
/// own registry and the test thread reads nothing.
#[test]
fn a_compilation_records_into_the_registry_of_the_test_that_started_it() {
    let _ = take_translation_drop_by_fn();
    with_test_ay_ctx_for_source("pub fn compilation_counters_handoff() {}", |_ctx| {
        record_translation_drop_for_fn("compilation_counters_handoff_probe", 2);
    });
    assert_eq!(
        take_translation_drop_by_fn().get("compilation_counters_handoff_probe").copied(),
        Some(2),
        "the compilation thread's records must reach the test that started it"
    );
}
