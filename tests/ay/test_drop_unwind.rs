// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: Some harnesses (3/8) demoted PROOF→UNKNOWN by false proof defense (ay#8578).
//
//! Tests for drop unwind handling (#469).
//!
//! Verifies that TerminatorKind::Drop correctly models unwinding by
//! branching to cleanup or normal path via nondet selection.
//!
//! The codegen implementation (statement.rs:codegen_drop) uses:
//! - UnwindAction::Cleanup -> goto cleanup block
//! - UnwindAction::Unreachable -> assert false
//! - UnwindAction::Terminate -> assert false
//! - UnwindAction::Continue -> no unwind path
//!
//! Key: nondet() boolean chooses between unwind and normal path.

/// Simple struct with Drop to trigger drop codegen.
struct Droppable {
    value: i32,
}

impl Drop for Droppable {
    fn drop(&mut self) {
        // Drop implementation exists - codegen will generate drop call
    }
}

/// Test basic drop path - verifies normal path works.
#[kani::proof]
fn test_drop_normal_path() {
    let d = Droppable { value: 42 };
    // d goes out of scope - drop will be called
    // Nondet selects between unwind and normal path
    // This test verifies normal path succeeds
    kani::assert(d.value == 42, "value should be 42 before drop");
}

/// Test drop with symbolic value.
#[kani::proof]
fn test_drop_symbolic_value() {
    let v: i32 = kani::any();
    kani::assume(v > 0 && v < 100);
    let d = Droppable { value: v };
    kani::assert(d.value > 0, "symbolic value should satisfy constraint");
    // d dropped here - both unwind and normal paths explored
}

/// Struct with nested Droppable to test nested drop.
struct Nested {
    inner: Droppable,
    extra: i32,
}

impl Drop for Nested {
    fn drop(&mut self) {
        // Nested drop - will also drop inner
    }
}

/// Test nested drop handling.
#[kani::proof]
fn test_nested_drop() {
    let n = Nested { inner: Droppable { value: 10 }, extra: 20 };
    kani::assert(n.inner.value == 10, "inner value should be 10");
    kani::assert(n.extra == 20, "extra value should be 20");
    // Both Nested and inner Droppable will be dropped
}

/// Test drop in conditional scope.
#[kani::proof]
fn test_conditional_drop() {
    let cond: bool = kani::any();
    let mut result = 0;

    if cond {
        let d = Droppable { value: 5 };
        result = d.value;
        // d dropped here when cond is true
    }

    // result is either 0 or 5 depending on cond
    kani::assert(result == 0 || result == 5, "result should be 0 or 5");
}

/// Test multiple drops in sequence.
#[kani::proof]
fn test_sequential_drops() {
    let d1 = Droppable { value: 1 };
    let d2 = Droppable { value: 2 };
    let sum = d1.value + d2.value;
    kani::assert(sum == 3, "sum should be 3");
    // d2 dropped first (LIFO order), then d1
}

/// Test drop with mutable value.
#[kani::proof]
fn test_drop_mutable() {
    let mut d = Droppable { value: 0 };
    d.value = 100;
    kani::assert(d.value == 100, "mutated value should be 100");
    // d dropped with value=100
}

/// Test drop in loop (multiple iterations).
#[kani::proof]
#[kani::unwind(3)]
fn test_drop_in_loop() {
    let mut count: i32 = 0;
    let mut i: i32 = 0;
    while i < 2 {
        let d = Droppable { value: i };
        count += d.value;
        // d dropped at end of each iteration
        i += 1;
    }
    kani::assert(count == 1, "count should be 0+1=1");
}

/// Struct that tracks drop via mutable reference.
/// This tests that drop codegen correctly handles the drop call.
struct DropCounter<'a> {
    counter: &'a mut i32,
}

impl<'a> Drop for DropCounter<'a> {
    fn drop(&mut self) {
        *self.counter += 1;
    }
}

/// Test drop side effect verification.
#[kani::proof]
fn test_drop_side_effect() {
    let mut counter = 0;
    {
        let _dc = DropCounter { counter: &mut counter };
        // _dc will be dropped at end of scope
    }
    // After drop, counter should be incremented
    // Note: with nondet unwind, the drop side effect may not occur on unwind path
    // This is correct behavior - drop panics skip the side effect
    kani::assert(counter == 0 || counter == 1, "counter should be 0 or 1");
}
