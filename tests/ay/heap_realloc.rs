// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-expect: test_vec_multiple_resize=PROOF
// kani-expect: test_vec_pop_preserve=PROOF
// kani-expect: test_vec_push_realloc=PROOF
// kani-expect: test_vec_reserve=PROOF
// kani-expect: test_vec_shrink_to_fit=PROOF
// kani-expect: test_vec_with_capacity=PROOF
// kani-flags: --ay-chc-track=mem
//
//! Heap realloc tests for Phase 4 (#1231).
//!
//! Tests reallocation patterns through Vec operations.
//! These patterns are common in real-world code and exercise
//! heap growth/shrink paths via the allocator.
//!
//! **Status:** 1/7 SUCCESSFUL, 4/7 all-checks-pass (DT+BV demotion),
//! 2/7 partial (2026-02-16). fld_data propagation complete (#1632).
//! Remaining blockers: reserve/capacity modeling, loop unrolling, DT+BV validation.

/// Test Vec push which may trigger realloc internally.
#[kani::proof]
fn test_vec_push_realloc() {
    // Vec starts with capacity 0, pushes trigger allocation and potential realloc
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    let cap_before = v.capacity();
    // Force a grow so we exercise realloc behavior deterministically.
    v.reserve_exact(cap_before);
    let cap_after = v.capacity();
    kani::assert(cap_after > cap_before, "reserve_exact should grow capacity");
    v.push(2);
    v.push(3);
    kani::assert(v.len() == 3, "vec should have 3 elements");
    kani::assert(v[0] == 1, "v[0] == 1");
    kani::assert(v[1] == 2, "v[1] == 2");
    kani::assert(v[2] == 3, "v[2] == 3");
}

/// Test Vec with_capacity avoids early reallocs.
#[kani::proof]
fn test_vec_with_capacity() {
    let mut v: Vec<i32> = Vec::with_capacity(10);
    kani::assert(v.capacity() >= 10, "capacity should be at least 10");
    kani::assert(v.len() == 0, "should be empty");
    let cap_before = v.capacity();
    v.push(42);
    kani::assert(v.len() == 1, "should have 1 element");
    kani::assert(v[0] == 42, "first element correct");
    kani::assert(v.capacity() == cap_before, "capacity should remain stable within reserved space");
}

/// Test Vec reserve which may realloc.
#[kani::proof]
fn test_vec_reserve() {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    let cap_before = v.capacity();
    v.reserve(100);
    kani::assert(v.capacity() >= 101, "capacity should be at least 101");
    kani::assert(v.capacity() > cap_before, "capacity should grow after reserve");
    kani::assert(v[0] == 1, "existing element preserved after reserve");
}

/// Test Vec shrink_to_fit which may realloc smaller.
#[kani::proof]
fn test_vec_shrink_to_fit() {
    let mut v: Vec<i32> = Vec::with_capacity(100);
    v.push(1);
    v.push(2);
    let cap_before = v.capacity();
    v.shrink_to_fit();
    // After shrink, capacity should be at least len but may be reduced
    kani::assert(v.capacity() >= 2, "capacity should hold elements");
    kani::assert(v.capacity() <= cap_before, "capacity should not increase");
    kani::assert(v[0] == 1, "element 0 preserved");
    kani::assert(v[1] == 2, "element 1 preserved");
}

/// Test Vec pop after 3 pushes with remaining element verification.
#[kani::proof]
fn test_vec_pop_preserve() {
    let mut v: Vec<i32> = Vec::new();
    v.push(10);
    v.push(20);
    v.push(30);
    let popped = v.pop();
    kani::assert(popped.is_some(), "pop should return Some");
    let val = popped.unwrap();
    kani::assert(val == 30, "popped value should be 30");
    kani::assert(v.len() == 2, "len should be 2 after pop");
    kani::assert(v[0] == 10, "v[0] preserved");
    kani::assert(v[1] == 20, "v[1] preserved");
}

/// Test multiple Vec resizes maintain data integrity.
#[kani::proof]
#[kani::unwind(7)]
fn test_vec_multiple_resize() {
    let mut v: Vec<i32> = Vec::new();
    // Trigger multiple potential reallocs
    for i in 0..5 {
        v.push(i);
    }
    kani::assert(v.len() == 5, "should have 5 elements");
    for i in 0..5 {
        kani::assert(v[i] == i as i32, "element should match index");
    }
}

/// Test Vec with symbolic size.
#[kani::proof]
#[kani::unwind(5)]
fn test_vec_symbolic_push() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 3); // Keep bounded for verification

    let mut v: Vec<i32> = Vec::new();
    for i in 0..n {
        v.push(i as i32);
    }
    kani::assert(v.len() == n, "vec should have n elements");

    // Verify all elements match their index
    for i in 0..n {
        kani::assert(v[i] == i as i32, "element should match index");
    }
}
