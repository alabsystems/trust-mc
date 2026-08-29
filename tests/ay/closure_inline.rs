// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// kani-flags: --ay-chc-track=mem
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Test closure inlining support (#1575).
//
// Tests that closures (FnOnce/FnMut/Fn) are properly inlined by the
// FunctionInlinePass. This is part of Phase 4 Milestone 2.

/// Test simple non-capturing closure inlining.
///
/// This is the simplest closure case - just returns a constant.
#[kani::proof]
fn test_simple_closure() {
    let get_five = || 5i32;
    let result = get_five();
    kani::assert(result == 5, "simple closure returns constant");
}

/// Test identity closure - returns its argument unchanged.
#[kani::proof]
fn test_identity_closure() {
    let identity = |n: i32| n;
    let result = identity(42);
    kani::assert(result == 42, "identity closure");
}

/// Test capturing closure - captures variable by shared reference.
///
/// Design doc test case from designs/2026-02-01-phase4-critical-path-integration.md:131-137
/// Note: Without `move`, the closure captures `x` by reference (&x).
/// This allows multiple calls and the original `x` remains accessible.
#[kani::proof]
fn test_capturing_closure() {
    let x = 5i32;
    let add_x = |n: i32| n + x; // Captures x by reference (&x)
    kani::assert(add_x(1) == 6, "closure captures x by reference");
    kani::assert(add_x(2) == 7, "can call multiple times (borrow)");
    kani::assert(x == 5, "original x still accessible");
}

/// Test closure that captures by value using `move`.
///
/// With `move`, the closure takes ownership of captured variables.
/// This is explicit capture-by-value semantics.
#[kani::proof]
fn test_value_capturing_closure() {
    let captured = 10i32;
    let add_captured = move |n: i32| n + captured; // move captures by value
    kani::assert(add_captured(5) == 15, "move closure captures by value");
}

/// Test FnMut closure that mutates captured state.
///
/// This tests that closures requiring mutable capture work correctly.
/// The closure is FnMut because it modifies `counter`.
#[kani::proof]
fn test_fnmut_closure() {
    let mut counter = 0i32;
    let mut increment = || {
        counter += 1;
        counter
    };
    let first = increment();
    let second = increment();
    kani::assert(first == 1, "first increment");
    kani::assert(second == 2, "second increment");
}

/// Test FnOnce closure that moves captured value.
///
/// This tests closures that can only be called once because they
/// consume their captured environment. These are FnOnce-only.
#[kani::proof]
fn test_fnonce_move_closure() {
    let value = 42i32;
    // `move` forces the closure to take ownership of `value`
    let consume_value = move || value;
    let result = consume_value();
    // Can't call consume_value() again - it consumed the captured value
    kani::assert(result == 42, "move closure returns captured value");
}

/// Test closure with multiple arguments.
///
/// This tests that closures with more than one parameter are
/// properly inlined with all arguments handled correctly.
#[kani::proof]
fn test_multi_arg_closure() {
    let add = |a: i32, b: i32| a + b;
    let result = add(3, 4);
    kani::assert(result == 7, "multi-arg closure adds correctly");
}

/// Test closure with multiple arguments and captured state.
///
/// Combines multi-argument closures with environment capture.
#[kani::proof]
fn test_multi_arg_capturing_closure() {
    let offset = 100i32;
    let add_offset = |a: i32, b: i32| a + b + offset;
    let result = add_offset(5, 10);
    kani::assert(result == 115, "multi-arg closure with capture");
}
