// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: test_addressof_cross_branch_nonnull gained PROOF at ay 8a4a9bcc2.
// kani-flags: --ay-chc-track=mem
//
//! Passing tests for AddressOf stability across blocks.
//!
//! These tests verify address equality across control-flow blocks.
//! Fixed by #1124: AddressOf(*ref) now resolves through ref_pointees
//! to get stable address symbols for the same underlying local.
//!
//! These harnesses require mem-level CHC tracking so address identity is
//! modeled independently from per-assignment SSA value expressions.
//!
//! Stable address aliasing model.

/// Test address non-null across if-else branches.
/// Taking &x in both branches should yield a non-null address.
#[kani::proof]
fn test_addressof_cross_branch_nonnull() {
    let cond: bool = kani::any();
    let x: i32 = 42;

    let addr: *const i32;
    if cond {
        addr = &x as *const i32;
    } else {
        addr = &x as *const i32;
    }

    // Address should be non-null regardless of branch
    kani::assert(!addr.is_null(), "address should be non-null");
}

/// Test address stability with symbolic condition - the address of x
/// should be the same regardless of which branch was taken.
/// Fixed by #1124: AddressOf(*ref) resolution through ref_pointees.
#[kani::proof]
fn test_addressof_stable_symbol() {
    let cond: bool = kani::any();
    let x: i32 = kani::any();

    // Take address in if branch
    let addr1: *const i32 = if cond {
        &x as *const i32
    } else {
        // This should be the SAME address as the if branch
        &x as *const i32
    };

    // Take address again unconditionally
    let addr2: *const i32 = &x as *const i32;

    // Both addresses must be equal - fixed by #1124
    kani::assert(addr1 == addr2, "address symbols should be stable across branches");
}

/// Test address stability across sequential blocks.
/// Address should remain the same across basic block boundaries.
/// Fixed by #1124: AddressOf(*ref) resolution through ref_pointees.
#[kani::proof]
fn test_addressof_sequential_blocks() {
    let mut x: i32 = 0;

    // Block 1
    x = 10;
    let addr1: *const i32 = &x as *const i32;

    // Block 2 (after unconditional assignment)
    x = 20;
    let addr2: *const i32 = &x as *const i32;

    // Block 3
    x = 30;
    let addr3: *const i32 = &x as *const i32;

    // All addresses should be the same place - fixed by #1124
    kani::assert(addr1 == addr2, "addr1 == addr2 after SSA version change");
    kani::assert(addr2 == addr3, "addr2 == addr3 after SSA version change");
}
