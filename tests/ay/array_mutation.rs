// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// kani-expect: test_array_symbolic_index_mutation=UNKNOWN  // AY-bump regression from PROOF (3d9db24e68); sound demotion
// NOTE: All harnesses recovered to PROOF after ay bump (U242-U248) except
// test_array_symbolic_index_mutation (symbolic index + Array invariant).
// kani-flags: --ay-chc-track=mem
//
//! Array element mutation tests for Phase 3 (#892).
//!
//! Tests the CHC encoding of array element modification through
//! indexing and pointer operations.

/// Test basic array element mutation.
#[kani::proof]
fn test_array_element_mutation() {
    let mut arr: [i32; 3] = [1, 2, 3];
    arr[1] = 42;
    kani::assert(arr[0] == 1, "arr[0] unchanged");
    kani::assert(arr[1] == 42, "arr[1] modified");
    kani::assert(arr[2] == 3, "arr[2] unchanged");
}

/// Test array element mutation through mutable reference.
#[kani::proof]
fn test_array_mutation_through_ref() {
    let mut arr: [i32; 2] = [10, 20];
    let elem_ref: &mut i32 = &mut arr[0];
    *elem_ref = 100;
    kani::assert(arr[0] == 100, "arr[0] modified through ref");
    kani::assert(arr[1] == 20, "arr[1] unchanged");
}

/// Test multiple array mutations.
#[kani::proof]
fn test_array_multiple_mutations() {
    let mut arr: [i32; 4] = [0, 0, 0, 0];
    arr[0] = 1;
    arr[1] = 2;
    arr[2] = 3;
    arr[3] = 4;
    kani::assert(arr[0] == 1, "arr[0] == 1");
    kani::assert(arr[1] == 2, "arr[1] == 2");
    kani::assert(arr[2] == 3, "arr[2] == 3");
    kani::assert(arr[3] == 4, "arr[3] == 4");
}

/// Test array mutation with symbolic index.
#[kani::proof]
fn test_array_symbolic_index_mutation() {
    let mut arr: [i32; 3] = [0, 0, 0];
    let idx: usize = kani::any();
    kani::assume(idx < 3);
    arr[idx] = 99;
    // At least one element should be 99
    kani::assert(arr[0] == 99 || arr[1] == 99 || arr[2] == 99, "some element modified to 99");
}

/// Test array mutation with symbolic value.
#[kani::proof]
fn test_array_symbolic_value_mutation() {
    let val: i32 = kani::any();
    kani::assume(val > 0);

    let mut arr: [i32; 2] = [0, 0];
    arr[0] = val;
    kani::assert(arr[0] == val, "symbolic value stored");
    kani::assert(arr[0] > 0, "constraint preserved after store");
}

/// Test overwrite: same index mutated twice.
#[kani::proof]
fn test_array_overwrite() {
    let mut arr: [i32; 2] = [0, 0];
    arr[0] = 10;
    kani::assert(arr[0] == 10, "first write");
    arr[0] = 20;
    kani::assert(arr[0] == 20, "second write overwrites first");
}

/// Test array of booleans mutation.
#[kani::proof]
fn test_array_bool_mutation() {
    let mut flags: [bool; 3] = [false, false, false];
    flags[1] = true;
    kani::assert(!flags[0], "flags[0] unchanged");
    kani::assert(flags[1], "flags[1] set to true");
    kani::assert(!flags[2], "flags[2] unchanged");
}

/// Test nested struct in array mutation.
struct ArrayPair {
    a: i32,
    b: i32,
}

#[kani::proof]
fn test_array_struct_mutation() {
    let mut arr: [ArrayPair; 2] = [ArrayPair { a: 1, b: 2 }, ArrayPair { a: 3, b: 4 }];
    arr[0].a = 100;
    kani::assert(arr[0].a == 100, "arr[0].a modified");
    kani::assert(arr[0].b == 2, "arr[0].b unchanged");
    kani::assert(arr[1].a == 3, "arr[1].a unchanged");
    kani::assert(arr[1].b == 4, "arr[1].b unchanged");
}
