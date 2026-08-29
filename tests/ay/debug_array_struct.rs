// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --ay-chc-track=mem
// kani-expect: PROOF
//
//! Diagnostic test for struct array encoding. Part of #2970.

struct Pair {
    a: i32,
    b: i32,
}

/// Test: can we read back struct fields from an initialized array?
#[kani::proof]
fn test_struct_array_init_read() {
    let arr: [Pair; 2] = [Pair { a: 1, b: 2 }, Pair { a: 3, b: 4 }];
    kani::assert(arr[0].a == 1, "arr[0].a == 1");
    kani::assert(arr[0].b == 2, "arr[0].b == 2");
    kani::assert(arr[1].a == 3, "arr[1].a == 3");
    kani::assert(arr[1].b == 4, "arr[1].b == 4");
}

/// Test: after mutating arr[0].a, does arr[1].b survive?
#[kani::proof]
fn test_struct_array_mutate_field() {
    let mut arr: [Pair; 2] = [Pair { a: 1, b: 2 }, Pair { a: 3, b: 4 }];
    arr[0].a = 100;
    kani::assert(arr[1].b == 4, "arr[1].b == 4 after arr[0].a mutation");
}
