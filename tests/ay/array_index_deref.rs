// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: All harnesses recovered to PROOF after ay bump (U242-U248) except
// test_ref_to_array_elem_symbolic_idx (symbolic index + Array invariant).
//
//! Regression tests for array index deref resolution (#1739).
//!
//! Tests `&arr[idx]` and `&arr[idx].field` patterns through CHC
//! deref resolution path. Verifies RefTarget tracking of Index and
//! ConstantIndex projections.
//!
//! Added by [P]11 per commit 78c8df65 request.

/// Test reference to array element with constant index.
///
/// Pattern: `&arr[0]` - creates reference to array element.
#[kani::proof]
fn test_ref_to_array_elem_const_idx() {
    let arr: [i32; 3] = [10, 20, 30];
    let elem_ref: &i32 = &arr[1];
    kani::assert(*elem_ref == 20, "deref of &arr[1] should be 20");
}

/// Test reference to array element with symbolic index.
///
/// Pattern: `&arr[idx]` where idx is symbolic.
#[kani::proof]
fn test_ref_to_array_elem_symbolic_idx() {
    let arr: [i32; 4] = [1, 2, 3, 4];
    let idx: usize = kani::any();
    kani::assume(idx < 4);

    let elem_ref: &i32 = &arr[idx];
    // The dereferenced value must be one of the array elements
    kani::assert(
        *elem_ref == 1 || *elem_ref == 2 || *elem_ref == 3 || *elem_ref == 4,
        "deref of &arr[idx] should be an array element",
    );
}

/// Test reference to field of array element with constant index.
///
/// Pattern: `&arr[0].field` - creates reference to struct field in array element.
#[kani::proof]
fn test_ref_to_array_elem_field_const_idx() {
    struct Pair {
        x: i32,
        y: i32,
    }

    let arr: [Pair; 2] = [Pair { x: 10, y: 20 }, Pair { x: 30, y: 40 }];
    let x_ref: &i32 = &arr[0].x;
    let y_ref: &i32 = &arr[1].y;

    kani::assert(*x_ref == 10, "deref of &arr[0].x should be 10");
    kani::assert(*y_ref == 40, "deref of &arr[1].y should be 40");
}

/// Test reference to field of array element with symbolic index.
///
/// Pattern: `&arr[idx].field` where idx is symbolic.
#[kani::proof]
fn test_ref_to_array_elem_field_symbolic_idx() {
    struct Point {
        a: i32,
        b: i32,
    }

    let arr: [Point; 3] = [
        Point { a: 1, b: 10 },
        Point { a: 2, b: 20 },
        Point { a: 3, b: 30 },
    ];
    let idx: usize = kani::any();
    kani::assume(idx < 3);

    let a_ref: &i32 = &arr[idx].a;
    // The field must be one of the 'a' values
    kani::assert(*a_ref == 1 || *a_ref == 2 || *a_ref == 3, "deref of &arr[idx].a");
}

/// Test mutable reference to array element mutation.
///
/// Pattern: `&mut arr[idx]` - mutable reference to array element.
#[kani::proof]
fn test_mut_ref_to_array_elem() {
    let mut arr: [i32; 3] = [100, 200, 300];
    let elem_ref: &mut i32 = &mut arr[1];
    *elem_ref = 999;

    kani::assert(arr[0] == 100, "arr[0] unchanged");
    kani::assert(arr[1] == 999, "arr[1] modified via &mut arr[1]");
    kani::assert(arr[2] == 300, "arr[2] unchanged");
}

/// Test mutable reference to field of array element.
///
/// Pattern: `&mut arr[idx].field` - mutable reference to struct field.
#[kani::proof]
fn test_mut_ref_to_array_elem_field() {
    struct Data {
        val: i32,
        flag: bool,
    }

    let mut arr: [Data; 2] = [Data { val: 1, flag: false }, Data { val: 2, flag: false }];
    let flag_ref: &mut bool = &mut arr[0].flag;
    *flag_ref = true;

    kani::assert(arr[0].val == 1, "arr[0].val unchanged");
    kani::assert(arr[0].flag, "arr[0].flag modified via &mut arr[0].flag");
    kani::assert(arr[1].val == 2, "arr[1].val unchanged");
    kani::assert(!arr[1].flag, "arr[1].flag unchanged");
}

/// Test chained array index: arr[i][j] pattern.
///
/// Pattern: `&arr[i][j]` - nested array access.
#[kani::proof]
fn test_ref_to_nested_array() {
    let arr: [[i32; 2]; 2] = [[1, 2], [3, 4]];
    let elem_ref: &i32 = &arr[1][0];

    kani::assert(*elem_ref == 3, "deref of &arr[1][0] should be 3");
}

/// Test intermediate reference: let r = &arr; r[idx] pattern.
///
/// Pattern: Creates reference to array, then indexes through it.
#[kani::proof]
fn test_index_through_array_ref() {
    let arr: [i32; 3] = [5, 10, 15];
    let arr_ref: &[i32; 3] = &arr;
    let elem = arr_ref[1];

    kani::assert(elem == 10, "arr_ref[1] should be 10");
}
