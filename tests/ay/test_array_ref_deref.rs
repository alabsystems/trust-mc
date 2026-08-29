// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-expect: test_ref_array_element_constant_index=PROOF
// kani-expect: test_ref_array_element_deref_chain=PROOF
// kani-expect: test_ref_array_element_field=PROOF
// kani-expect: test_ref_array_element_field_mut=PROOF
// kani-expect: test_ref_array_element_mut=PROOF
// kani-expect: test_ref_array_nested_field=PROOF
// kani-expect: test_ref_array_symbolic_index=PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).
//
//! CHC regression tests for `&arr[idx]` and `&arr[idx].field` deref resolution.
//!
//! Part of #1739: Tests the RefTarget projection handling for Index and
//! ConstantIndex projections in deref chains.
//!
//! Related commits:
//! - 78c8df65: Updated RefTarget deref resolution to handle Index/ConstantIndex

/// Test `&arr[idx]` - reference to array element with constant index.
/// This tests ConstantIndex projection in RefTarget resolution.
#[kani::proof]
fn test_ref_array_element_constant_index() {
    let arr: [i32; 3] = [10, 20, 30];
    let elem_ref: &i32 = &arr[1];
    kani::assert(*elem_ref == 20, "&arr[1] should dereference to 20");
}

/// Test `&arr[idx]` - reference to array element with mutable modification.
#[kani::proof]
fn test_ref_array_element_mut() {
    let mut arr: [i32; 2] = [100, 200];
    let elem_ref: &mut i32 = &mut arr[0];
    *elem_ref = 999;
    kani::assert(arr[0] == 999, "mutation through &mut arr[0] should work");
    kani::assert(arr[1] == 200, "arr[1] should be unchanged");
}

/// Test `&arr[idx].field` - reference to field of array element.
/// This tests Field projection after Index projection in RefTarget resolution.
struct Point {
    x: i32,
    y: i32,
}

#[kani::proof]
fn test_ref_array_element_field() {
    let arr: [Point; 2] = [Point { x: 1, y: 2 }, Point { x: 3, y: 4 }];
    let x_ref: &i32 = &arr[0].x;
    let y_ref: &i32 = &arr[1].y;
    kani::assert(*x_ref == 1, "&arr[0].x should dereference to 1");
    kani::assert(*y_ref == 4, "&arr[1].y should dereference to 4");
}

/// Test `&mut arr[idx].field` - mutable reference to field of array element.
#[kani::proof]
fn test_ref_array_element_field_mut() {
    let mut arr: [Point; 2] = [Point { x: 10, y: 20 }, Point { x: 30, y: 40 }];
    let x_ref: &mut i32 = &mut arr[0].x;
    *x_ref = 100;
    kani::assert(arr[0].x == 100, "mutation through &mut arr[0].x should work");
    kani::assert(arr[0].y == 20, "arr[0].y should be unchanged");
    kani::assert(arr[1].x == 30, "arr[1].x should be unchanged");
}

/// Test chained deref: `let r = &arr[0]; let v = *r;`
#[kani::proof]
fn test_ref_array_element_deref_chain() {
    let arr: [u8; 4] = [1, 2, 3, 4];
    let r: &u8 = &arr[2];
    let v: u8 = *r;
    kani::assert(v == 3, "chained deref should yield arr[2]");
}

/// Test nested struct field access: `&arr[idx].inner.field`
struct Outer {
    inner: Point,
    value: i32,
}

#[kani::proof]
fn test_ref_array_nested_field() {
    let arr: [Outer; 2] = [
        Outer { inner: Point { x: 5, y: 6 }, value: 100 },
        Outer { inner: Point { x: 7, y: 8 }, value: 200 },
    ];
    let inner_x: &i32 = &arr[0].inner.x;
    let inner_y: &i32 = &arr[1].inner.y;
    kani::assert(*inner_x == 5, "&arr[0].inner.x should be 5");
    kani::assert(*inner_y == 8, "&arr[1].inner.y should be 8");
}

/// Test symbolic index: `&arr[idx]` where idx is symbolic.
/// This tests Index projection (not ConstantIndex) in RefTarget resolution.
#[kani::proof]
fn test_ref_array_symbolic_index() {
    let arr: [i32; 3] = [111, 222, 333];
    let idx: usize = kani::any();
    kani::assume(idx < 3);
    let elem_ref: &i32 = &arr[idx];
    // The value must be one of the array elements
    kani::assert(
        *elem_ref == 111 || *elem_ref == 222 || *elem_ref == 333,
        "&arr[symbolic_idx] should be valid element",
    );
}

/// Test mutable modification through symbolic index reference.
#[kani::proof]
fn test_ref_array_symbolic_index_mut() {
    let mut arr: [i32; 2] = [0, 0];
    let idx: usize = kani::any();
    kani::assume(idx < 2);
    let elem_ref: &mut i32 = &mut arr[idx];
    *elem_ref = 42;
    // At least one element should be 42
    kani::assert(arr[0] == 42 || arr[1] == 42, "some element should be 42");
}
