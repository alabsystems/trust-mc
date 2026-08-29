// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
// kani-verify-pass
//
//! Regression test for deref chain codegen (#869).
//!
//! Tests that `ensure_ref_pointee_for_place` correctly derives ref_pointees
//! mappings for complex deref chains like `**r` where `r: &&T`.
//!
//! Tests ref-pointee deref chain correctness.

/// Test deref chain: &&T -> **r path.
///
/// Creates a reference-to-reference and verifies double dereference works.
#[kani::proof]
fn ay_deref_chain_double_ref() {
    let value: u32 = 42;
    let ref_to_value: &u32 = &value;
    let ref_to_ref: &&u32 = &ref_to_value;

    // Double dereference: **r
    let result = **ref_to_ref;
    assert_eq!(result, 42);
}

/// Test deref + field: (*r).field path.
///
/// Creates a reference to a struct and dereferences to access a field.
#[kani::proof]
fn ay_deref_chain_struct_field() {
    struct Point {
        x: u32,
        y: u32,
    }

    let point = Point { x: 10, y: 20 };
    let ref_to_point: &Point = &point;

    // Deref + field: (*r).x
    let x_val = (*ref_to_point).x;
    let y_val = (*ref_to_point).y;

    assert_eq!(x_val, point.x);
    assert_eq!(y_val, point.y);
}

/// Test nested deref: (*(*r).inner).val path.
///
/// Creates a more complex chain with nested references.
#[kani::proof]
fn ay_deref_chain_nested() {
    struct Inner {
        val: u32,
    }

    struct Outer<'a> {
        inner: &'a Inner,
    }

    let inner = Inner { val: 100 };
    let outer = Outer { inner: &inner };
    let ref_to_outer: &Outer = &outer;

    // Access nested field through reference + reference field
    let val = (*(*ref_to_outer).inner).val;
    assert_eq!(val, inner.val);
}
