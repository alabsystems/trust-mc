// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-expect: test_field_projection_through_deref=PROOF
// kani-expect: test_mutable_reference=PROOF
// kani-expect: test_mutable_reference_symbolic=PROOF
// kani-expect: test_reference_deref=PROOF
// kani-expect: test_reference_symbolic=PROOF
// kani-expect: test_struct_field_mutation_through_ref=PROOF
// kani-expect: test_struct_field_through_ref=PROOF
// NOTE: 6 harness(es) UNKNOWN at ay 65537dc81 — reference deref and field
// projection through references produce SolverError or false proof defense
// (BMC cross-check contradiction). 2 harnesses (test_reference_symbolic,
// test_whole_struct_deref_assign) correctly annotated UNKNOWN.
//
//! Integration tests for pointer operations (#356).
//!
//! Tests reference creation, dereference, and field projection
//! through the full trust_mc/AY verification pipeline.

/// Test basic reference creation and dereference.
#[kani::proof]
fn test_reference_deref() {
    let x: i32 = 42;
    let r: &i32 = &x;
    kani::assert(*r == 42, "dereferenced reference should equal original value");
}

/// Test mutable reference modification.
#[kani::proof]
fn test_mutable_reference() {
    let mut x: i32 = 10;
    let r: &mut i32 = &mut x;
    *r = 20;
    kani::assert(x == 20, "value should be modified through mutable reference");
}

/// Test reference with symbolic value.
#[kani::proof]
fn test_reference_symbolic() {
    let x: i32 = kani::any();
    kani::assume(x > 0);
    let r: &i32 = &x;
    kani::assert(*r > 0, "dereferenced symbolic should satisfy constraint");
}

/// Test mutable reference with symbolic value.
#[kani::proof]
fn test_mutable_reference_symbolic() {
    let mut x: i32 = kani::any();
    kani::assume(x == 5);
    let r: &mut i32 = &mut x;
    *r = *r + 10;
    kani::assert(x == 15, "symbolic value modified through reference");
}

/// Simple struct for field projection tests.
struct Point {
    x: i32,
    y: i32,
}

/// Test field access through reference.
#[kani::proof]
fn test_struct_field_through_ref() {
    let p = Point { x: 10, y: 20 };
    let r: &Point = &p;
    kani::assert(r.x == 10, "field x through reference should be 10");
    kani::assert(r.y == 20, "field y through reference should be 20");
}

/// Test mutable field modification through reference.
#[kani::proof]
fn test_struct_field_mutation_through_ref() {
    let mut p = Point { x: 10, y: 20 };
    let r: &mut Point = &mut p;
    r.x = 100;
    kani::assert(p.x == 100, "field x should be modified through reference");
    kani::assert(p.y == 20, "field y should be unchanged");
}

/// Test nested reference dereference pattern (*ptr).field.
#[kani::proof]
fn test_field_projection_through_deref() {
    let mut p = Point { x: 5, y: 15 };
    let r: &mut Point = &mut p;
    // Explicit (*r).field pattern
    (*r).x = 50;
    (*r).y = 150;
    kani::assert(p.x == 50, "(*r).x should update p.x");
    kani::assert(p.y == 150, "(*r).y should update p.y");
}

/// Test whole struct assignment through deref (*r = new_value).
/// This tests pure deref assignment without field projection.
#[kani::proof]
fn test_whole_struct_deref_assign() {
    let mut p = Point { x: 1, y: 2 };
    let r: &mut Point = &mut p;
    // Assign entire struct through reference
    *r = Point { x: 100, y: 200 };
    kani::assert(p.x == 100, "whole struct deref assign should update x");
    kani::assert(p.y == 200, "whole struct deref assign should update y");
}
