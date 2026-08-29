// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
//! Smoke tests for tuple datatype codegen (#142).

#[kani::proof]
fn test_tuple_fields_smoke() {
    let t: (u32, bool) = (5, true);
    kani::assert(t.0 == 5, "tuple .0 field should be 5");
    kani::assert(t.1, "tuple .1 field should be true");
}

#[kani::proof]
fn test_nested_tuple_fields_smoke() {
    let t: ((u32, bool), u8) = ((5, true), 7);
    kani::assert((t.0).0 == 5, "nested tuple (t.0).0 field should be 5");
    kani::assert((t.0).1, "nested tuple (t.0).1 field should be true");
    kani::assert(t.1 == 7, "tuple .1 field should be 7");
}

#[kani::proof]
fn test_tuple_field_mutation_smoke() {
    let mut t: (u32, bool) = (5, true);
    t.0 = 9;
    kani::assert(t.0 == 9, "tuple .0 field should be updated");
    kani::assert(t.1, "tuple .1 field should be preserved");
}

#[kani::proof]
fn test_nested_tuple_field_mutation_smoke() {
    let mut t: ((u32, bool), u8) = ((5, true), 7);
    t.0.0 = 9;
    t.1 = 8;
    kani::assert((t.0).0 == 9, "nested tuple (t.0).0 field should be updated");
    kani::assert((t.0).1, "nested tuple (t.0).1 field should be preserved");
    kani::assert(t.1 == 8, "tuple .1 field should be updated");
}
