// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-expect: array_struct_field_u32=PROOF
// kani-expect: array_struct_field_u64=PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).

// Tests BV field extraction from flattened struct arrays.
// Uses kani::assert (not assert_eq!) to avoid reference creation
// and test the value-path encoding directly.

#[derive(Copy, Clone)]
struct Pair {
    x: u32,
    y: u64,
}

#[kani::proof]
fn array_struct_field_u32() {
    let a = [Pair { x: 42, y: 100 }; 4];
    let i: usize = kani::any();
    kani::assume(i < 4);
    let elem = a[i];
    kani::assert(elem.x == 42, "x field should be 42");
}

#[kani::proof]
fn array_struct_field_u64() {
    let a = [Pair { x: 42, y: 100 }; 4];
    let i: usize = kani::any();
    kani::assume(i < 4);
    let elem = a[i];
    kani::assert(elem.y == 100, "y field should be 100");
}

// Struct with enum field (Option<u16>) — tests multi-leaf BV span extraction
#[derive(Copy, Clone)]
struct WithOption {
    a: u8,
    b: u32,
    c: Option<u16>,
}

#[kani::proof]
fn array_struct_scalar_field_with_enum_sibling() {
    let v = WithOption { a: 7, b: 99, c: Some(42) };
    let a = [v; 3];
    let i: usize = kani::any();
    kani::assume(i < 3);
    let elem = a[i];
    kani::assert(elem.a == 7, "a field should be 7");
    kani::assert(elem.b == 99, "b field should be 99");
}
