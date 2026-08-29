// Test file for debugging #948 - multiple struct types in single harness
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: test_single_struct was PROOF at ay 417854b7, regressed to ERROR at ay 8a4a9bcc2,
// recovered to PROOF at ay 65537dc81. test_two_structs_simple remains UNKNOWN.

#[derive(Clone, Copy)]
struct Variable(u32);

#[derive(Clone, Copy)]
struct Literal(u32);

// This should work - single struct type
#[kani::proof]
fn test_single_struct() {
    let x: u32 = kani::any();
    kani::assume(x < 100);
    let v = Variable(x);
    assert!(v.0 == x);
}

// This fails - multiple struct types
#[kani::proof]
fn test_two_structs_simple() {
    let x: u32 = kani::any();
    kani::assume(x < 100);
    let v = Variable(x);
    let lit = Literal(x * 2);
    assert!(lit.0 == x * 2);
    assert!(v.0 == x);
}
