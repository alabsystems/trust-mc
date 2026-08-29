// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: PROOF

/// Test 1: Function returns modified scalar field — does this work?
struct Simple { x: u32, y: u32 }

fn make_simple() -> Simple {
    let mut s = Simple { x: 0, y: 0 };
    s.x = 42;
    s
}

#[kani::proof]
fn proof_simple_return() {
    let s = make_simple();
    assert!(s.x == 42, "x is 42");
}

/// Test 2: Function returns struct with modified array
struct WithArray { vals: [u32; 4], len: usize }

fn make_with_array() -> WithArray {
    let mut w = WithArray { vals: [0; 4], len: 0 };
    w.vals[0] = 42;
    w.len = 1;
    w
}

#[kani::proof]
fn proof_array_return() {
    let w = make_with_array();
    assert!(w.vals[0] == 42, "vals[0] is 42");
    assert!(w.len == 1, "len is 1");
}

/// Test 3: Method (impl) returns struct with modified array
impl WithArray {
    fn new_1(v0: u32) -> Self {
        let mut w = Self { vals: [0; 4], len: 0 };
        w.vals[0] = v0;
        w.len = 1;
        w
    }
}

#[kani::proof]
fn proof_method_return() {
    let w = WithArray::new_1(42);
    assert!(w.vals[0] == 42, "vals[0] is 42");
    assert!(w.len == 1, "len is 1");
}
