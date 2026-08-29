// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN

//! Minimal diagnostic: isolate method-based Vec write encoding.

struct W {
    v: Vec<bool>,
}

impl W {
    fn new(n: usize) -> Self {
        Self { v: vec![false; n] }
    }

    fn set(&mut self, i: usize) {
        self.v[i] = true;
    }

    fn get(&self, i: usize) -> bool {
        self.v[i]
    }
}

/// Simplest: method set, then direct read
#[kani::proof]
fn method_set_direct_read() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 5);
    let i: usize = kani::any();
    kani::assume(i < n);

    let mut w = W::new(n);
    w.set(i);
    assert!(w.v[i]); // direct field access for read
}

/// Method set, method read
#[kani::proof]
fn method_set_method_read() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 5);
    let i: usize = kani::any();
    kani::assume(i < n);

    let mut w = W::new(n);
    w.set(i);
    assert!(w.get(i));
}

/// Direct set, method read
#[kani::proof]
fn direct_set_method_read() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 5);
    let i: usize = kani::any();
    kani::assume(i < n);

    let mut w = W::new(n);
    w.v[i] = true;
    assert!(w.get(i));
}

/// Direct set, direct read (baseline - should PROOF)
#[kani::proof]
fn direct_set_direct_read() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 5);
    let i: usize = kani::any();
    kani::assume(i < n);

    let mut w = W::new(n);
    w.v[i] = true;
    assert!(w.v[i]);
}
