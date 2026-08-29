// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN

//! Diagnostic: minimal Vec<bool> IndexMut test to isolate #3348 encoding gap.
//! If PROOF: struct-embedded path is the blocker.
//! If CTREX: bare Vec IndexMut is the blocker.

/// Bare Vec<bool>: write then read
#[kani::proof]
fn vec_bool_write_read() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let idx: usize = kani::any();
    kani::assume(idx < n);

    let mut v: Vec<bool> = vec![false; n];
    assert!(!v[idx]); // should be false from const_array
    v[idx] = true;
    assert!(v[idx]); // should be true after store
}

/// Bare Vec<bool>: write preserves other elements
#[kani::proof]
fn vec_bool_write_isolation() {
    let n: usize = kani::any();
    kani::assume(n >= 2 && n <= 10);
    let i: usize = kani::any();
    let j: usize = kani::any();
    kani::assume(i < n && j < n);
    kani::assume(i != j);

    let mut v: Vec<bool> = vec![false; n];
    v[i] = true;
    assert!(v[i]);
    assert!(!v[j]); // j != i, should still be false
}

/// Struct-embedded Vec<bool>: write then read (mirrors SeenMarks)
struct Marks {
    data: Vec<bool>,
}

impl Marks {
    fn new(n: usize) -> Self {
        Self { data: vec![false; n] }
    }
}

#[kani::proof]
fn struct_vec_bool_write_read() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let idx: usize = kani::any();
    kani::assume(idx < n);

    let mut m = Marks::new(n);
    assert!(!m.data[idx]);
    m.data[idx] = true;
    assert!(m.data[idx]);
}
