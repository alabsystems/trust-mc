// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN

//! Diagnostic: struct with two Vec fields, method-based access.
//! Isolates whether dual-Vec struct methods break IndexMut encoding.

struct TwoVecs {
    marks: Vec<bool>,
    trail: Vec<usize>,
}

impl TwoVecs {
    fn new(n: usize) -> Self {
        Self { marks: vec![false; n], trail: Vec::new() }
    }

    fn mark(&mut self, var: usize) {
        if var < self.marks.len() && !self.marks[var] {
            self.marks[var] = true;
            self.trail.push(var);
        }
    }

    fn is_marked(&self, var: usize) -> bool {
        var < self.marks.len() && self.marks[var]
    }
}

/// Two-Vec struct with method mark + check
#[kani::proof]
fn dual_vec_mark_then_check() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let var: usize = kani::any();
    kani::assume(var < n);

    let mut tv = TwoVecs::new(n);
    assert!(!tv.is_marked(var));
    tv.mark(var);
    assert!(tv.is_marked(var));
}

/// Simpler: only test marks vec (ignore trail push)
struct OneVecMethod {
    marks: Vec<bool>,
}

impl OneVecMethod {
    fn new(n: usize) -> Self {
        Self { marks: vec![false; n] }
    }

    fn mark(&mut self, var: usize) {
        if var < self.marks.len() {
            self.marks[var] = true;
        }
    }

    fn is_marked(&self, var: usize) -> bool {
        var < self.marks.len() && self.marks[var]
    }
}

/// One-Vec struct with method mark + check
#[kani::proof]
fn one_vec_method_mark_check() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let var: usize = kani::any();
    kani::assume(var < n);

    let mut m = OneVecMethod::new(n);
    m.mark(var);
    assert!(m.is_marked(var));
}

/// Direct field access on dual-vec struct (no methods)
#[kani::proof]
fn dual_vec_direct_access() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let var: usize = kani::any();
    kani::assume(var < n);

    let mut tv = TwoVecs::new(n);
    tv.marks[var] = true;
    assert!(tv.marks[var]);
}
