// kani-expect: PROOF
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(ptr_metadata)]

include!("../trust_mc/Helpers/vtable_utils_ignore.rs");

fn check_size(fun: &dyn Fn() -> i32) {
    assert!(size_from_vtable(vtable!(fun)) == 8);
}

#[kani::proof]
fn main() {
    let a = vec![3];
    let closure = || a[0] + 2;
    check_size(&closure);
}
