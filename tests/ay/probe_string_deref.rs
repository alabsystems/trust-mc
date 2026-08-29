// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: UNKNOWN

//! Probe: different ways to get &mut str from String.
//! Part of #4163 — isolate whether get_mut or deref is the issue.

#[kani::proof]
fn probe_string_deref_len() {
    let buf = String::from("000");
    let s: &str = &buf;
    assert_eq!(s.len(), 3);
}

#[kani::proof]
fn probe_string_as_str_len() {
    let buf = String::from("000");
    assert_eq!(buf.as_str().len(), 3);
}

#[kani::proof]
fn probe_string_as_mut_str_len() {
    let mut buf = String::from("000");
    let s: &mut str = buf.as_mut_str();
    assert_eq!(s.len(), 3);
}

#[kani::proof]
fn probe_string_get_mut_len() {
    let mut buf = String::from("000");
    let s = buf.get_mut(..).unwrap();
    assert_eq!(s.len(), 3);
}
