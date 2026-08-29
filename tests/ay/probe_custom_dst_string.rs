// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: UNKNOWN

//! Probe: isolate size_of_val with String-derived custom DST.
//! Part of #4163 — test the String → get_mut → raw_parts → cast chain.

use std::mem::size_of_val;

struct MyStr {
    header_0: u8,
    header_1: u8,
    data: str,
}

impl MyStr {
    fn new(original: &mut String) -> &mut Self {
        let buf = original.get_mut(..).unwrap();
        assert!(size_of_val(buf) > 2, "This requires at least 2 bytes");
        let unsized_len = buf.len() - 2;
        let ptr = std::ptr::slice_from_raw_parts_mut(buf.as_mut_ptr(), unsized_len);
        unsafe { &mut *(ptr as *mut Self) }
    }
}

#[kani::proof]
fn probe_mystr_single_size() {
    let mut buf = String::from("000");
    let my_str = MyStr::new(&mut buf);
    // MyStr { header_0: u8(1), header_1: u8(1), data: str(1 byte) } = 3
    assert_eq!(size_of_val(my_str), 3);
}
