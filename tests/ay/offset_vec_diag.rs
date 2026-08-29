// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF
//! Diagnostic: isolate offset_non_power_two CTREX root cause.
//! Tests ptr.add + offset_from_unsigned on Vec<[u64; 3]> with concrete offset.

#[kani::proof]
fn offset_vec_diag() {
    let mut v = vec![[0u64; 3], [2u64; 3]];
    unsafe {
        let begin = v.as_mut_ptr();
        let end = begin.add(1);
        assert_eq!(end.offset_from_unsigned(begin), 1);
    }
}
