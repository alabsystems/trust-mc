// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
//! Diagnostic: symbolic offset via any() + assume() (no any_where).

#[kani::proof]
fn offset_vec_symbolic() {
    let mut v = vec![[0u64; 3], [2u64; 3]];
    let offset: usize = kani::any();
    kani::assume(offset <= v.len());
    unsafe {
        let begin = v.as_mut_ptr();
        let end = begin.add(offset);
        assert_eq!(end.offset_from_unsigned(begin), offset);
    }
}
