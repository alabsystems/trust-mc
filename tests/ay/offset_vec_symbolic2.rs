// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
//! Diagnostic: any_where with Vec<[u64; 3]> — isolate any_where encoding.

#[kani::proof]
fn offset_vec_symbolic2() {
    let mut v = vec![[0u64; 3], [2u64; 3]];
    unsafe {
        let offset = kani::any_where(|o: &usize| *o <= v.len());
        let begin = v.as_mut_ptr();
        let end = begin.add(offset);
        assert_eq!(end.offset_from_unsigned(begin), offset);
    }
}
