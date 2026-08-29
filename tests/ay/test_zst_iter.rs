// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// kani-flags: --unstable=array-iter-unroll
// kani-expect: PROOF

// Test ZST array iteration transformation
// Tests that ArrayIterUnrollPass correctly handles ZST arrays like [(); N]
// (elements are zero-sized but array has N > 0 elements)

#[kani::proof]
#[kani::unwind(5)]
fn test_zst_iter_simple() {
    // ZST array - all elements are ()
    let arr: [(); 3] = [(), (), ()];
    let mut count = 0u32;
    for _ in arr {
        count += 1;
    }
    // Should iterate exactly 3 times
    kani::assert(count == 3, "Should iterate 3 times");
}

#[kani::proof]
#[kani::unwind(12)]
fn test_zst_iter_any() {
    // ZST array from kani::any() - still all ()
    let arr: [(); 10] = kani::any();
    let mut count = 0u32;
    for e in arr {
        // e is () - unit value
        let _: () = e;
        count += 1;
    }
    kani::assert(count == 10, "Should iterate 10 times");
}

// Zero-length array tests - fixed in #492
// ArrayIterUnrollPass now handles [T; 0] by bypassing the iterator infrastructure

#[kani::proof]
#[kani::unwind(1)]
fn test_zero_length_u8() {
    // Zero-length array of u8
    let arr: [u8; 0] = [];
    let mut count = 0u32;
    for _ in arr {
        count += 1;
    }
    // Should iterate exactly 0 times
    kani::assert(count == 0, "Should iterate 0 times");
}

#[kani::proof]
#[kani::unwind(1)]
fn test_zero_length_zst() {
    // Zero-length array of ZST
    let arr: [(); 0] = [];
    let mut count = 0u32;
    for _ in arr {
        count += 1;
    }
    // Should iterate exactly 0 times
    kani::assert(count == 0, "Should iterate 0 times");
}
