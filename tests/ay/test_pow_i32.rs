// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
// Quick test: does the pow handler fire for i32?
// Part of #3294: pow is MIR-inlined before CHC codegen sees it, so the
// algebraic call-dispatch handler never fires. CHC now proves the inlined
// exp-by-squaring loop directly at the bounded exponent used here.
#[kani::proof]
fn test_pow_i32() {
    let exp: u32 = kani::any();
    kani::assume(exp < 8);
    let result = 2_i32.pow(exp);
    assert!(result > 0);
}
