// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[inline(never)]
fn call<F: FnOnce(&u64) -> u64>(function: F, value: &u64) -> u64 {
    function(value)
}

#[kani::proof]
fn readonly_symbolic_word_rustcall_safe() {
    let value: u64 = kani::any();
    kani::assume(value < 10);
    let result = call(|value| *value, &value);
    assert!(result == value);
}

#[kani::proof]
fn readonly_symbolic_word_wrong_range_bug() {
    let value: u64 = kani::any();
    kani::assume(value < 10);
    let result = call(|value| *value, &value);
    assert!(result >= 10);
}
