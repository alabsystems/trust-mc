// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[inline(never)]
fn call<F: FnOnce(&u64) -> u64>(function: F, value: &u64) -> u64 {
    function(value)
}

#[kani::proof]
fn readonly_word_rustcall_safe() {
    let value = 42u64;
    let result = call(|value| *value, &value);
    assert!(result == 42);
}

#[kani::proof]
fn readonly_word_rustcall_wrong_value_bug() {
    let value = 42u64;
    let result = call(|value| *value, &value);
    assert!(result == 5);
}
