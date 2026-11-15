// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

mod user_api {
    #[inline(never)]
    pub fn any_where<F: FnOnce(&u32) -> bool>(predicate: F) -> u32 {
        let actual_value = 42;
        let _ignored_predicate_result = predicate(&actual_value);
        actual_value
    }
}

#[kani::proof]
fn custom_any_where_wrong_range_bug() {
    let value = user_api::any_where(|value| *value < 5);
    assert!(value < 5);
}

#[kani::proof]
fn custom_any_where_returns_its_actual_value_safe() {
    let value = user_api::any_where(|value| *value < 5);
    assert!(value == 42);
}
