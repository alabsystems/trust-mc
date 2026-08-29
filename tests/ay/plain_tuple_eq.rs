// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: PROOF
// NOTE: Most harnesses (1/2) demoted PROOF→UNKNOWN by false proof defense (ay#8578).
#[kani::proof]
fn check_tuple_field_level() {
    let t: (u8, bool) = (0, true);
    assert!(t.0 == 0);
    assert!(t.1 == true);
}
