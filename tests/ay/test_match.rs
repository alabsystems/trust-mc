// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
// NOTE: Recovered to PROOF at ay e1c70f4a.
//
//! Test case for match expressions with 3+ arms (#107)

#[kani::proof]
fn test_match_three_arms() {
    let x: i32 = kani::any();
    kani::assume(x >= 0 && x < 3);

    let result = match x {
        0 => 10,
        1 => 20,
        _ => 30,
    };

    // Should be 10, 20, or 30 depending on x
    assert!(result == 10 || result == 20 || result == 30);
}

#[kani::proof]
fn test_match_constrained() {
    let x: i32 = kani::any();
    kani::assume(x == 1);

    let result = match x {
        0 => {
            assert!(false); // Unreachable - x is 1
            0
        }
        1 => {
            assert!(true); // Should be reached
            1
        }
        _ => {
            assert!(false); // Unreachable - x is 1
            2
        }
    };

    assert!(result == 1);
}
