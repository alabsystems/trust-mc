// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Reduced current-head reproducer for the NIA `product_sign_associative`
//! residual tracked in #3925.
//!
//! Mirrors the shared `product_sign_{2,3}` helper shape used by the tier2 and
//! tier3 bootstrap files, but removes unrelated bootstrap context so the
//! remaining verdict class is attributable to the theorem itself.
//!
//! The reduced associative harness is stable as a clean base-engine UNKNOWN, but
//! the driver's retry ladder can promote that into a watchdog cleanup under load.
//! Keep retries disabled here so the file captures the theorem classification,
//! not retry-policy side effects.

// kani-flags: --ay-chc-no-retry
// kani-expect: ay_nia_product_sign_zero_factor_reduced=PROOF
// kani-expect: ay_nia_product_sign_associative_reduced=BMC_SAFE

/// Compute the sign of a product of two factors.
/// Returns: -1 (negative), 0 (zero), 1 (positive)
fn product_sign_2(a: i32, b: i32) -> i32 {
    if a == 0 || b == 0 {
        return 0;
    }
    a * b
}

/// Compute the sign of a product of three factors.
fn product_sign_3(a: i32, b: i32, c: i32) -> i32 {
    if a == 0 || b == 0 || c == 0 {
        return 0;
    }
    a * b * c
}

/// Control harness: the current-head zero-factor property is already PROOF in
/// both bootstrap files, so the reduced file should preserve that.
#[kani::proof]
fn ay_nia_product_sign_zero_factor_reduced() {
    let s1: i32 = kani::any();
    let s2: i32 = kani::any();
    kani::assume(s1 >= -1 && s1 <= 1);
    kani::assume(s2 >= -1 && s2 <= 1);

    assert!(product_sign_3(s1, 0, s2) == 0, "Zero factor yields zero product");
}

/// Reduced reproducer for the current-head associative residual.
#[kani::proof]
fn ay_nia_product_sign_associative_reduced() {
    let s1: i32 = kani::any();
    let s2: i32 = kani::any();
    let s3: i32 = kani::any();
    kani::assume(s1 == -1 || s1 == 1);
    kani::assume(s2 == -1 || s2 == 1);
    kani::assume(s3 == -1 || s3 == 1);

    let all = product_sign_3(s1, s2, s3);
    let grouped_12_3 = product_sign_2(product_sign_2(s1, s2), s3);
    let grouped_1_23 = product_sign_2(s1, product_sign_2(s2, s3));

    assert!(all == grouped_12_3, "product_sign is associative (12,3)");
    assert!(all == grouped_1_23, "product_sign is associative (1,23)");
}
