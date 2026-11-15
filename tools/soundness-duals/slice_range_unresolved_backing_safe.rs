// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// DUAL (safe twin) for `slice_range_unresolved_backing_bug.rs`.
//
// The same shapes with IN-BOUNDS ranges. The fail-closed rule the bug twin
// pins makes an unresolved backing report FAILED, so this twin's job is to
// show the conservative rule is not so blunt that ordinary in-bounds slicing
// becomes unprovable in the cases where the backing DOES resolve.
//
// Oracle: NOT_GENUINE — a safe program must not be certified as a failure.

#[kani::proof]
fn range_to_in_bounds_safe() {
    let data: [u8; 4] = [1, 2, 3, 4];
    let s: &[u8] = &data;
    let sub = &s[..2];
    assert!(sub.len() == 2);
}

#[kani::proof]
fn range_from_in_bounds_safe() {
    let data: [u8; 4] = [1, 2, 3, 4];
    let s: &[u8] = &data;
    let sub = &s[2..];
    assert!(sub.len() == 2);
}

#[kani::proof]
fn range_full_in_bounds_safe() {
    let data: [u8; 4] = [1, 2, 3, 4];
    assert!(data[1] == 2);
    let p = data.as_ptr();
    let s: &[u8] = unsafe { core::slice::from_raw_parts(p, 4) };
    let n = kani::any_where(|n: &usize| *n >= 1 && *n <= 4);
    let sub = &s[1..n];
    assert!(sub.len() <= 3);
}
