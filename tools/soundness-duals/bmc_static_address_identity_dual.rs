// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness, BMC lane; Kani 0.67.0 semantics):
//   bug_two_statics_claimed_aliased     -> VERIFICATION:- FAILED (assertion)
//   safe_two_statics_are_distinct       -> VERIFICATION:- SUCCESSFUL
//   bug_static_initializer_claimed_zero -> VERIFICATION:- FAILED (assertion)
//   safe_static_initializer_read        -> VERIFICATION:- SUCCESSFUL
//
// WHY THIS FILE EXISTS. The BMC lane gave every static reached through a
// raw-pointer constant (`&raw mut A`, `addr_of_mut!`) the literal address
// 0x1000 and put none of its initializer bytes in `memory`. Two distinct
// statics were therefore ONE cell: after `A = 5`, `assert!(B == 5)` was
// PROVED on main 1a1cb3865 (a false proof), and a read of a static's initial
// value came from free bytes, so a true assertion about it failed certified
// Genuine (kani/Drop/forget_no_drop.rs, kani/Static/method_static_var.rs).

static mut A: i32 = 0;
static mut B: i32 = 0;
static mut C: u32 = 7;

#[kani::proof]
fn bug_two_statics_claimed_aliased() {
    unsafe {
        let a = &raw mut A;
        let b = &raw mut B;
        *a = 5;
        assert!(*b == 5);
    }
}

#[kani::proof]
fn safe_two_statics_are_distinct() {
    unsafe {
        let a = &raw mut A;
        let b = &raw mut B;
        *a = 5;
        assert!(*b == 0);
        assert!(*a == 5);
    }
}

#[kani::proof]
fn bug_static_initializer_claimed_zero() {
    unsafe {
        let c = &raw const C;
        assert!(*c == 0);
    }
}

#[kani::proof]
fn safe_static_initializer_read() {
    unsafe {
        let c = &raw const C;
        assert!(*c == 7);
    }
}
