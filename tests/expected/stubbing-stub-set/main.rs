// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z stubbing
//! Check that `kani::stub_set!` and `#[kani::use_stub_set]` expand to ordinary
//! harness stubs.

fn identity(i: i8) -> i8 {
    i
}

fn decrement(i: i8) -> i8 {
    i.wrapping_sub(1)
}

fn increment(i: i8) -> i8 {
    i.wrapping_add(1)
}

kani::stub_set!(all_identity, stub(decrement, identity), stub(increment, identity),);

kani::stub_set!(pub nested_identity, use_stub_set(all_identity),);

#[kani::proof]
#[kani::use_stub_set(nested_identity)]
fn check_stub_set() {
    let n = kani::any();
    assert_eq!(decrement(n), n);
    assert_eq!(increment(n), n);
}
