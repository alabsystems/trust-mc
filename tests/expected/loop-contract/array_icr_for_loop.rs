// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// kani-flags: -Z loop-contracts -Z mem-predicates -Z quantifiers

//! Check a loop invariant with a quantified array update.
//! The active expected diagnostic records the remaining solver limitation
//! tracked in <https://github.com/model-checking/kani/issues/4282>.

#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]

#[kani::proof]
fn check_array_inc() {
    let mut a: [i32; 8] = kani::any();
    kani::assume(kani::forall!(|j in (0, a.len())| a[j] < i32::MAX));
    let initial = a;
    let mut i = 0;
    #[kani::loop_invariant(
        i <= a.len()
            && kani::forall!(|j in (0, i)| a[j] == i32::wrapping_add(initial[j], 1))
            && kani::forall!(|j in (i, a.len())| a[j] == initial[j])
    )]
    while i < a.len() {
        a[i] = a[i].wrapping_add(1);
        i += 1;
    }
    assert!(kani::forall!(|j in (0, a.len())| a[j] == i32::wrapping_add(initial[j], 1)));
}
