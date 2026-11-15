// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness and seed):
//   safe_* -> VERIFICATION:- SUCCESSFUL
//   bug_*  -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS (design trust-mc-reds-final §4.3, Rule C, the guard).
// Rule C keys a memory cell by representation: a `#[repr(transparent)]`
// wrapper shares its field's key ONLY when the two have the same SMT sort. A
// user newtype over an integer is a datatype sort, its field a bitvector; a
// key collapse that ignored the sort would store a datatype value into a
// bitvector array, refused as a sort mismatch (a false failure on a correct
// program). Stores and loads through `&mut W` and `*mut W` must keep working.

#[repr(transparent)]
pub struct W(u32);

fn bump(w: &mut W) {
    w.0 = w.0.wrapping_add(1);
}

#[kani::proof]
fn safe_newtype_through_mut_ref() {
    let v: u32 = kani::any();
    let mut w = W(v);
    bump(&mut w);
    assert!(w.0 == v.wrapping_add(1));
}

#[kani::proof]
fn bug_newtype_through_mut_ref() {
    let v: u32 = kani::any();
    let mut w = W(v);
    bump(&mut w);
    assert!(w.0 == v);
}

#[kani::proof]
fn safe_newtype_through_raw_ptr() {
    let v: u32 = kani::any();
    let p: *mut W = Box::into_raw(Box::new(W(v)));
    unsafe {
        (*p).0 = 7;
        assert!((*p).0 == 7);
        drop(Box::from_raw(p));
    }
}

#[kani::proof]
fn bug_newtype_through_raw_ptr() {
    let v: u32 = kani::any();
    let p: *mut W = Box::into_raw(Box::new(W(v)));
    unsafe {
        (*p).0 = 7;
        assert!((*p).0 == v);
        drop(Box::from_raw(p));
    }
}
