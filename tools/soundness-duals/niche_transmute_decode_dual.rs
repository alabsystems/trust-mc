// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- bits or a raw pointer transmuted into a niche-encoded pointer
//! enum (review of fix/chc-lost-writes, lostwrite track round 1, finding 2). Main's
//! sort coercion did not decode the niche: a live address unwrapped to `None` and the
//! panic was certified Genuine on a program Kani proves. fix/chc-lost-writes made the
//! value fresh, which also lost `ptr::null()` -> `None` and `Box::into_raw` -> `Some`,
//! which main had right on both twins. The transmute now decodes the niche: `None`
//! exactly when the bits are zero, `Some(bits)` for a payload that is the pointer
//! itself (`Box`, `NonNull` in a datatype sort), a fresh `Some` for a by-value
//! reference payload (`Option<&T>` is modelled as `Option<T>`, so the pointee's value
//! is not in the bits), and bits that fold decide the variant outright.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_transmute_null_to_option_ref_is_none -> SUCCESSFUL
//!   bug_transmute_null_unwrap_panics          -> FAILED ('called `Option::unwrap()` on a `None` value')
//!   safe_transmute_box_raw_to_option_box      -> SUCCESSFUL
//!   bug_transmute_box_raw_wrong_value         -> FAILED ('assertion failed: *o.unwrap() == 4')
//!   safe_transmute_valid_ptr_to_option_ref    -> SUCCESSFUL
//!   bug_transmute_literal_to_option_ref       -> FAILED ('dereference failure: invalid integer address')
//!   bug_transmute_freed_ptr_to_option_ref     -> FAILED ('dereference failure: deallocated dynamic object')
//!   safe_reversed_enum_null_is_empty          -> SUCCESSFUL
//!   bug_reversed_enum_null_is_has             -> FAILED ('assertion failed: matches!(r, Rev::Has(_))')
//!   safe_reversed_enum_symbolic               -> SUCCESSFUL
//!   bug_reversed_enum_symbolic                -> FAILED ('assertion failed: matches!(r, Rev::Has(_))')
//!   safe_reversed_enum_live_is_has            -> SUCCESSFUL
//!   bug_reversed_enum_live_is_empty           -> FAILED ('assertion failed: matches!(r, Rev::Empty)')
//!   safe_rev_from_zero_usize_is_empty         -> SUCCESSFUL
//!   bug_rev_from_zero_usize_is_has            -> FAILED ('assertion failed: matches!(r, Rev::Has(_))')
//!   safe_revnn_null_is_nothing                -> SUCCESSFUL
//!   bug_revnn_null_is_ptr                     -> FAILED ('assertion failed: matches!(r, RevNN::Ptr(_))')
//!   safe_revref_null_is_z                     -> SUCCESSFUL
//!   bug_revref_null_is_r                      -> FAILED ('assertion failed: matches!(r, RevRef::R(_))')
//!   safe_symbolic_null_arm_is_none            -> SUCCESSFUL
//!   bug_symbolic_null_arm_unwrap              -> FAILED ('called `Option::unwrap()` on a `None` value')
//!
//! The rows from `safe_reversed_enum_null_is_empty` on are the round 2 review's
//! (lostwrite track round 2, finding 1): a two-variant niche enum whose payload
//! variant comes FIRST. Its datatype listed the empty constructor first, the
//! reverse of its variants, and the round 1 decode read `transmute(null)` as the
//! payload variant: a clean false proof of `bug_reversed_enum_null_is_has` and
//! certified false failures. The other sources (`usize`, `NonNull`, `&T`, a live
//! `Box`) were inverted on main too. The datatype now lists its constructors in
//! variant order. The last two rows: the by-value `Option<&T>` non-null arm is
//! `Some` of a fresh payload, not a fresh value of the whole sort (which could be
//! `None`).
#![allow(unused)]
use std::mem::transmute;
use std::ptr;
use std::ptr::NonNull;

enum Rev {
    Has(Box<u16>),
    Empty,
}

enum RevNN {
    Ptr(NonNull<u8>),
    Nothing,
}

enum RevRef<'a> {
    R(&'a u32),
    Z,
}

#[kani::proof]
fn safe_transmute_null_to_option_ref_is_none() {
    let r: Option<&u16> = unsafe { std::mem::transmute::<*const u16, Option<&u16>>(ptr::null()) };
    assert!(r.is_none());
}

#[kani::proof]
fn bug_transmute_null_unwrap_panics() {
    let r: Option<&u16> = unsafe { std::mem::transmute::<*const u16, Option<&u16>>(ptr::null()) };
    let v = *r.unwrap();
    assert!(v == v);
}

#[kani::proof]
fn safe_transmute_box_raw_to_option_box() {
    let b = Box::new(3u8);
    let raw = Box::into_raw(b);
    let o: Option<Box<u8>> = unsafe { std::mem::transmute::<*mut u8, Option<Box<u8>>>(raw) };
    assert!(*o.unwrap() == 3);
}

#[kani::proof]
fn bug_transmute_box_raw_wrong_value() {
    let b = Box::new(3u8);
    let raw = Box::into_raw(b);
    let o: Option<Box<u8>> = unsafe { std::mem::transmute::<*mut u8, Option<Box<u8>>>(raw) };
    assert!(*o.unwrap() == 4);
}

// A by-value reference payload stays an approximation: a false failure, never a
// certificate (main certified the unwrap panic Genuine).
#[kani::proof]
fn safe_transmute_valid_ptr_to_option_ref() {
    let x = 5u16;
    let r: Option<&u16> =
        unsafe { std::mem::transmute::<*const u16, Option<&u16>>(&x as *const u16) };
    assert!(*r.unwrap() == 5);
}

#[kani::proof]
fn bug_transmute_literal_to_option_ref() {
    let r: Option<&u16> = unsafe { std::mem::transmute::<usize, Option<&u16>>(0x1000) };
    let v = *r.unwrap();
    assert!(v == v);
}

#[kani::proof]
fn bug_transmute_freed_ptr_to_option_ref() {
    let b = Box::new(3u16);
    let raw = Box::into_raw(b);
    unsafe { drop(Box::from_raw(raw)) };
    let r: Option<&u16> = unsafe { std::mem::transmute::<*const u16, Option<&u16>>(raw) };
    let v = *r.unwrap();
    assert!(v == v);
}

#[kani::proof]
fn safe_reversed_enum_null_is_empty() {
    let r: Rev = unsafe { transmute::<*mut u16, Rev>(ptr::null_mut()) };
    assert!(matches!(r, Rev::Empty));
}

#[kani::proof]
fn bug_reversed_enum_null_is_has() {
    let r: Rev = unsafe { transmute::<*mut u16, Rev>(ptr::null_mut()) };
    assert!(matches!(r, Rev::Has(_)));
}

#[kani::proof]
fn safe_reversed_enum_symbolic() {
    let raw = Box::into_raw(Box::new(4u16));
    let c: bool = kani::any();
    let p = if c { raw } else { ptr::null_mut() };
    let r: Rev = unsafe { transmute::<*mut u16, Rev>(p) };
    assert!(matches!(r, Rev::Has(_)) == c);
}

#[kani::proof]
fn bug_reversed_enum_symbolic() {
    let raw = Box::into_raw(Box::new(4u16));
    let c: bool = kani::any();
    let p = if c { raw } else { ptr::null_mut() };
    let r: Rev = unsafe { transmute::<*mut u16, Rev>(p) };
    assert!(matches!(r, Rev::Has(_)));
}

#[kani::proof]
fn safe_reversed_enum_live_is_has() {
    let raw = Box::into_raw(Box::new(4u16));
    let r: Rev = unsafe { transmute::<*mut u16, Rev>(raw) };
    match r {
        Rev::Has(b) => assert!(*b == 4),
        Rev::Empty => panic!("not empty"),
    }
}

#[kani::proof]
fn bug_reversed_enum_live_is_empty() {
    let raw = Box::into_raw(Box::new(4u16));
    let r: Rev = unsafe { transmute::<*mut u16, Rev>(raw) };
    assert!(matches!(r, Rev::Empty));
}

#[kani::proof]
fn safe_rev_from_zero_usize_is_empty() {
    let r: Rev = unsafe { transmute::<usize, Rev>(0usize) };
    assert!(matches!(r, Rev::Empty));
}

#[kani::proof]
fn bug_rev_from_zero_usize_is_has() {
    let r: Rev = unsafe { transmute::<usize, Rev>(0usize) };
    assert!(matches!(r, Rev::Has(_)));
}

#[kani::proof]
fn safe_revnn_null_is_nothing() {
    let r: RevNN = unsafe { transmute::<*mut u8, RevNN>(ptr::null_mut()) };
    assert!(matches!(r, RevNN::Nothing));
}

#[kani::proof]
fn bug_revnn_null_is_ptr() {
    let r: RevNN = unsafe { transmute::<*mut u8, RevNN>(ptr::null_mut()) };
    assert!(matches!(r, RevNN::Ptr(_)));
}

#[kani::proof]
fn safe_revref_null_is_z() {
    let r: RevRef = unsafe { transmute::<*const u32, RevRef>(ptr::null()) };
    assert!(matches!(r, RevRef::Z));
}

#[kani::proof]
fn bug_revref_null_is_r() {
    let r: RevRef = unsafe { transmute::<*const u32, RevRef>(ptr::null()) };
    assert!(matches!(r, RevRef::R(_)));
}

#[kani::proof]
fn safe_symbolic_null_arm_is_none() {
    let c: bool = kani::any();
    let x = 5u16;
    let p: *const u16 = if c { &x } else { ptr::null() };
    let r: Option<&u16> = unsafe { transmute::<*const u16, Option<&u16>>(p) };
    assert!(r.is_some() == c);
}

#[kani::proof]
fn bug_symbolic_null_arm_unwrap() {
    let c: bool = kani::any();
    let x = 5u16;
    let p: *const u16 = if c { &x } else { ptr::null() };
    let r: Option<&u16> = unsafe { transmute::<*const u16, Option<&u16>>(p) };
    if !c {
        let v = *r.unwrap();
        assert!(v == v);
    }
}
