// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a write that the CHC encoder applies to a local's STATE, observed
// through a pointer whose read goes to the local's typed-memory IMAGE.
//
// Audit evidence: probes written while repairing m3/chc-joined-option-eq (2026-09-12).
// A pointer joined from two borrows (`if b { &m } else { &n }`) has no single points-at
// edge, so a read through it loads typed memory. The image of `m` is written when `m`
// is assigned or borrowed; a swap, replace or store through a resolved reference that
// constrained only `m`'s state left the image stale, and --ay-chc proved
// `scalar_swap_must_fail` and `deref_store_scalar_must_fail` on the head of the branch
// (VERIFICATION:- SUCCESSFUL) although native Rust panics on the path that took `&m`.
//
// Oracle (per harness):
//   swap_then_refjoin_must_fail        -> VERIFICATION:- FAILED (assertion)
//   swap_then_refjoin_safe             -> VERIFICATION:- SUCCESSFUL
//   replace_then_refjoin_must_fail     -> VERIFICATION:- FAILED (assertion)
//   deref_store_then_refjoin_must_fail -> VERIFICATION:- FAILED (assertion)
//   refjoin_then_swap_must_fail        -> VERIFICATION:- FAILED (assertion)
//   refjoin_then_swap_safe             -> VERIFICATION:- SUCCESSFUL
//   rawjoin_then_store_must_fail       -> VERIFICATION:- FAILED (assertion)
//   callee_clear_must_fail             -> VERIFICATION:- FAILED (assertion)
//   option_take_must_fail              -> VERIFICATION:- FAILED (assertion)
//   deref_store_option_must_fail       -> VERIFICATION:- FAILED (assertion)
//   deref_store_scalar_must_fail       -> VERIFICATION:- FAILED (assertion)
//   deref_store_scalar_safe            -> VERIFICATION:- SUCCESSFUL
//   replace_option_must_fail           -> VERIFICATION:- FAILED (assertion)
//   callee_set7_must_fail              -> VERIFICATION:- FAILED (assertion)
//   scalar_swap_must_fail              -> VERIFICATION:- FAILED (assertion)
//   scalar_swap_safe                   -> VERIFICATION:- SUCCESSFUL

fn clear(x: &mut Option<u8>) {
    *x = None;
}
fn set7(x: &mut Option<u8>) {
    *x = Some(7);
}

#[kani::proof]
fn swap_then_refjoin_must_fail() {
    let mut m = Some(1u8);
    let mut n = Some(2u8);
    let b: bool = kani::any();
    core::mem::swap(&mut m, &mut n);
    let r: &Option<u8> = if b { &m } else { &n };
    assert!(!(r == &Some(2)) || !b);
}
#[kani::proof]
fn swap_then_refjoin_safe() {
    let mut m = Some(1u8);
    let mut n = Some(2u8);
    let b: bool = kani::any();
    core::mem::swap(&mut m, &mut n);
    let r: &Option<u8> = if b { &m } else { &n };
    assert!((r == &Some(2)) == b);
}
#[kani::proof]
fn replace_then_refjoin_must_fail() {
    let mut m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let _old = core::mem::replace(&mut m, Some(3));
    let r: &Option<u8> = if b { &m } else { &n };
    assert!(!(r == &Some(3)) || !b);
}
#[kani::proof]
fn deref_store_then_refjoin_must_fail() {
    let mut m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let p = &mut m;
    *p = Some(3);
    let r: &Option<u8> = if b { &m } else { &n };
    assert!(!(r == &Some(3)) || !b);
}
#[kani::proof]
fn refjoin_then_swap_must_fail() {
    let mut m = Some(1u8);
    let mut n = Some(2u8);
    let b: bool = kani::any();
    {
        let r: *const Option<u8> = if b { &m } else { &n };
        core::mem::swap(&mut m, &mut n);
        let v = unsafe { *r };
        assert!(!(v == Some(2)) || !b);
    }
}
#[kani::proof]
fn refjoin_then_swap_safe() {
    let mut m = Some(1u8);
    let mut n = Some(2u8);
    let b: bool = kani::any();
    {
        let r: *const Option<u8> = if b { &m } else { &n };
        core::mem::swap(&mut m, &mut n);
        let v = unsafe { *r };
        assert!((v == Some(2)) == b);
    }
}
#[kani::proof]
fn rawjoin_then_store_must_fail() {
    let mut m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: *const Option<u8> = if b { &m } else { &n };
    m = Some(7);
    let v = unsafe { &*r };
    assert!(!(v == &Some(7)) || !b);
    let _ = n;
}
#[kani::proof]
fn callee_clear_must_fail() {
    let mut m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: *const Option<u8> = if b { &m } else { &n };
    clear(&mut m);
    let v = unsafe { *r };
    assert!(v != None || !b);
}
#[kani::proof]
fn option_take_must_fail() {
    let mut m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: *const Option<u8> = if b { &m } else { &n };
    let _t = m.take();
    let v = unsafe { *r };
    assert!(v != None || !b);
}
#[kani::proof]
fn deref_store_option_must_fail() {
    let mut m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: *const Option<u8> = if b { &m } else { &n };
    let p = &mut m;
    *p = Some(7);
    let v = unsafe { *r };
    assert!(v != Some(7) || !b);
}
#[kani::proof]
fn deref_store_scalar_must_fail() {
    let mut m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let r: *const u8 = if b { &m } else { &n };
    let p = &mut m;
    *p = 7;
    let v = unsafe { *r };
    assert!(v != 7 || !b);
}
#[kani::proof]
fn deref_store_scalar_safe() {
    let mut m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let r: *const u8 = if b { &m } else { &n };
    let p = &mut m;
    *p = 7;
    let v = unsafe { *r };
    assert!((v == 7) == b);
}
#[kani::proof]
fn replace_option_must_fail() {
    let mut m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: *const Option<u8> = if b { &m } else { &n };
    let _old = core::mem::replace(&mut m, Some(7));
    let v = unsafe { *r };
    assert!(v != Some(7) || !b);
}
#[kani::proof]
fn callee_set7_must_fail() {
    let mut m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: *const Option<u8> = if b { &m } else { &n };
    set7(&mut m);
    let v = unsafe { *r };
    assert!(v != Some(7) || !b);
}
#[kani::proof]
fn scalar_swap_must_fail() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    let r: *const u8 = if b { &m } else { &n };
    core::mem::swap(&mut m, &mut n);
    let v = unsafe { *r };
    assert!(v != 2 || !b);
}
#[kani::proof]
fn scalar_swap_safe() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    let r: *const u8 = if b { &m } else { &n };
    core::mem::swap(&mut m, &mut n);
    let v = unsafe { *r };
    assert!((v == 2) == b);
}
