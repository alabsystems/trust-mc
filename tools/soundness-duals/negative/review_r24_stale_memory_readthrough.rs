// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r24): A joined Option (or an aggregate holding one) written through &mut by a std callee, then
// compared through a reference: the ReadThrough typed-memory load must see the write.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r24. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   swap_differ_must_fail          -> VERIFICATION:- FAILED (assertion)
//   swap_differ_safe               -> VERIFICATION:- SUCCESSFUL
//   mem_take_then_eq_must_fail     -> VERIFICATION:- FAILED (assertion)
//   mem_take_then_eq_safe          -> VERIFICATION:- SUCCESSFUL
//   option_take_then_eq_must_fail  -> VERIFICATION:- FAILED (assertion)
//   option_take_then_eq_safe       -> VERIFICATION:- SUCCESSFUL
//   ptr_write_then_eq_must_fail    -> VERIFICATION:- FAILED (assertion)
//   ptr_write_then_eq_safe         -> VERIFICATION:- SUCCESSFUL
//   replace_none_then_eq_must_fail -> VERIFICATION:- FAILED (assertion)
//   replace_none_then_eq_safe      -> VERIFICATION:- SUCCESSFUL
//   swap_nested_struct_must_fail   -> VERIFICATION:- FAILED (assertion)
//   swap_nested_struct_safe        -> VERIFICATION:- SUCCESSFUL
//   swap_nojoin_must_fail          -> VERIFICATION:- FAILED (assertion)
//   swap_nojoin_safe               -> VERIFICATION:- SUCCESSFUL

struct W {
    o: Option<u8>,
    k: u8,
}
impl W {
    fn has_none(&self) -> bool {
        matches!(self.o, None)
    }
}

#[kani::proof]
fn swap_differ_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(1) } else { Some(2) };
    let mut q: Option<u8> = Some(9);
    core::mem::swap(&mut o, &mut q);
    assert!(o == Some(1) || o == Some(2));
}
#[kani::proof]
fn swap_differ_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(1) } else { Some(2) };
    let mut q: Option<u8> = Some(9);
    core::mem::swap(&mut o, &mut q);
    assert!(o == Some(9) && (q == Some(1)) == b);
}
#[kani::proof]
fn mem_take_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let _t = core::mem::take(&mut o);
    assert!(!(o == None));
}
#[kani::proof]
fn mem_take_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let t = core::mem::take(&mut o);
    assert!(o == None && t == Some(4));
}
#[kani::proof]
fn option_take_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let _t = o.take();
    assert!(!(o == None));
}
#[kani::proof]
fn option_take_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let t = o.take();
    assert!(o == None && t == Some(4));
}
#[kani::proof]
fn ptr_write_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    unsafe { core::ptr::write(&mut o, None) };
    assert!(!(o == None));
}
#[kani::proof]
fn ptr_write_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    unsafe { core::ptr::write(&mut o, None) };
    assert!(o == None);
}
#[kani::proof]
fn replace_none_then_eq_must_fail() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let _old = core::mem::replace(&mut o, None);
    assert!(!(o == None));
}
#[kani::proof]
fn replace_none_then_eq_safe() {
    let b: bool = kani::any();
    let mut o: Option<u8> = if b { Some(4) } else { Some(4) };
    let old = core::mem::replace(&mut o, None);
    assert!(o == None && old == Some(4));
}
#[kani::proof]
fn swap_nested_struct_must_fail() {
    let b: bool = kani::any();
    let mut w1 = if b { W { o: Some(4), k: 1 } } else { W { o: Some(4), k: 1 } };
    let mut w2 = W { o: None, k: 2 };
    core::mem::swap(&mut w1, &mut w2);
    assert!(!w1.has_none());
}
#[kani::proof]
fn swap_nested_struct_safe() {
    let b: bool = kani::any();
    let mut w1 = if b { W { o: Some(4), k: 1 } } else { W { o: Some(4), k: 1 } };
    let mut w2 = W { o: None, k: 2 };
    core::mem::swap(&mut w1, &mut w2);
    assert!(w1.has_none() && w1.k == 2 && !w2.has_none());
}
#[kani::proof]
fn swap_nojoin_must_fail() {
    let mut o: Option<u8> = Some(4);
    let mut q: Option<u8> = None;
    core::mem::swap(&mut o, &mut q);
    assert!(!(o == None));
}
#[kani::proof]
fn swap_nojoin_safe() {
    let mut o: Option<u8> = Some(4);
    let mut q: Option<u8> = None;
    core::mem::swap(&mut o, &mut q);
    assert!(o == None && q == Some(4));
}
