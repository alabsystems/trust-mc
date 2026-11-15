// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r20): User callees that WRITE through a &mut joined from two borrows (pointee without an enum:
// bind_inline_referent_arg keeps the cascade term; the caller-side deref-store refusal never sees the write).
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r20. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   callee_store_first_path_must_fail  -> VERIFICATION:- FAILED (assertion)
//   callee_store_second_path_must_fail -> VERIFICATION:- FAILED (assertion)
//   callee_store_safe                  -> VERIFICATION:- SUCCESSFUL
//   callee_inc_first_path_must_fail    -> VERIFICATION:- FAILED (assertion)
//   callee_inc_safe                    -> VERIFICATION:- SUCCESSFUL
//   method_store_second_path_must_fail -> VERIFICATION:- FAILED (assertion)
//   method_store_safe                  -> VERIFICATION:- SUCCESSFUL
//   mem_replace_first_path_must_fail   -> VERIFICATION:- FAILED (assertion)
//   mem_replace_safe                   -> VERIFICATION:- SUCCESSFUL
//   ptr_write_first_path_must_fail     -> VERIFICATION:- FAILED (assertion)
//   ptr_write_safe                     -> VERIFICATION:- SUCCESSFUL

struct S {
    a: u8,
}
impl S {
    fn set9(&mut self) {
        self.a = 9;
    }
}
fn set9(p: &mut u8) {
    *p = 9;
}
fn inc(p: &mut u8) {
    *p += 1;
}

#[kani::proof]
fn callee_store_first_path_must_fail() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    kani::assume(b);
    let r: &mut u8 = if b { &mut m } else { &mut n };
    set9(r);
    assert!(m == 1);
}
#[kani::proof]
fn callee_store_second_path_must_fail() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    kani::assume(!b);
    let r: &mut u8 = if b { &mut m } else { &mut n };
    set9(r);
    assert!(n == 2);
}
#[kani::proof]
fn callee_store_safe() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    let r: &mut u8 = if b { &mut m } else { &mut n };
    set9(r);
    assert!((m == 9) == b && (n == 9) != b);
}
#[kani::proof]
fn callee_inc_first_path_must_fail() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    kani::assume(b);
    let r: &mut u8 = if b { &mut m } else { &mut n };
    inc(r);
    assert!(m == 1);
}
#[kani::proof]
fn callee_inc_safe() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    let r: &mut u8 = if b { &mut m } else { &mut n };
    inc(r);
    assert!((m == 2) == b && (n == 3) != b);
}
#[kani::proof]
fn method_store_second_path_must_fail() {
    let mut m = S { a: 1 };
    let mut n = S { a: 2 };
    let b: bool = kani::any();
    kani::assume(!b);
    let r: &mut S = if b { &mut m } else { &mut n };
    r.set9();
    assert!(n.a == 2);
}
#[kani::proof]
fn method_store_safe() {
    let mut m = S { a: 1 };
    let mut n = S { a: 2 };
    let b: bool = kani::any();
    let r: &mut S = if b { &mut m } else { &mut n };
    r.set9();
    assert!((m.a == 9) == b && (n.a == 9) != b);
}
#[kani::proof]
fn mem_replace_first_path_must_fail() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    kani::assume(b);
    let r: &mut u8 = if b { &mut m } else { &mut n };
    let _old = core::mem::replace(r, 9);
    assert!(m == 1);
}
#[kani::proof]
fn mem_replace_safe() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    let r: &mut u8 = if b { &mut m } else { &mut n };
    let old = core::mem::replace(r, 9);
    assert!((m == 9) == b && (n == 9) != b && (old == 1) == b);
}
#[kani::proof]
fn ptr_write_first_path_must_fail() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    kani::assume(b);
    let p: *mut u8 = if b { &mut m as *mut u8 } else { &mut n as *mut u8 };
    unsafe { core::ptr::write(p, 9) };
    assert!(m == 1);
}
#[kani::proof]
fn ptr_write_safe() {
    let mut m = 1u8;
    let mut n = 2u8;
    let b: bool = kani::any();
    let p: *mut u8 = if b { &mut m as *mut u8 } else { &mut n as *mut u8 };
    unsafe { core::ptr::write(p, 9) };
    assert!((m == 9) == b && (n == 9) != b);
}
