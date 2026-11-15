// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r08): Reference arguments whose pointee has NO enum (EnumPlacement::Absent keeps the cascade term),
// including u64/usize where the pointee sort equals the address sort.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r08. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   struct_value_join_method_must_fail -> VERIFICATION:- FAILED (assertion)
//   struct_value_join_method_safe      -> VERIFICATION:- SUCCESSFUL
//   struct_value_differ_a_must_fail    -> VERIFICATION:- FAILED (assertion)
//   struct_value_differ_b_must_fail    -> VERIFICATION:- FAILED (assertion)
//   struct_value_differ_safe           -> VERIFICATION:- SUCCESSFUL
//   u64_value_differ_a_must_fail       -> VERIFICATION:- FAILED (assertion)
//   u64_value_differ_b_must_fail       -> VERIFICATION:- FAILED (assertion)
//   u64_value_differ_safe              -> VERIFICATION:- SUCCESSFUL
//   usize_value_differ_b_must_fail     -> VERIFICATION:- FAILED (assertion)
//   usize_value_differ_safe            -> VERIFICATION:- SUCCESSFUL
//   struct_u64_differ_b_must_fail      -> VERIFICATION:- FAILED (assertion)
//   struct_u64_differ_safe             -> VERIFICATION:- SUCCESSFUL
//   u64_mut_callee_join_must_fail      -> VERIFICATION:- FAILED (assertion)
//   u64_mut_callee_join_safe           -> VERIFICATION:- SUCCESSFUL

#[derive(Clone, Copy)]
struct S {
    a: u8,
    c: u16,
}
impl S {
    fn get(&self) -> u8 {
        self.a
    }
    fn sum(&self) -> u16 {
        self.a as u16 + self.c
    }
}
#[derive(Clone, Copy)]
struct P {
    x: u64,
}
impl P {
    fn is7(&self) -> bool {
        self.x == 7
    }
}
fn is7(x: &u64) -> bool {
    *x == 7
}
fn is7usize(x: &usize) -> bool {
    *x == 7
}
fn bump(x: &mut u64) {
    *x += 1;
}

#[kani::proof]
fn struct_value_join_method_must_fail() {
    let b: bool = kani::any();
    let s = if b { S { a: 4, c: 1 } } else { S { a: 4, c: 1 } };
    assert!(s.get() != 4);
}
#[kani::proof]
fn struct_value_join_method_safe() {
    let b: bool = kani::any();
    let s = if b { S { a: 4, c: 1 } } else { S { a: 4, c: 1 } };
    assert!(s.get() == 4 && s.sum() == 5);
}
#[kani::proof]
fn struct_value_differ_a_must_fail() {
    let b: bool = kani::any();
    let s = if b { S { a: 1, c: 1 } } else { S { a: 2, c: 1 } };
    assert!(s.get() == 1);
}
#[kani::proof]
fn struct_value_differ_b_must_fail() {
    let b: bool = kani::any();
    let s = if b { S { a: 1, c: 1 } } else { S { a: 2, c: 1 } };
    assert!(s.get() == 2);
}
#[kani::proof]
fn struct_value_differ_safe() {
    let b: bool = kani::any();
    let s = if b { S { a: 1, c: 1 } } else { S { a: 2, c: 1 } };
    assert!((s.get() == 1) == b);
}
#[kani::proof]
fn u64_value_differ_a_must_fail() {
    let b: bool = kani::any();
    let v: u64 = if b { 7 } else { 9 };
    assert!(is7(&v));
}
#[kani::proof]
fn u64_value_differ_b_must_fail() {
    let b: bool = kani::any();
    let v: u64 = if b { 7 } else { 9 };
    assert!(!is7(&v));
}
#[kani::proof]
fn u64_value_differ_safe() {
    let b: bool = kani::any();
    let v: u64 = if b { 7 } else { 9 };
    assert!(is7(&v) == b);
}
#[kani::proof]
fn usize_value_differ_b_must_fail() {
    let b: bool = kani::any();
    let v: usize = if b { 7 } else { 9 };
    assert!(!is7usize(&v));
}
#[kani::proof]
fn usize_value_differ_safe() {
    let b: bool = kani::any();
    let v: usize = if b { 7 } else { 9 };
    assert!(is7usize(&v) == b);
}
#[kani::proof]
fn struct_u64_differ_b_must_fail() {
    let b: bool = kani::any();
    let p = if b { P { x: 7 } } else { P { x: 9 } };
    assert!(!p.is7());
}
#[kani::proof]
fn struct_u64_differ_safe() {
    let b: bool = kani::any();
    let p = if b { P { x: 7 } } else { P { x: 9 } };
    assert!(p.is7() == b);
}
#[kani::proof]
fn u64_mut_callee_join_must_fail() {
    let b: bool = kani::any();
    let mut v: u64 = if b { 7 } else { 9 };
    bump(&mut v);
    assert!(v == 8);
}
#[kani::proof]
fn u64_mut_callee_join_safe() {
    let b: bool = kani::any();
    let mut v: u64 = if b { 7 } else { 9 };
    bump(&mut v);
    assert!((v == 8) == b && (v == 10) != b);
}
