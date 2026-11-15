// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: reads through a pointer joined from two producers, on the path
// that took the FIRST producer.
//
// Audit evidence: related-construct probes of 2026-09-12 for
// limits-page/chc-joined-option-eq-false-proof (base 7b7f719f7, ay 0.26.0
// 94bf24d0f). The encoder records a concrete stack address per LOCAL
// (`known_stack_addr_exprs`), so `let r = if b { &m } else { &n };` kept only
// the producer translated last, and every read through `r` saw `n`. On the base
// bundle every `_must_fail` harness here was SUCCESSFUL under --ay-chc, and the
// scalar, `matches!` and raw-pointer ones were SUCCESSFUL in the default lane
// too; every `_safe` twin FAILED labelled Genuine in both lanes.
//
// Oracle (per harness):
//   scalar_first_path_must_fail          -> VERIFICATION:- FAILED (assertion)
//   scalar_first_path_safe               -> VERIFICATION:- SUCCESSFUL
//   option_matches_first_path_must_fail  -> VERIFICATION:- FAILED (assertion)
//   option_matches_first_path_safe       -> VERIFICATION:- SUCCESSFUL
//   raw_pointer_first_path_must_fail     -> VERIFICATION:- FAILED (assertion)
//   raw_pointer_first_path_safe          -> VERIFICATION:- SUCCESSFUL
//   struct_method_first_path_must_fail   -> VERIFICATION:- FAILED (assertion)
//   struct_method_first_path_safe        -> VERIFICATION:- SUCCESSFUL
//
// Each harness keeps only the path through the first borrow (`assume(b)`); the
// `_must_fail` assertion names the second referent's value, the `_safe` one the
// first's.

#[derive(Clone, Copy)]
struct S {
    a: u8,
}

impl S {
    fn get(&self) -> u8 {
        self.a
    }
}

#[kani::proof]
fn scalar_first_path_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    kani::assume(b);
    let r: &u8 = if b { &m } else { &n };
    assert!(*r == 2);
}

#[kani::proof]
fn scalar_first_path_safe() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    kani::assume(b);
    let r: &u8 = if b { &m } else { &n };
    assert!(*r == 1);
}

#[kani::proof]
fn option_matches_first_path_must_fail() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    kani::assume(b);
    let r: &Option<u8> = if b { &m } else { &n };
    assert!(matches!(*r, Some(2)));
}

#[kani::proof]
fn option_matches_first_path_safe() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    kani::assume(b);
    let r: &Option<u8> = if b { &m } else { &n };
    assert!(matches!(*r, Some(1)));
}

#[kani::proof]
fn raw_pointer_first_path_must_fail() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    kani::assume(b);
    let p: *const u8 = if b { &m as *const u8 } else { &n as *const u8 };
    assert!(unsafe { *p } == 2);
}

#[kani::proof]
fn raw_pointer_first_path_safe() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    kani::assume(b);
    let p: *const u8 = if b { &m as *const u8 } else { &n as *const u8 };
    assert!(unsafe { *p } == 1);
}

#[kani::proof]
fn struct_method_first_path_must_fail() {
    let m = S { a: 1 };
    let n = S { a: 2 };
    let b: bool = kani::any();
    kani::assume(!b);
    let r: &S = if b { &m } else { &n };
    assert!(r.get() == 1);
}

#[kani::proof]
fn struct_method_first_path_safe() {
    let m = S { a: 1 };
    let n = S { a: 2 };
    let b: bool = kani::any();
    kani::assume(!b);
    let r: &S = if b { &m } else { &n };
    assert!(r.get() == 2);
}
