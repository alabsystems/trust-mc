// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: stores and reads through a reference chosen on a path.
//
// Found while fixing negative/modifies_frame_residual.rs (2026-09-12). The BMC
// register model resolved `*p` through `ref_pointees`, ONE flow-insensitive
// name table written in block-encoding order, so after
// `let p = if c { &mut b } else { &mut a }; *p = 1` the store wrote `a` on
// both paths: `assert!(a == 1)` verified SUCCESSFUL (a false proof) and the
// safe twin failed with a Genuine certificate. The CHC lane lost the store
// through a path-merged pointer and constant-folded the reads (false
// certificate on the safe twin; callee_store_must_fail verified SUCCESSFUL in
// two of three runs on bundle 31793ccc3). Measured on bundle 31793ccc3:
//   bmc: last_arm, raw_merge, field_store, callee_store SUCCESSFUL;
//        merged_safe FAILED Genuine.
//   chc: callee_store SUCCESSFUL (nondeterministic); merged_safe FAILED Genuine.
//
// Oracle (per harness):
//   last_arm_must_fail            -> VERIFICATION:- FAILED (assertion)
//   first_arm_must_fail           -> VERIFICATION:- FAILED (assertion)
//   callee_store_must_fail        -> VERIFICATION:- FAILED (assertion)
//   early_return_pick_must_fail   -> VERIFICATION:- FAILED (assertion)
//   field_store_must_fail         -> VERIFICATION:- FAILED (assertion)
//   loop_merge_must_fail          -> VERIFICATION:- FAILED (assertion)
//   raw_merge_must_fail           -> VERIFICATION:- FAILED (assertion)
//   merged_safe                   -> never a Genuine counterexample (SUCCESSFUL
//                                    or an honestly demoted FAILED)
//   merged_read_safe              -> never a Genuine counterexample

struct Pair {
    x: u32,
    y: u32,
}

fn store_one(p: &mut u32) {
    *p = 1;
}

fn pick<'a>(a: &'a mut u32, b: &'a mut u32, c: bool) -> &'a mut u32 {
    if c {
        return b;
    }
    a
}

#[kani::proof]
fn last_arm_must_fail() {
    let mut a: u32 = 0;
    let mut b: u32 = 0;
    let c: bool = kani::any();
    let p: &mut u32 = if c { &mut b } else { &mut a };
    *p = 1;
    // FALSE when c: the store went to b.
    assert!(a == 1);
}

#[kani::proof]
fn first_arm_must_fail() {
    let mut a: u32 = 0;
    let mut b: u32 = 0;
    let c: bool = kani::any();
    let p: &mut u32 = if c { &mut a } else { &mut b };
    *p = 1;
    // FALSE when !c.
    assert!(a == 1);
}

#[kani::proof]
fn callee_store_must_fail() {
    let mut a: u32 = 0;
    let mut b: u32 = 0;
    let c: bool = kani::any();
    let p: &mut u32 = if c { &mut b } else { &mut a };
    store_one(p);
    // FALSE when c.
    assert!(a == 1);
}

#[kani::proof]
fn early_return_pick_must_fail() {
    let mut a: u32 = 0;
    let mut b: u32 = 0;
    let c: bool = kani::any();
    let p = pick(&mut a, &mut b, c);
    *p = 1;
    // FALSE when c.
    assert!(a == 1);
}

#[kani::proof]
fn field_store_must_fail() {
    let mut s = Pair { x: 0, y: 0 };
    let mut t = Pair { x: 0, y: 0 };
    let c: bool = kani::any();
    let p: &mut Pair = if c { &mut t } else { &mut s };
    p.x = 1;
    assert!(s.y == 0 && t.y == 0);
    // FALSE when c.
    assert!(s.x == 1);
}

#[kani::proof]
#[kani::unwind(4)]
fn loop_merge_must_fail() {
    let mut a: u32 = 0;
    let mut b: u32 = 0;
    let n: u8 = kani::any();
    kani::assume(n < 3);
    let mut p: &mut u32 = &mut a;
    let mut i = 0;
    while i < n {
        p = &mut b;
        i += 1;
    }
    *p = 1;
    // FALSE when n > 0.
    assert!(a == 1);
}

#[kani::proof]
fn raw_merge_must_fail() {
    let mut a: u32 = 0;
    let mut b: u32 = 0;
    let c: bool = kani::any();
    let p: *mut u32 = if c { &mut b as *mut u32 } else { &mut a as *mut u32 };
    unsafe {
        *p = 1;
    }
    // FALSE when c.
    assert!(a == 1);
}

#[kani::proof]
fn merged_safe() {
    let mut a: u32 = 0;
    let mut b: u32 = 0;
    let c: bool = kani::any();
    let p: &mut u32 = if c { &mut b } else { &mut a };
    *p = 1;
    assert!(a + b == 1);
    assert!(if c { b == 1 && a == 0 } else { a == 1 && b == 0 });
}

#[kani::proof]
fn merged_read_safe() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let c: bool = kani::any();
    let r: &u32 = if c { &b } else { &a };
    assert!(*r == if c { b } else { a });
}
