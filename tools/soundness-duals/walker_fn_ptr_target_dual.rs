// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tracker, closed by design 3) -- which function a fn
//! POINTER calls, inside a dyn-dispatched body walked by the CHC INLINE WALKER
//! (and at the top level).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_samename_decoy           -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_samename_symbolic        -> VERIFICATION:- FAILED  (same check)
//!   bug_samename_direct_symbolic -> VERIFICATION:- FAILED  (same check)
//!   safe_samename_distinct_ptrs  -> VERIFICATION:- SUCCESSFUL
//!   bug_static_fnptr_decoy       -> VERIFICATION:- FAILED  (same check)
//!   bug_static_two_decoys        -> VERIFICATION:- FAILED  (same check)
//!   bug_static_nodecoy           -> VERIFICATION:- FAILED  (same check)
//!   bug_const_fnptr_nodecoy      -> VERIFICATION:- FAILED  (same check)
//!   safe_static_two_decoys       -> VERIFICATION:- SUCCESSFUL
//!   bug_single_target_too_large  -> VERIFICATION:- FAILED  (same check)
//!   bug_symbolic_target_too_large -> VERIFICATION:- FAILED  (same check; control)
//!
//! STATUS (2026-09-25): closed by design 3 of
//! `docs/chc-hole-fix-designs-2026-09-24.md`. Ids are minted per instance
//! (`codegen_ay/fn_ptr_identity.rs`); a call's candidates are walked under
//! `pointer == id` only when the set is complete (one minted id, an
//! if-then-else of minted ids, or a closed host local) with the obligation
//! "invalid function pointer" as the default arm, and anything else fails
//! closed (`call/fn_ptr_targets.rs`). The bug_samename_ rows FAIL Genuine;
//! the static, const and too-large rows FAIL OverApproximation;
//! safe_samename_distinct_ptrs verifies; safe_static_two_decoys is a
//! known-red false failure (a static's fn-pointer value is not an id).
//!
//! MECHANISMS (as found; the review of the walker branch confirmed each, and
//! main 25905b622 still missed each the same way):
//! 1. IDS KEYED BY TRIMMED NAME. `translate_reify_fn_pointer`
//!    (`stmt/codegen_stmt_rvalue_ref/cast_dispatch.rs`, also
//!    `codegen_call_alloc_payload.rs`) keys `fn_ptr_ids` by
//!    `format!("{}_{:?}", def.trimmed_name(), args)`, so `m1::op2` and
//!    `m2::op2` get ONE id. `host_fn_ptr_reification_candidates`
//!    (`call/codegen_call_fn_ptr.rs`) skips the second as already seen and the
//!    walker's FnPtr arm (`codegen_call_virtual_inline/nested_call.rs`) walks
//!    `m1::op2` for either pointer (`bug_samename_*`); with no walker at all the
//!    two pointers compare equal (`safe_samename_distinct_ptrs`, a Genuine
//!    false counterexample). `bug_samename_direct_symbolic` is a top-level call:
//!    `resolve_fn_ptr_body` walks the FIRST reification in the pointer's copy
//!    chain, and it is missed with distinct names too.
//! 2. TARGETS NOT REIFIED IN THE HOST. The FnPtr arm treats every function
//!    the host body reifies as the complete target set. A pointer read from a
//!    static or a const is never among them: with none reified the call is
//!    havocked as a SoundHavoc (`bug_static_nodecoy`, `bug_const_fnptr_nodecoy`);
//!    with one decoy the decoy is walked unconditionally
//!    (`bug_static_fnptr_decoy`); with two, the merge's fresh default arm
//!    (`dispatch.rs` `merge_guarded_dispatch_results`, `__partial_vdisp_*`)
//!    carries no checks and records nothing (`bug_static_two_decoys`), and a
//!    correct program gets a Genuine counterexample from it
//!    (`safe_static_two_decoys`).
//! 3. ONE TARGET TOO LARGE TO WALK. The unconditional walk
//!    (`walk_nested_fn_ptr_target`) returns None over the 16-block limit and
//!    records nothing, so the call is havocked as a SoundHavoc
//!    (`bug_single_target_too_large`); the multi-candidate twin records
//!    `nested_fn_ptr_target_unresolved` and fails closed
//!    (`bug_symbolic_target_too_large`, the control).
//!
//! Promoted from the 2026-09-24 adversarial review (merges-and-dispatch lens,
//! merge/fnptr_samename.rs, fnptr_id_collision.rs, fnptr_origin.rs,
//! fnptr_static_multi.rs, fnptr_default_label.rs and big_body.rs).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_fn_ptr_target_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

mod m1 {
    pub fn op2(a: u8, b: u8) -> u8 {
        a.wrapping_add(b)
    }
}
mod m2 {
    pub fn op2(a: u8, b: u8) -> u8 {
        unsafe { a.unchecked_add(b) }
    }
}
mod n1 {
    pub fn op3(a: u8, b: u8) -> u8 {
        a.wrapping_add(b)
    }
}
mod n2 {
    pub fn op3(a: u8, b: u8) -> u8 {
        a.wrapping_sub(b)
    }
}

fn add_safe(a: u8, b: u8) -> u8 {
    a.wrapping_add(b)
}
fn sub_safe(a: u8, b: u8) -> u8 {
    a.wrapping_sub(b)
}
fn mul_safe(a: u8, b: u8) -> u8 {
    a.wrapping_mul(b)
}
fn add_ub(a: u8, b: u8) -> u8 {
    unsafe { a.unchecked_add(b) }
}

fn big_ub(a: u8, b: u8) -> u8 {
    let mut r = a;
    if b == 1 { r ^= 1; }
    if b == 2 { r ^= 2; }
    if b == 3 { r ^= 3; }
    if b == 4 { r ^= 4; }
    if b == 5 { r ^= 5; }
    if b == 6 { r ^= 6; }
    if b == 7 { r ^= 7; }
    if b == 8 { r ^= 8; }
    if b == 9 { r ^= 9; }
    if b == 10 { r ^= 10; }
    if b == 11 { r ^= 11; }
    if b == 12 { r ^= 12; }
    if b == 13 { r ^= 13; }
    if b == 14 { r ^= 14; }
    unsafe { r.unchecked_add(b) }
}

const F_UB: fn(u8, u8) -> u8 = add_ub;
static S_UB: fn(u8, u8) -> u8 = add_ub;
static S_MUL: fn(u8, u8) -> u8 = mul_safe;

pub trait Op {
    fn op(&self, f: fn(u8, u8) -> u8, a: u8, b: u8) -> u8;
}
pub struct A;
pub struct B;
impl Op for A {
    fn op(&self, f: fn(u8, u8) -> u8, a: u8, b: u8) -> u8 {
        f(a, b)
    }
}
impl Op for B {
    fn op(&self, f: fn(u8, u8) -> u8, a: u8, b: u8) -> u8 {
        f(a, b)
    }
}

fn pick() -> Box<dyn Op> {
    if kani::any() { Box::new(A) } else { Box::new(B) }
}

#[kani::proof]
fn bug_samename_decoy() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let decoy: fn(u8, u8) -> u8 = m1::op2;
    sink(decoy);
    let f: fn(u8, u8) -> u8 = m2::op2;
    sink(pick().op(f, a, b));
}

#[kani::proof]
fn bug_samename_symbolic() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = if kani::any() { m1::op2 } else { m2::op2 };
    sink(pick().op(f, a, b));
}

#[kani::proof]
fn bug_samename_direct_symbolic() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = if kani::any() { m1::op2 } else { m2::op2 };
    sink(f(a, b));
}

#[kani::proof]
fn safe_samename_distinct_ptrs() {
    let p1: fn(u8, u8) -> u8 = n1::op3;
    let p2: fn(u8, u8) -> u8 = n2::op3;
    assert!(p1 != p2);
}

#[kani::proof]
fn bug_static_fnptr_decoy() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let decoy: fn(u8, u8) -> u8 = add_safe;
    sink(decoy);
    let f = S_UB;
    sink(pick().op(f, a, b));
}

#[kani::proof]
fn bug_static_two_decoys() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let d1: fn(u8, u8) -> u8 = add_safe;
    let d2: fn(u8, u8) -> u8 = sub_safe;
    sink(d1);
    sink(d2);
    let f = S_UB;
    sink(pick().op(f, a, b));
}

#[kani::proof]
fn bug_static_nodecoy() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f = S_UB;
    sink(pick().op(f, a, b));
}

#[kani::proof]
fn bug_const_fnptr_nodecoy() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f = F_UB;
    sink(pick().op(f, a, b));
}

#[kani::proof]
fn safe_static_two_decoys() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let d1: fn(u8, u8) -> u8 = add_safe;
    let d2: fn(u8, u8) -> u8 = sub_safe;
    sink(d1);
    sink(d2);
    let f = S_MUL;
    let r = pick().op(f, a, b);
    assert!(r == a.wrapping_mul(b));
}

#[kani::proof]
fn bug_single_target_too_large() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = big_ub;
    sink(pick().op(f, a, b));
}

#[kani::proof]
fn bug_symbolic_target_too_large() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = if kani::any() { add_safe } else { big_ub };
    sink(pick().op(f, a, b));
}
