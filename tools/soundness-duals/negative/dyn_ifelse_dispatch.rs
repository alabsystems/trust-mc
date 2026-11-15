// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: `&dyn Trait` coerced on BOTH arms of an if/else, then called.
//
// Audit evidence: chc-codegen/virtual-call-devirt. Refuted as stated (multi-impl
// dyn calls use an ITE case split); the residual the plan keeps for M3 is a
// CLEAN false proof from build_dispatch_ite_chain's constant-vtable
// short-circuit (dispatch.rs, #4075 D2): when the receiver's vtable
// discriminant folds to a BitVecConst the chain inlines only the matching
// body. If a flow-insensitive vtable side table hands an if/else-coerced
// receiver ONE arm's constant, the other arm is never dispatched, and one
// polarity of the assertions below is proved although the other arm reaches it.
//
// NOT REPRODUCED on bundle 07b812dd1 (2026-09-11): the CHC lane fails every
// must-fail harness here with a Genuine counterexample. The shapes cover the
// ways a single constant can reach the call (direct if/else, assignment on both
// arms, prebound `&dyn` locals, a call boundary, two call boundaries, Box<dyn>)
// in both polarities, so the short-circuit cannot pick either arm unseen. They
// stay as the tripwire for the M3 fix. The BMC lane certifies Genuine
// counterexamples on the safe twins (a separate false failure).
//
// Oracle (per harness):
//   ifelse_dyn_then_arm_value_must_fail     -> VERIFICATION:- FAILED (assertion)
//   ifelse_dyn_else_arm_value_must_fail     -> VERIFICATION:- FAILED (assertion)
//   assign_both_arms_then_must_fail         -> VERIFICATION:- FAILED (assertion)
//   assign_both_arms_else_must_fail         -> VERIFICATION:- FAILED (assertion)
//   prebound_refs_then_must_fail            -> VERIFICATION:- FAILED (assertion)
//   prebound_refs_else_must_fail            -> VERIFICATION:- FAILED (assertion)
//   ifelse_dyn_cross_fn_must_fail           -> VERIFICATION:- FAILED (assertion)
//   nested_call_then_must_fail              -> VERIFICATION:- FAILED (assertion)
//   nested_call_else_must_fail              -> VERIFICATION:- FAILED (assertion)
//   boxed_then_must_fail                    -> VERIFICATION:- FAILED (assertion)
//   boxed_else_must_fail                    -> VERIFICATION:- FAILED (assertion)
//   ifelse_dyn_both_arms_safe               -> VERIFICATION:- SUCCESSFUL
//   ifelse_dyn_cross_fn_safe                -> VERIFICATION:- SUCCESSFUL

trait Val {
    fn v(&self) -> u32;
}

struct One;
impl Val for One {
    fn v(&self) -> u32 {
        1
    }
}

struct Two;
impl Val for Two {
    fn v(&self) -> u32 {
        2
    }
}

fn call_v(x: &dyn Val) -> u32 {
    x.v()
}

fn outer(x: &dyn Val) -> u32 {
    call_v(x)
}

#[kani::proof]
fn ifelse_dyn_then_arm_value_must_fail() {
    let c: bool = kani::any();
    let one = One;
    let two = Two;
    let x: &dyn Val = if c { &one } else { &two };
    // FALSE when c == false.
    assert!(x.v() == 1);
}

#[kani::proof]
fn ifelse_dyn_else_arm_value_must_fail() {
    let c: bool = kani::any();
    let one = One;
    let two = Two;
    let x: &dyn Val = if c { &one } else { &two };
    // FALSE when c == true.
    assert!(x.v() == 2);
}

#[kani::proof]
fn assign_both_arms_then_must_fail() {
    let c: bool = kani::any();
    let one = One;
    let two = Two;
    let x: &dyn Val;
    if c {
        x = &one;
    } else {
        x = &two;
    }
    assert!(x.v() == 1);
}

#[kani::proof]
fn assign_both_arms_else_must_fail() {
    let c: bool = kani::any();
    let one = One;
    let two = Two;
    let x: &dyn Val;
    if c {
        x = &one;
    } else {
        x = &two;
    }
    assert!(x.v() == 2);
}

#[kani::proof]
fn prebound_refs_then_must_fail() {
    let c: bool = kani::any();
    let one = One;
    let two = Two;
    let r1: &dyn Val = &one;
    let r2: &dyn Val = &two;
    let x = if c { r1 } else { r2 };
    assert!(x.v() == 1);
}

#[kani::proof]
fn prebound_refs_else_must_fail() {
    let c: bool = kani::any();
    let one = One;
    let two = Two;
    let r1: &dyn Val = &one;
    let r2: &dyn Val = &two;
    let x = if c { r1 } else { r2 };
    assert!(x.v() == 2);
}

#[kani::proof]
fn ifelse_dyn_cross_fn_must_fail() {
    let c: bool = kani::any();
    let one = One;
    let two = Two;
    let x: &dyn Val = if c { &one } else { &two };
    // FALSE when c == false; the dispatch happens in another function.
    assert!(call_v(x) == 1);
}

#[kani::proof]
fn nested_call_then_must_fail() {
    let c: bool = kani::any();
    let one = One;
    let two = Two;
    let x: &dyn Val = if c { &one } else { &two };
    assert!(outer(x) == 1);
}

#[kani::proof]
fn nested_call_else_must_fail() {
    let c: bool = kani::any();
    let one = One;
    let two = Two;
    let x: &dyn Val = if c { &one } else { &two };
    assert!(outer(x) == 2);
}

#[kani::proof]
fn boxed_then_must_fail() {
    let c: bool = kani::any();
    let x: Box<dyn Val> = if c { Box::new(One) } else { Box::new(Two) };
    assert!(x.v() == 1);
}

#[kani::proof]
fn boxed_else_must_fail() {
    let c: bool = kani::any();
    let x: Box<dyn Val> = if c { Box::new(One) } else { Box::new(Two) };
    assert!(x.v() == 2);
}

#[kani::proof]
fn ifelse_dyn_both_arms_safe() {
    let c: bool = kani::any();
    let one = One;
    let two = Two;
    let x: &dyn Val = if c { &one } else { &two };
    let got = x.v();
    assert!(if c { got == 1 } else { got == 2 });
}

#[kani::proof]
fn ifelse_dyn_cross_fn_safe() {
    let c: bool = kani::any();
    let one = One;
    let two = Two;
    let x: &dyn Val = if c { &one } else { &two };
    let got = call_v(x);
    assert!(got == 1 || got == 2);
}
