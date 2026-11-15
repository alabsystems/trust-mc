// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a function of the crate under
//! verification whose NAME matches a standard-library helper the encoders
//! model by name (`wrapping_add`, `saturating_sub`), including a
//! `#[kani::stub]` replacement named after the function it stubs.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3 with -Z stubbing,
//! measured 2026-09-27):
//!   bug_user_fn_named_wrapping_add   -> VERIFICATION:- FAILED  ("user wrapping_add assertion")
//!   safe_user_fn_named_wrapping_add  -> VERIFICATION:- SUCCESSFUL
//!   bug_user_fn_named_saturating_sub -> VERIFICATION:- FAILED  ("user saturating_sub assertion")
//!   bug_stub_named_wrapping_add      -> VERIFICATION:- FAILED  ("stubbed wrapping_add")
//!
//! MECHANISM UNDER TEST. The MIR inliner keeps a call a "special codegen
//! handler" boundary when the callee's name contains `wrapping_`, `checked_`,
//! `saturating_`, ... (`FunctionInlinePass::has_special_codegen_handler`),
//! and the BMC lane then models the call by the same name
//! (`try_codegen_std_intrinsic` -> `dispatch_arithmetic`), dropping the body.
//! Both matched a USER function as well as the library one: on main c22e1022e
//! the BMC lane verified bug_user_fn_named_wrapping_add and
//! bug_stub_named_wrapping_add SUCCESSFUL clean and certified
//! safe_user_fn_named_wrapping_add's counterexample Genuine (it modelled
//! `a ^ b` as `a + b`). The CHC lane walks the body and matches. Found in the
//! package round of fix/chc-walker-fail-closed (item a): with call sites
//! rewritten to the stub, a stub named after `wrapping_add` met the BMC
//! name model. FIXED: a function defined in the crate under verification is
//! never a name-keyed handler boundary nor a name-keyed std model.
//!
//! Lanes: BMC and CHC.
//!
//! Run: trust-mc-driver [--ay-chc] -Z unstable-options -Z stubbing --harness-timeout=30s user_fn_std_helper_name_dual.rs

#[inline(never)]
fn my_wrapping_add(a: u8, b: u8) -> u8 {
    assert!(a != 100, "user wrapping_add assertion");
    a ^ b
}

#[inline(never)]
fn xor_wrapping_add(a: u8, b: u8) -> u8 {
    a ^ b
}

#[inline(never)]
fn my_saturating_sub(a: u8, b: u8) -> u8 {
    assert!(a != 100, "user saturating_sub assertion");
    a.wrapping_sub(b)
}

pub fn stub_wrapping_add(a: u8, b: u8) -> u8 {
    assert!(a != 100, "stubbed wrapping_add");
    a ^ b
}

#[kani::proof]
fn bug_user_fn_named_wrapping_add() {
    let a: u8 = kani::any();
    let r = my_wrapping_add(a, 1);
    // Holds for `a ^ 1` and for `a + 1` alike, so only the assertion fails.
    assert!(r != 255 || a == 254, "other check");
}

#[kani::proof]
fn safe_user_fn_named_wrapping_add() {
    let a: u8 = kani::any();
    assert!(xor_wrapping_add(a, 1) == a ^ 1);
}

#[kani::proof]
fn bug_user_fn_named_saturating_sub() {
    let a: u8 = kani::any();
    let r = my_saturating_sub(a, 1);
    assert!(r != 255 || a == 0, "other check");
}

#[kani::proof]
#[kani::stub(u8::wrapping_add, stub_wrapping_add)]
fn bug_stub_named_wrapping_add() {
    let a: u8 = kani::any();
    let r = a.wrapping_add(1);
    assert!(r != 255 || a == 254, "other check");
}
