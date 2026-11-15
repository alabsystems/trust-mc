// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- `dyn` -> `dyn` unsizes: trait upcasting (`Box<dyn Sub>`
//! -> `Box<dyn Super>`) and dropping an auto trait (`Box<dyn Tr + Send>` ->
//! `Box<dyn Tr>`), from the design 3 review (2026-09-26).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_upcast_mixed           -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   safe_upcast_mixed          -> VERIFICATION:- SUCCESSFUL
//!   bug_upcast_only            -> VERIFICATION:- FAILED  (same check)
//!   bug_upcast_ref             -> VERIFICATION:- FAILED  (same check)
//!   bug_upcast_helper          -> VERIFICATION:- FAILED  (same check)
//!   bug_upcast_nested_call     -> VERIFICATION:- FAILED  (same check)
//!   safe_upcast_nested_call    -> VERIFICATION:- SUCCESSFUL
//!   bug_upcast_fn              -> VERIFICATION:- FAILED  (same check)
//!   bug_upcast_fn_only         -> VERIFICATION:- FAILED  (same check)
//!   bug_drop_send_box          -> VERIFICATION:- FAILED  (same check)
//!   safe_drop_send_box         -> VERIFICATION:- SUCCESSFUL
//!   bug_drop_send_ref          -> VERIFICATION:- FAILED  (same check)
//!   bug_drop_send_nested_call  -> VERIFICATION:- FAILED  (same check)
//!   bug_fn_drop_send           -> VERIFICATION:- FAILED  (same check)
//!   bug_fn_drop_send_sole      -> VERIFICATION:- FAILED  (same check)
//!
//! MECHANISM (main 25905b622 and the first design 3 bundle ba0988f16445):
//! a coercion site stores the index of its concrete type in the candidate
//! list of the TARGET trait object's principal. For a `dyn Sub` source the
//! site looked up `dyn Sub` itself, which the host body's own cast had put in
//! `Super`'s list as a pseudo-candidate; the dispatch dropped that candidate
//! (a trait object has no method body) and its merge's default arm stood for
//! it silently, because the reachability universe recorded only unsizes from
//! concrete types and so did not list `SB` as a runtime type of `dyn Super`.
//! Every bug_ row verified SUCCESSFUL clean, and both safe_ upcast rows
//! failed Genuine. In a walked body the source's id was copied unchanged,
//! naming an unrelated candidate of the target list. Now (`dyn_to_dyn.rs`)
//! a cast that keeps the principal copies the source's id, an upcast maps
//! each source candidate to the target list's id of the same concrete type,
//! and the universe closes over upcasts.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_dyn_upcast_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Super {
    fn m(&self, a: u8, b: u8) -> u8;
}
pub trait Sub: Super {}
pub struct SA;
pub struct SB;
pub struct SC;
impl Super for SA {
    fn m(&self, a: u8, b: u8) -> u8 {
        a.wrapping_add(b)
    }
}
impl Super for SB {
    fn m(&self, a: u8, b: u8) -> u8 {
        unsafe { a.unchecked_add(b) }
    }
}
impl Super for SC {
    fn m(&self, a: u8, b: u8) -> u8 {
        a.wrapping_mul(b)
    }
}
impl Sub for SB {}
impl Sub for SC {}

// Only SA is coerced to `dyn Super` directly; SB reaches it only by upcast.
#[kani::proof]
fn bug_upcast_mixed() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Super> = if kani::any() {
        Box::new(SA)
    } else {
        let s: Box<dyn Sub> = Box::new(SB);
        s
    };
    sink(o.m(a, b));
}

#[kani::proof]
fn safe_upcast_mixed() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Super> = if kani::any() {
        Box::new(SA)
    } else {
        let s: Box<dyn Sub> = Box::new(SC);
        s
    };
    let r = o.m(a, b);
    assert!(r == a.wrapping_add(b) || r == a.wrapping_mul(b));
}

#[kani::proof]
fn bug_upcast_only() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let s: Box<dyn Sub> = Box::new(SB);
    let o: Box<dyn Super> = s;
    sink(o.m(a, b));
}

#[kani::proof]
fn bug_upcast_ref() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let sa = SA;
    let sb = SB;
    let s: &dyn Sub = &sb;
    let o: &dyn Super = if kani::any() { &sa } else { s };
    sink(o.m(a, b));
}

#[inline(never)]
fn upcast_in_helper(s: Box<dyn Sub>) -> Box<dyn Super> {
    s
}

#[kani::proof]
fn bug_upcast_helper() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Super> =
        if kani::any() { Box::new(SA) } else { upcast_in_helper(Box::new(SB)) };
    sink(o.m(a, b));
}

#[inline(never)]
fn call_m(o: &dyn Super, a: u8, b: u8) -> u8 {
    o.m(a, b)
}

#[kani::proof]
fn bug_upcast_nested_call() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Super> = if kani::any() {
        Box::new(SA)
    } else {
        let s: Box<dyn Sub> = Box::new(SB);
        s
    };
    sink(call_m(&*o, a, b));
}

#[kani::proof]
fn safe_upcast_nested_call() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Super> = if kani::any() {
        Box::new(SA)
    } else {
        let s: Box<dyn Sub> = Box::new(SC);
        s
    };
    let r = call_m(&*o, a, b);
    assert!(r == a.wrapping_add(b) || r == a.wrapping_mul(b));
}

// The Fn family: a closure boxed as `dyn MyFn` and upcast to `dyn Fn`.
pub trait MyFn: Fn(u8, u8) -> u8 {}
impl<T: Fn(u8, u8) -> u8> MyFn for T {}

#[kani::proof]
fn bug_upcast_fn() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: Box<dyn Fn(u8, u8) -> u8> = if kani::any() {
        Box::new(|x: u8, y: u8| x.wrapping_add(y))
    } else {
        let g: Box<dyn MyFn> = Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) });
        g
    };
    sink(f(a, b));
}

// The closure coerced to `dyn Fn` directly is the only one the body unsizes
// to it: it used to be walked unconditionally as the sole runtime type.
#[kani::proof]
fn bug_upcast_fn_only() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let safe: Box<dyn Fn(u8, u8) -> u8> = Box::new(|x: u8, y: u8| x.wrapping_add(y));
    sink(safe(a, 1));
    let g: Box<dyn MyFn> = Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) });
    let f: Box<dyn Fn(u8, u8) -> u8> = g;
    sink(f(a, b));
}

// Dropping an auto trait keeps the principal.
pub trait Tr {
    fn t(&self, a: u8, b: u8) -> u8;
}
impl Tr for SA {
    fn t(&self, a: u8, b: u8) -> u8 {
        a.wrapping_add(b)
    }
}
impl Tr for SB {
    fn t(&self, a: u8, b: u8) -> u8 {
        unsafe { a.unchecked_add(b) }
    }
}

#[kani::proof]
fn bug_drop_send_box() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Tr> = if kani::any() {
        Box::new(SA)
    } else {
        let s: Box<dyn Tr + Send> = Box::new(SB);
        s
    };
    sink(o.t(a, b));
}

#[kani::proof]
fn safe_drop_send_box() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let o: Box<dyn Tr> = if kani::any() {
        Box::new(SA)
    } else {
        let s: Box<dyn Tr + Send> = Box::new(SB);
        s
    };
    sink(o.t(a, b));
}

#[kani::proof]
fn bug_drop_send_ref() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let sa = SA;
    let sb = SB;
    let s: &(dyn Tr + Sync) = &sb;
    let o: &dyn Tr = if kani::any() { &sa } else { s };
    sink(o.t(a, b));
}

#[inline(never)]
fn call_t(o: &dyn Tr, a: u8, b: u8) -> u8 {
    o.t(a, b)
}

#[kani::proof]
fn bug_drop_send_nested_call() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Tr> = if kani::any() {
        Box::new(SA)
    } else {
        let s: Box<dyn Tr + Send> = Box::new(SB);
        s
    };
    sink(call_t(&*o, a, b));
}

#[kani::proof]
fn bug_fn_drop_send() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: Box<dyn Fn(u8, u8) -> u8> = if kani::any() {
        Box::new(|x: u8, y: u8| x.wrapping_add(y))
    } else {
        let g: Box<dyn Fn(u8, u8) -> u8 + Send> =
            Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) });
        g
    };
    sink(f(a, b));
}

#[kani::proof]
fn bug_fn_drop_send_sole() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let safe: Box<dyn Fn(u8, u8) -> u8> = Box::new(|x: u8, y: u8| x.wrapping_add(y));
    sink(safe(a, 1));
    let g: Box<dyn Fn(u8, u8) -> u8 + Send> =
        Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) });
    let f: Box<dyn Fn(u8, u8) -> u8> = g;
    sink(f(a, b));
}
