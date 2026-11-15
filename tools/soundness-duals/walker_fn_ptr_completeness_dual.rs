// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- candidate completeness for calls through a fn pointer or
//! a trait object, beyond the two tracker files (design 3 of
//! `docs/chc-hole-fix-designs-2026-09-24.md`; `walker_fn_ptr_target_dual.rs`,
//! `walker_dispatch_candidates_dual.rs`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_host_symbolic            -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   safe_host_symbolic           -> VERIFICATION:- SUCCESSFUL
//!   bug_host_two_targets_write   -> VERIFICATION:- FAILED  ('assertion failed: v < 100')
//!   safe_host_two_targets_write  -> VERIFICATION:- SUCCESSFUL
//!   bug_host_two_targets_static  -> VERIFICATION:- FAILED  ('assertion failed: unsafe { G } < 100')
//!   bug_fnptr_from_call          -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_fnptr_in_struct_dyn      -> VERIFICATION:- FAILED  (same check)
//!   bug_helper_boxed_closure     -> VERIFICATION:- FAILED  (same check)
//!   safe_helper_boxed_closure    -> VERIFICATION:- SUCCESSFUL
//!   bug_supertrait_method        -> VERIFICATION:- FAILED  (same check)
//!   safe_supertrait_method       -> VERIFICATION:- SUCCESSFUL
//!   safe_static_eq_reified       -> VERIFICATION:- SUCCESSFUL
//!   safe_const_eq_reified        -> VERIFICATION:- SUCCESSFUL
//!   bug_static_eq_other          -> VERIFICATION:- FAILED  ('assertion failed: SF == g')
//!   safe_fnptr_usize_roundtrip   -> VERIFICATION:- SUCCESSFUL
//!   safe_fnptr_void_ptr_callback -> VERIFICATION:- SUCCESSFUL
//!
//! SHAPES (each one a route the design-3 review measured on main 25905b622):
//! * A symbolic choice between two reified functions, called on the host.
//!   The host route walked the FIRST reification in the pointer's copy chain
//!   unconditionally (`bug_host_symbolic` SUCCESSFUL clean on main); with two
//!   targets writing through `&mut` the other target's write was lost
//!   (`bug_host_two_targets_write`), and with two targets writing one
//!   `static mut` the same (`bug_host_two_targets_static`). Now the set is
//!   complete (a closed local) and dispatched under `pointer == id` with the
//!   obligation "invalid function pointer"; arms that write memory decline to
//!   the fail-closed fallback instead of applying both writes unguarded.
//! * A pointer returned by a call, or read from a struct field inside a walked
//!   dyn method: its value is not known, so the call fails closed.
//! * A `Box<dyn Fn>` built in a helper: the closures are unsized only in the
//!   helper, so neither is in the dispatch list from impls and the host body;
//!   the harness's dyn-coercion universe adds them.
//! * A supertrait method called on `Box<dyn Sub>`: dispatched over `Sub`'s
//!   list, the one the stored vtable ids index.
//!
//! * Added by the design 3 review (2026-09-26). A fn pointer a static or a
//!   const holds is the function's identity: `SF == f` for the same function
//!   failed, certified Genuine, because a reification minted a counter id
//!   and an allocation's relocation read as a hash (a const) or as its zero
//!   bytes (a static). Both now read `fn_ptr_identity_value`.
//! * Also from the review: a fn pointer read back through another type (a
//!   `usize` cell, a `*const ()` callback slot) is unconstrained in the
//!   type-indexed memory model; the universe completes its call, and the
//!   "invalid function pointer" obligation then failed on the unconstrained
//!   value, certified Genuine. That obligation is now uncertified (a sound
//!   havoc whose freed variable it reads): still a false failure, never a
//!   certificate.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_fn_ptr_completeness_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

fn add_safe(a: u8, b: u8) -> u8 {
    a.wrapping_add(b)
}
fn add_ub(a: u8, b: u8) -> u8 {
    unsafe { a.unchecked_add(b) }
}
fn w1(x: &mut u8) {
    *x = 1;
}
fn w2(x: &mut u8) {
    *x = 200;
}
static mut G: u8 = 0;
fn g1() {
    unsafe {
        G = 1;
    }
}
fn g2() {
    unsafe {
        G = 200;
    }
}

#[inline(never)]
fn choose(c: bool) -> fn(u8, u8) -> u8 {
    if c { add_safe } else { add_ub }
}

pub struct Holder {
    pub f: fn(u8, u8) -> u8,
}
pub trait Apply {
    fn apply(&self, h: &Holder, a: u8, b: u8) -> u8;
}
pub struct P;
pub struct Q;
impl Apply for P {
    fn apply(&self, h: &Holder, a: u8, b: u8) -> u8 {
        (h.f)(a, b)
    }
}
impl Apply for Q {
    fn apply(&self, h: &Holder, a: u8, b: u8) -> u8 {
        (h.f)(a, b)
    }
}
fn pick_apply() -> Box<dyn Apply> {
    if kani::any() { Box::new(P) } else { Box::new(Q) }
}

#[inline(never)]
fn make_adder(c: bool) -> Box<dyn Fn(u8, u8) -> u8> {
    if c { Box::new(|x: u8, y: u8| x.wrapping_add(y)) } else { Box::new(|x: u8, y: u8| unsafe { x.unchecked_add(y) }) }
}
#[inline(never)]
fn make_safe_adder(c: bool) -> Box<dyn Fn(u8, u8) -> u8> {
    if c { Box::new(|x: u8, y: u8| x.wrapping_add(y)) } else { Box::new(|x: u8, y: u8| x.wrapping_sub(y)) }
}

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
impl Sub for SA {}
impl Sub for SB {}
impl Sub for SC {}

#[kani::proof]
fn bug_host_symbolic() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = if kani::any() { add_safe } else { add_ub };
    sink(f(a, b));
}

#[kani::proof]
fn safe_host_symbolic() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let f: fn(u8, u8) -> u8 = if kani::any() { add_safe } else { add_ub };
    sink(f(a, b));
}

#[kani::proof]
fn bug_host_two_targets_write() {
    let mut v: u8 = 5;
    let f: fn(&mut u8) = if kani::any() { w1 } else { w2 };
    f(&mut v);
    assert!(v < 100);
}

#[kani::proof]
fn safe_host_two_targets_write() {
    let mut v: u8 = 5;
    let f: fn(&mut u8) = if kani::any() { w1 } else { w2 };
    f(&mut v);
    assert!(v == 1 || v == 200);
}

#[kani::proof]
fn bug_host_two_targets_static() {
    let f: fn() = if kani::any() { g1 } else { g2 };
    f();
    assert!(unsafe { G } < 100);
}

#[kani::proof]
fn bug_fnptr_from_call() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f = choose(kani::any());
    sink(f(a, b));
}

#[kani::proof]
fn bug_fnptr_in_struct_dyn() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let h = Holder { f: if kani::any() { add_safe } else { add_ub } };
    sink(pick_apply().apply(&h, a, b));
}

#[kani::proof]
fn bug_helper_boxed_closure() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f = make_adder(kani::any());
    sink(f(a, b));
}

#[kani::proof]
fn safe_helper_boxed_closure() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f = make_safe_adder(kani::any());
    let r = f(a, b);
    assert!(r == a.wrapping_add(b) || r == a.wrapping_sub(b));
}

#[kani::proof]
fn bug_supertrait_method() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Sub> = if kani::any() { Box::new(SA) } else { Box::new(SB) };
    sink(o.m(a, b));
}

#[kani::proof]
fn safe_supertrait_method() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Sub> = if kani::any() { Box::new(SA) } else { Box::new(SC) };
    let r = o.m(a, b);
    assert!(r == a.wrapping_add(b) || r == a.wrapping_mul(b));
}

static SF: fn(u8, u8) -> u8 = add_safe;
const CF: fn(u8, u8) -> u8 = add_safe;

#[kani::proof]
fn safe_static_eq_reified() {
    let f: fn(u8, u8) -> u8 = add_safe;
    assert!(SF == f);
}

#[kani::proof]
fn safe_const_eq_reified() {
    let f: fn(u8, u8) -> u8 = add_safe;
    assert!(CF == f);
}

#[kani::proof]
fn bug_static_eq_other() {
    let g: fn(u8, u8) -> u8 = add_ub;
    assert!(SF == g);
}

#[kani::proof]
fn safe_fnptr_usize_roundtrip() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = add_safe;
    let x: usize = f as usize;
    let g: fn(u8, u8) -> u8 = unsafe { *(&x as *const usize as *const fn(u8, u8) -> u8) };
    sink(g(a, b));
}

#[kani::proof]
fn safe_fnptr_void_ptr_callback() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let f: fn(u8, u8) -> u8 = add_safe;
    let p: *const () = f as *const ();
    let g: fn(u8, u8) -> u8 = unsafe { *(&p as *const *const () as *const fn(u8, u8) -> u8) };
    sink(g(a, b));
}
