// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- writes the inline walker lost with no reason recorded,
//! found by the review of design 2 Phase 0
//! (docs/chc-hole-fix-designs-2026-09-24.md, "Design 2, Phase 0: review
//! findings"). Every bug_ row below except two was SUCCESSFUL on the Phase 0
//! bundle and on main at ay 6818b5d06, and every safe_ row a false Genuine
//! certificate there, while the corpus-rev Kani 4c0fce8c3 FAILS each bug_ row
//! and verifies each safe_ row (the manifest entry has the measurements). The
//! two exceptions are guards: bug_dyn2_field_reborrow (Phase 0 already failed
//! it closed) and bug_dyn2_stale_outer (F1 fails it closed on both).
//!
//! M1: a write `*p = v` through a NON-ARGUMENT reference local whose term is
//! the referent's value (`let p = &mut x`, `&mut s`, `&mut arr[i]`, an
//! `Option` payload) rebound `p` only; `x` kept its old term. Fixed by
//! applying the write to the referent the walked body names
//! (codegen_call_virtual_inline/referent_write.rs), or recording
//! walker_deref_write_rebind_lost when it names none (the Option rows).
//! Reached through five front doors: two dyn candidates, the dyn door's
//! constant-vtable single candidate, `&dyn Fn`, `Box<dyn FnMut>`, the
//! fn_inline walker (a self-recursive callee) and a host fn pointer.
//!
//! M2: a memory store through a pointer that is not itself an argument local
//! (a raw-pointer copy of an argument, a reference in a by-value struct or
//! tuple argument, a local struct around the argument) recorded nothing, and
//! the caller's state variable kept the old value. Fixed by classifying every
//! store of the walker's store lanes (inline_walk_guard.rs,
//! classify_inline_walk_lane_store): walker_deref_writeback_memory_only.
//!
//! M3: the host fn-pointer route dropped a walked closure's alias updates, so
//! a write through a `&mut` argument never reached the caller. Fixed by
//! re-keying them to the call's arguments (codegen_call_fn_ptr.rs).
//!
//! M6: the walker's static mirror wrote the first `static mut` state variable
//! of a matching sort, not the static the store reached: a walked `H = 9`
//! proved `K == 9`. Fixed by keying the mirror on the static's object
//! (projected_assign_helpers.rs, mirror_static_state_var_update).
//!
//! F2 residual: a reference held in a by-value aggregate argument, read
//! through a field, was read as its address. Fixed by tagging the copied
//! reference address-bound (statement_exec.rs, rvalue_reads_field_address),
//! so its read fails closed; more shapes in walker_agg_ref_read_dual.rs.
//!
//! The fn-pointer rows use two candidate bodies that differ: the host route
//! walks only the first ReifyFnPointer cast it finds
//! (walker_fn_ptr_target_dual.rs::bug_samename_direct_symbolic, known-red), so
//! each row is written to hold, or fail, whichever body is walked.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_*  -> VERIFICATION:- FAILED
//!   safe_* -> VERIFICATION:- SUCCESSFUL
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_referent_write_dual.rs

#[inline(never)]
fn sink<T>(_v: T) {}

pub struct S {
    pub a: u8,
    pub b: u8,
}
pub struct W<'a> {
    pub r: &'a mut u8,
    pub k: u8,
}
pub struct Wr<'a> {
    pub r: &'a u8,
    pub k: u8,
}

// ---- M1: a write through a non-argument reference local -------------------
pub trait T {
    fn local_alias(&self, v: u8) -> u8;
    fn struct_alias(&self, v: u8) -> u8;
    fn arr_alias(&self, v: u8) -> u8;
    fn loop_alias(&self, v: u8) -> u8;
    fn add_after_alias(&self, v: u8) -> u8;
    fn as_mut_alias(&self, v: u8) -> u8;
    fn opt_arg(&self, o: Option<&mut u8>);
    fn opt_local(&self, a: &mut u8);
    fn field_reborrow(&self, s: &mut S);
    fn two_referents(&self, c: bool, v: u8) -> u8;
    fn reborrow_chain(&self, v: u8) -> u8;
    fn stale_outer(&self, v: u8) -> u8;
}
pub struct A;
pub struct B;
macro_rules! imp_t {
    ($t:ty) => {
        impl T for $t {
            fn local_alias(&self, v: u8) -> u8 {
                let mut x: u8 = 0;
                let p = &mut x;
                *p = v;
                x
            }
            fn struct_alias(&self, v: u8) -> u8 {
                let mut s = S { a: 0, b: 0 };
                let p = &mut s;
                p.a = v;
                s.a
            }
            fn arr_alias(&self, v: u8) -> u8 {
                let mut arr = [0u8; 2];
                let p = &mut arr[1];
                *p = v;
                arr[1]
            }
            fn loop_alias(&self, v: u8) -> u8 {
                let mut x: u8 = 0;
                let p = &mut x;
                let mut i = 0;
                while i < 2 {
                    *p = v;
                    i += 1;
                }
                x
            }
            fn add_after_alias(&self, v: u8) -> u8 {
                let mut x: u8 = 0;
                let p = &mut x;
                *p = v;
                unsafe { x.unchecked_add(1) }
            }
            fn as_mut_alias(&self, v: u8) -> u8 {
                let mut o: Option<u8> = Some(0);
                if let Some(e) = o.as_mut() {
                    *e = v;
                }
                o.unwrap_or(0)
            }
            fn opt_arg(&self, o: Option<&mut u8>) {
                if let Some(r) = o {
                    *r = 200;
                }
            }
            fn opt_local(&self, a: &mut u8) {
                let o = Some(a);
                if let Some(r) = o {
                    *r = 200;
                }
            }
            fn field_reborrow(&self, s: &mut S) {
                let p = &mut s.a;
                *p = 200;
            }
            // Two definitions of `p` name two places: no single referent.
            fn two_referents(&self, c: bool, v: u8) -> u8 {
                let mut x: u8 = 0;
                let mut y: u8 = 0;
                let p = if c { &mut x } else { &mut y };
                *p = v;
                x.wrapping_add(y)
            }
            // `p = &mut *q`, `q = &mut x`: the referent is two hops away.
            fn reborrow_chain(&self, v: u8) -> u8 {
                let mut x: u8 = 0;
                let q = &mut x;
                let p = &mut *q;
                *p = v;
                x
            }
            // `q` still holds the old value after the write through `p`; its
            // read goes through a `Deref`, which F1 fails closed.
            fn stale_outer(&self, v: u8) -> u8 {
                let mut x: u8 = 0;
                let q = &mut x;
                {
                    let p = &mut *q;
                    *p = v;
                }
                *q
            }
        }
    };
}
imp_t!(A);
imp_t!(B);

fn pick() -> Box<dyn T> {
    if kani::any() { Box::new(A) } else { Box::new(B) }
}
fn one() -> Box<dyn T> {
    Box::new(A)
}

#[kani::proof]
fn bug_dyn2_local_alias() {
    assert!(pick().local_alias(255) == 0);
}
#[kani::proof]
fn safe_dyn2_local_alias() {
    assert!(pick().local_alias(255) == 255);
}
#[kani::proof]
fn bug_dyn1_local_alias() {
    assert!(one().local_alias(255) == 0);
}
#[kani::proof]
fn safe_dyn1_local_alias() {
    assert!(one().local_alias(255) == 255);
}
#[kani::proof]
fn bug_dyn2_struct_alias() {
    assert!(pick().struct_alias(255) == 0);
}
#[kani::proof]
fn safe_dyn2_struct_alias() {
    assert!(pick().struct_alias(255) == 255);
}
#[kani::proof]
fn bug_dyn2_arr_alias() {
    assert!(pick().arr_alias(255) == 0);
}
#[kani::proof]
fn safe_dyn2_arr_alias() {
    assert!(pick().arr_alias(255) == 255);
}
#[kani::proof]
fn bug_dyn2_loop_alias() {
    assert!(pick().loop_alias(255) == 0);
}
#[kani::proof]
fn bug_dyn2_add_after_alias() {
    sink(pick().add_after_alias(255));
}
#[kani::proof]
fn safe_dyn2_add_after_alias() {
    assert!(pick().add_after_alias(254) == 255);
}
#[kani::proof]
fn bug_dyn2_as_mut_alias() {
    assert!(pick().as_mut_alias(255) == 0);
}
#[kani::proof]
fn bug_dyn2_opt_arg() {
    let mut a: u8 = 7;
    pick().opt_arg(Some(&mut a));
    assert!(a == 7);
}
#[kani::proof]
fn safe_dyn2_opt_arg() {
    let mut a: u8 = 7;
    pick().opt_arg(Some(&mut a));
    assert!(a == 200);
}
#[kani::proof]
fn bug_dyn2_opt_local() {
    let mut a: u8 = 7;
    pick().opt_local(&mut a);
    assert!(a == 7);
}
#[kani::proof]
fn bug_dyn2_field_reborrow() {
    let mut s = S { a: 7, b: 0 };
    pick().field_reborrow(&mut s);
    assert!(s.a == 7);
}

#[kani::proof]
fn bug_dyn2_two_referents() {
    let c: bool = kani::any();
    assert!(pick().two_referents(c, 9) == 0);
}
#[kani::proof]
fn safe_dyn2_two_referents() {
    let c: bool = kani::any();
    assert!(pick().two_referents(c, 9) == 9);
}
#[kani::proof]
fn bug_dyn2_reborrow_chain() {
    assert!(pick().reborrow_chain(9) == 0);
}
#[kani::proof]
fn safe_dyn2_reborrow_chain() {
    assert!(pick().reborrow_chain(9) == 9);
}
#[kani::proof]
fn bug_dyn2_stale_outer() {
    assert!(pick().stale_outer(9) == 0);
}

// Other front doors: a Fn-trait object, a boxed FnMut, the fn_inline walker
// (a self-recursive callee is never MIR-inlined) and a host fn pointer.
#[kani::proof]
fn bug_dynfn_local_alias() {
    let c1 = |v: u8| {
        let mut x: u8 = 0;
        let p = &mut x;
        *p = v;
        x
    };
    let c2 = |v: u8| {
        let mut x: u8 = 1;
        let p = &mut x;
        *p = v;
        x
    };
    let f: &dyn Fn(u8) -> u8 = if kani::any() { &c1 } else { &c2 };
    assert!(f(255) <= 1);
}
#[kani::proof]
fn bug_boxfnmut_local_alias() {
    let mut f: Box<dyn FnMut(u8) -> u8> = if kani::any() {
        Box::new(|v: u8| {
            let mut x: u8 = 0;
            let p = &mut x;
            *p = v;
            x
        })
    } else {
        Box::new(|v: u8| {
            let mut x: u8 = 1;
            let p = &mut x;
            *p = v;
            x
        })
    };
    assert!(f(255) <= 1);
}
fn rec(n: u8, v: u8) -> u8 {
    if n == 0 {
        let mut x: u8 = 0;
        let p = &mut x;
        *p = v;
        x
    } else {
        rec(n - 1, v)
    }
}
#[kani::proof]
#[kani::unwind(4)]
fn bug_rec_local_alias() {
    assert!(rec(1, 255) == 0);
}
#[kani::proof]
#[kani::unwind(4)]
fn safe_rec_local_alias() {
    assert!(rec(1, 255) == 255);
}
fn la1(v: u8) -> u8 {
    let mut x: u8 = 0;
    let p = &mut x;
    *p = v;
    x
}
fn la2(v: u8) -> u8 {
    let mut x: u8 = 1;
    let p = &mut x;
    *p = v;
    x
}
#[kani::proof]
fn bug_fnptr_local_alias() {
    let f: fn(u8) -> u8 = if kani::any() { la1 } else { la2 };
    assert!(f(255) <= 1);
}
#[kani::proof]
fn safe_fnptr_local_alias() {
    let f: fn(u8) -> u8 = if kani::any() { la1 } else { la2 };
    assert!(f(255) == 255);
}

// ---- M2: a store through a pointer that is not an argument local ----------
// Two impls, the receiver statically `A`: the dyn door's constant-vtable
// shortcut walks ONE body, so the branch-arm rule does not see the store.
pub trait M {
    fn raw_copy(&self, a: &mut u8);
    fn struct_arg(&self, w: W<'_>);
    fn tuple_arg(&self, t: (&mut u8, u8));
    fn local_struct(&self, a: &mut u8);
}
pub struct MA;
pub struct MB;
macro_rules! imp_m {
    ($t:ty) => {
        impl M for $t {
            fn raw_copy(&self, a: &mut u8) {
                let p = a as *mut u8;
                unsafe {
                    *p = 200;
                }
            }
            fn struct_arg(&self, w: W<'_>) {
                *w.r = 200;
            }
            fn tuple_arg(&self, t: (&mut u8, u8)) {
                *t.0 = 200;
            }
            fn local_struct(&self, a: &mut u8) {
                let w = W { r: a, k: 0 };
                *w.r = 200;
            }
        }
    };
}
imp_m!(MA);
imp_m!(MB);
fn one_m() -> Box<dyn M> {
    Box::new(MA)
}

#[kani::proof]
fn bug_dyn1_raw_copy() {
    let mut a: u8 = 7;
    one_m().raw_copy(&mut a);
    assert!(a == 7);
}
#[kani::proof]
fn safe_dyn1_raw_copy() {
    let mut a: u8 = 7;
    one_m().raw_copy(&mut a);
    assert!(a == 200);
}
#[kani::proof]
fn bug_dyn1_struct_arg() {
    let mut a: u8 = 7;
    one_m().struct_arg(W { r: &mut a, k: 0 });
    assert!(a == 7);
}
#[kani::proof]
fn bug_dyn1_tuple_arg() {
    let mut a: u8 = 7;
    one_m().tuple_arg((&mut a, 0));
    assert!(a == 7);
}
#[kani::proof]
fn bug_dyn1_local_struct() {
    let mut a: u8 = 7;
    one_m().local_struct(&mut a);
    assert!(a == 7);
}
fn v1(x: &mut u8) {
    let p = x as *mut u8;
    unsafe {
        *p = 200;
    }
}
fn v2(x: &mut u8) {
    let p = x as *mut u8;
    unsafe {
        *p = 201;
    }
}
#[kani::proof]
fn bug_fnptr_raw_copy() {
    let mut a: u8 = 7;
    let f: fn(&mut u8) = if kani::any() { v1 } else { v2 };
    f(&mut a);
    assert!(a == 7);
}

// ---- M3: a closure behind a host fn pointer writes a `&mut` argument ------
#[kani::proof]
fn bug_fnptr_closure_write() {
    let mut a: u8 = 7;
    let mut b: u8 = 7;
    let f: fn(&mut u8, &mut u8) = if kani::any() {
        |_x: &mut u8, y: &mut u8| {
            *y = 200;
        }
    } else {
        |_x: &mut u8, y: &mut u8| {
            *y = 201;
        }
    };
    f(&mut a, &mut b);
    assert!(b == 7);
}
#[kani::proof]
fn safe_fnptr_closure_write() {
    let mut a: u8 = 7;
    let mut b: u8 = 7;
    let f: fn(&mut u8, &mut u8) = if kani::any() {
        |_x: &mut u8, y: &mut u8| {
            *y = 200;
        }
    } else {
        |_x: &mut u8, y: &mut u8| {
            *y = 201;
        }
    };
    f(&mut a, &mut b);
    assert!(a == 7 && b >= 200);
}

// ---- M6: a walked store to a static the harness never names ---------------
static mut H: u8 = 0;
static mut K: u8 = 0;
pub trait Hs {
    fn to_h(&self);
}
pub struct HA;
pub struct HB;
impl Hs for HA {
    fn to_h(&self) {
        unsafe {
            H = 9;
        }
    }
}
impl Hs for HB {
    fn to_h(&self) {
        unsafe {
            H = 9;
        }
    }
}
fn one_h() -> Box<dyn Hs> {
    Box::new(HA)
}
// Nothing writes K.
#[kani::proof]
fn bug_callee_static_mirror() {
    one_h().to_h();
    assert!(unsafe { K } == 9);
}
#[kani::proof]
fn safe_callee_static_mirror() {
    one_h().to_h();
    assert!(unsafe { K } == 0);
}

// ---- F2 residual: a reference in a by-value aggregate, read through a field
pub trait Ag {
    fn agg_ref_read(&self, w: Wr<'_>) -> u8;
}
pub struct GA;
pub struct GB;
impl Ag for GA {
    fn agg_ref_read(&self, w: Wr<'_>) -> u8 {
        unsafe { (*w.r).unchecked_add(1) }
    }
}
impl Ag for GB {
    fn agg_ref_read(&self, w: Wr<'_>) -> u8 {
        unsafe { (*w.r).unchecked_add(1) }
    }
}
fn pick_ag() -> Box<dyn Ag> {
    if kani::any() { Box::new(GA) } else { Box::new(GB) }
}
#[kani::proof]
fn bug_agg_ref_read() {
    let x: u8 = 255;
    sink(pick_ag().agg_ref_read(Wr { r: &x, k: 0 }));
}
