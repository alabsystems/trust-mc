// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (precision pin) -- a field store before a `Box<dyn>`
//! coercion (`ptr::write`, `mem::replace`) in a harness that also reallocates
//! another object or allocates in a loop.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_ptr_write_coerce_with_realloc   -> FAILED ('assertion failed: o.get() < 255')
//!   safe_ptr_write_coerce_with_realloc  -> SUCCESSFUL
//!   bug_replace_coerce_with_loop_alloc  -> FAILED ('assertion failed: o.get() < 255')
//!   safe_replace_coerce_with_loop_alloc -> SUCCESSFUL
//!
//! WHAT IS PINNED (review of fix/chc-lost-writes round 6, finding 5). Without
//! the second object these field stores are decided in about 0.3 s
//! (walker_dyn_heap_write_dual.rs, the timing rows). Here the bug rows end
//! FAILED Unknown at the budget, on main and on the branch alike, and
//! `safe_replace_coerce_with_loop_alloc` is a false failure (FAILED Unknown):
//! not a soundness issue, a precision cost this file makes visible.
//!
//! Measured causes (2026-09-27, a diagnostic build of round 7 that printed the
//! constant-propagation guards' inputs):
//! - realloc: `has_scalarized_obj_size_bounds` fires, as designed. The
//!   always-moved realloc model copies the old object through a window of the
//!   OLD size (`add_always_moved_realloc_copy_constraints`) and aliases the old
//!   object's region, so the 2-byte new object carries scalarized cells past
//!   its size (a 4-byte `mem_u32` cell at offset 0, region bytes 2 and 3). An
//!   out-of-bounds cell is exactly what the guard keeps unreduced; the emitted
//!   VC with and without `TRUST_MC_NO_CONST_PROP=1` is byte-identical. The safe
//!   twin still proves.
//! - loop allocation: the guard does NOT fire (every scalarized cell is inside
//!   its object; constant propagation runs and takes the VC from 69 rules to
//!   44). What stays undecided is the loop, whose relation carries memory
//!   arrays, around a dyn call with two candidate bodies: with `DV` as the only
//!   implementer of `Tv` the safe row proves in 0.02 s.

#![allow(unused)]
#[inline(never)]
fn sink<T>(_value: T) {}
pub trait Tv {
    fn get(&self) -> u8;
}
pub struct DV {
    a: u8,
    b: u8,
}
impl Tv for DV {
    fn get(&self) -> u8 {
        self.a
    }
}
// A second implementer, as in the review's probe file: the dyn call `o.get()`
// then has two candidate bodies. With `DV` alone the safe rows prove at once.
pub struct D8 {
    a: u8,
    h: u8,
}
impl Tv for D8 {
    fn get(&self) -> u8 {
        self.a.wrapping_add(self.h)
    }
}

#[kani::proof]
fn bug_ptr_write_coerce_with_realloc() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    unsafe { core::ptr::write(&mut d.a as *mut u8, 255); }
    let o: Box<dyn Tv> = d;
    unsafe {
        let l = std::alloc::Layout::from_size_align(4, 4).unwrap();
        let p = std::alloc::alloc(l);
        if !p.is_null() {
            let q = std::alloc::realloc(p, l, 2);
            if !q.is_null() {
                std::alloc::dealloc(q, std::alloc::Layout::from_size_align(2, 4).unwrap());
            }
        }
    }
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_ptr_write_coerce_with_realloc() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    unsafe { core::ptr::write(&mut d.a as *mut u8, 200); }
    let o: Box<dyn Tv> = d;
    unsafe {
        let l = std::alloc::Layout::from_size_align(4, 4).unwrap();
        let p = std::alloc::alloc(l);
        if !p.is_null() {
            let q = std::alloc::realloc(p, l, 2);
            if !q.is_null() {
                std::alloc::dealloc(q, std::alloc::Layout::from_size_align(2, 4).unwrap());
            }
        }
    }
    assert!(o.get() == 200);
}

#[kani::proof]
fn bug_replace_coerce_with_loop_alloc() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    let _ = core::mem::replace(&mut d.a, 255);
    let o: Box<dyn Tv> = d;
    for i in 0..2u8 {
        let b = Box::new(i);
        sink(b);
    }
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_replace_coerce_with_loop_alloc() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    let _ = core::mem::replace(&mut d.a, 200);
    let o: Box<dyn Tv> = d;
    for i in 0..2u8 {
        let b = Box::new(i);
        sink(b);
    }
    assert!(o.get() == 200);
}
