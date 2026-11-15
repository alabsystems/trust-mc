// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- dynamic dispatch with several impls of the dispatched trait (a Box and a
//! reference receiver, a store before the coercion, a raw-pointer impl as the runtime type and as
//! another candidate, its read past an array), a Box<dyn FnMut> called through a helper, and a
//! store through an Rc beside a local Cell (review of fix/chc-lost-writes, lostwrite round 1,
//! measurement of the repair). Once an access through a symbolic object lane took a bound, the
//! walker's eager read of a receiver's fields and every dispatch arm's accesses, checked with no
//! guard, failed the safe rows; the eager read takes no lane bound and an arm's checks are weakened
//! by its dispatch condition.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   bug_box_dyn_several_impls_read               -> FAILED ('assertion failed: o.get() != a')
//!   safe_box_dyn_several_impls_read              -> SUCCESSFUL
//!   bug_box_dyn_several_impls_write_then_coerce  -> FAILED ('assertion failed: o.get() < 200')
//!   safe_box_dyn_several_impls_write_then_coerce -> SUCCESSFUL
//!   bug_ref_dyn_several_impls_read               -> FAILED ('assertion failed: o.get() != a')
//!   safe_ref_dyn_several_impls_read              -> SUCCESSFUL
//!   bug_raw_ptr_arm_runtime_read                 -> FAILED ('assertion failed: o.get() != byte')
//!   safe_raw_ptr_arm_runtime_read                -> SUCCESSFUL
//!   bug_raw_ptr_arm_past_the_byte                -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_raw_ptr_arm_last_byte                   -> SUCCESSFUL
//!   bug_box_dyn_fn_mut_promoted_ref              -> FAILED ('assertion failed: x == 1')
//!   safe_box_dyn_fn_mut_promoted_ref             -> SUCCESSFUL
//!   bug_box_dyn_fn_mut_closure                   -> FAILED ('assertion failed: x == 1')
//!   safe_box_dyn_fn_mut_closure                  -> SUCCESSFUL
//!   bug_rc_cell_beside_local                     -> FAILED ('assertion failed: b.get() == 0')
//!   safe_rc_cell_beside_local                    -> SUCCESSFUL
//!
use std::cell::Cell;
use std::rc::Rc;

pub trait Tv {
    fn get(&self) -> u8;
}
pub struct DV {
    pub a: u8,
    pub b: u8,
}
impl Tv for DV {
    fn get(&self) -> u8 {
        self.a
    }
}
pub struct D3 {
    pub x: ((u8, u8), u8),
    pub z: u8,
}
impl Tv for D3 {
    fn get(&self) -> u8 {
        (self.x.0).0
    }
}
pub struct DA {
    pub x: [(u8, u8); 2],
    pub z: u8,
}
impl Tv for DA {
    fn get(&self) -> u8 {
        self.z
    }
}
pub struct DW {
    pub w: [u64; 4],
}
impl Tv for DW {
    fn get(&self) -> u8 {
        self.w[3] as u8
    }
}
pub struct DP {
    pub p: *const u8,
}
impl Tv for DP {
    fn get(&self) -> u8 {
        unsafe { *self.p }
    }
}

/// Coerces every other impl, so each is a dispatch candidate of `get`.
pub fn keep_impls_alive(k: u8) -> u8 {
    let byte = 9u8;
    let o: Box<dyn Tv> = match k {
        0 => Box::new(D3 { x: ((1, 2), 3), z: 4 }),
        1 => Box::new(DA { x: [(1, 2), (3, 4)], z: 5 }),
        2 => Box::new(DW { w: [0, 0, 0, 6] }),
        _ => Box::new(DP { p: &byte }),
    };
    o.get()
}

#[kani::proof]
fn bug_box_dyn_several_impls_read() {
    let a: u8 = kani::any();
    let o: Box<dyn Tv> = Box::new(DV { a, b: 1 });
    assert!(o.get() != a);
}

#[kani::proof]
fn safe_box_dyn_several_impls_read() {
    let a: u8 = kani::any();
    let o: Box<dyn Tv> = Box::new(DV { a, b: 1 });
    assert!(o.get() == a);
}

#[kani::proof]
fn bug_box_dyn_several_impls_write_then_coerce() {
    let a: u8 = kani::any();
    let mut d = Box::new(DV { a, b: 1 });
    d.a = 200;
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 200);
}

#[kani::proof]
fn safe_box_dyn_several_impls_write_then_coerce() {
    let a: u8 = kani::any();
    let mut d = Box::new(DV { a, b: 1 });
    d.a = 200;
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn bug_ref_dyn_several_impls_read() {
    let a: u8 = kani::any();
    let d = DV { a, b: 1 };
    let o: &dyn Tv = &d;
    assert!(o.get() != a);
}

#[kani::proof]
fn safe_ref_dyn_several_impls_read() {
    let a: u8 = kani::any();
    let d = DV { a, b: 1 };
    let o: &dyn Tv = &d;
    assert!(o.get() == a);
}

#[kani::proof]
fn bug_raw_ptr_arm_runtime_read() {
    let byte: u8 = kani::any();
    let o: Box<dyn Tv> = Box::new(DP { p: &byte });
    assert!(o.get() != byte);
}

#[kani::proof]
fn safe_raw_ptr_arm_runtime_read() {
    let byte: u8 = kani::any();
    let o: Box<dyn Tv> = Box::new(DP { p: &byte });
    assert!(o.get() == byte);
}

#[kani::proof]
fn bug_raw_ptr_arm_past_the_byte() {
    let bytes = [1u8, 2];
    let p = bytes.as_ptr().wrapping_add(2);
    let o: Box<dyn Tv> = Box::new(DP { p });
    let _ = o.get();
}

#[kani::proof]
fn safe_raw_ptr_arm_last_byte() {
    let bytes = [1u8, 2];
    let p = bytes.as_ptr().wrapping_add(1);
    let o: Box<dyn Tv> = Box::new(DP { p });
    assert!(o.get() == 2);
}

fn takes_dyn_fun(mut fun: Box<dyn FnMut(&mut i32)>, x_ptr: &mut i32) {
    fun(x_ptr)
}
fn mut_i32_ptr(x: &mut i32) {
    *x = x.wrapping_add(1);
}

#[kani::proof]
fn bug_box_dyn_fn_mut_promoted_ref() {
    let mut x = 1;
    takes_dyn_fun(Box::new(&mut_i32_ptr), &mut x);
    assert!(x == 1);
}

#[kani::proof]
fn safe_box_dyn_fn_mut_promoted_ref() {
    let mut x = 1;
    takes_dyn_fun(Box::new(&mut_i32_ptr), &mut x);
    assert!(x == 2);
}

#[kani::proof]
fn bug_box_dyn_fn_mut_closure() {
    let mut x = 1;
    let k: i32 = kani::any();
    kani::assume(k > 0 && k < 10);
    takes_dyn_fun(Box::new(move |v: &mut i32| *v += k), &mut x);
    assert!(x == 1);
}

#[kani::proof]
fn safe_box_dyn_fn_mut_closure() {
    let mut x = 1;
    let k: i32 = kani::any();
    kani::assume(k > 0 && k < 10);
    takes_dyn_fun(Box::new(move |v: &mut i32| *v += k), &mut x);
    assert!(x == 1 + k);
}

#[kani::proof]
fn bug_rc_cell_beside_local() {
    let a = Cell::new(1u32);
    let b = Rc::new(Cell::new(0u32));
    b.set(7);
    assert!(a.get() == 1);
    assert!(b.get() == 0);
}

#[kani::proof]
fn safe_rc_cell_beside_local() {
    let a = Cell::new(1u32);
    let b = Rc::new(Cell::new(0u32));
    b.set(7);
    assert!(a.get() == 1);
    assert!(b.get() == 7);
}
