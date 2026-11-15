// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- the heap view ledger, the element-store referent guard and
//! the symbolic-lane bound against programs main got right on both twins, and the
//! false certificates and missed bug main and fix/chc-lost-writes shared (review of
//! fix/chc-lost-writes, lostwrite track round 1, findings 3, 4, 9 and 10).
//!
//! * A load whose value no rule uses is not judged (a `Box<dyn>` coercion's
//!   declined alias load), an element store traced through the MIR to a `Box`'s
//!   payload is exact, and a later store of a key masks an earlier store that left
//!   it stale.
//! * The bound of an access through a symbolic object lane is certified, and the
//!   size choice includes the global objects (a static's `&[u8]` referents).
//! * A read through a pointer the encoder cannot place, of a view nothing that may
//!   run before it wrote, is a free cell, never a certificate; `vec![x; n]` with a
//!   count that does not fold returns a free pointer word, accounted; an `Rc` value
//!   aligned beyond 16 fails closed.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_elem_store_then_dyn_read            -> SUCCESSFUL
//!   bug_elem_store_then_dyn_read             -> FAILED ('assertion failed: d.get() == 4')
//!   safe_box_2d_row_store_elem_addr_read     -> SUCCESSFUL
//!   bug_box_2d_row_store_elem_addr_read      -> FAILED ('assertion failed: unsafe { *q } == 3')
//!   safe_box_2d_row_store_wide_row_read      -> SUCCESSFUL
//!   bug_box_2d_row_store_wide_row_read       -> FAILED ('assertion failed: w == 0x0004_0003')
//!   bug_dyn_from_call_oob                    -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_static_slice_wrapping_oob            -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_static_slice_wrapping_inbounds      -> SUCCESSFUL
//!   safe_box_u8x4_read_as_u32                -> SUCCESSFUL
//!   bug_box_u8x4_read_as_u32_wrong_value     -> FAILED ('assertion failed: v == 0x0403_0200')
//!   safe_vec_symbolic_len_ptr_read           -> SUCCESSFUL
//!   bug_vec_symbolic_len_ptr_read_oob        -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_rc_align32_last_byte                -> SUCCESSFUL
//!   bug_rc_align32_past                      -> FAILED ('dereference failure: pointer outside object bounds')
//!
#![allow(unused)]
use std::rc::Rc;

trait Tv {
    fn get(&self) -> u16;
}
struct DV {
    a: u16,
    b: u16,
}
struct DA {
    x: [u16; 4],
}
impl Tv for DV {
    fn get(&self) -> u16 {
        self.b
    }
}
impl Tv for DA {
    fn get(&self) -> u16 {
        self.x[3]
    }
}

#[kani::proof]
fn safe_elem_store_then_dyn_read() {
    let mut b = Box::new(DA { x: [1, 2, 3, 4] });
    let p: *mut [u16; 4] = &mut b.x;
    unsafe { (*p)[3] = 8 };
    let d: Box<dyn Tv> = b;
    assert!(d.get() == 8);
}

#[kani::proof]
fn bug_elem_store_then_dyn_read() {
    let mut b = Box::new(DA { x: [1, 2, 3, 4] });
    let p: *mut [u16; 4] = &mut b.x;
    unsafe { (*p)[3] = 8 };
    let d: Box<dyn Tv> = b;
    assert!(d.get() == 4);
}

#[kani::proof]
fn safe_box_2d_row_store_elem_addr_read() {
    let mut b = Box::new([[1u16, 2], [3, 4]]);
    let p: *mut [u16; 2] = &mut b[1];
    unsafe { (*p)[0] = 9 };
    let q = &b[1][0] as *const u16;
    assert!(unsafe { *q } == 9);
}

#[kani::proof]
fn bug_box_2d_row_store_elem_addr_read() {
    let mut b = Box::new([[1u16, 2], [3, 4]]);
    let p: *mut [u16; 2] = &mut b[1];
    unsafe { (*p)[0] = 9 };
    let q = &b[1][0] as *const u16;
    assert!(unsafe { *q } == 3);
}

#[kani::proof]
fn safe_box_2d_row_store_wide_row_read() {
    let mut b = Box::new([[1u16, 2], [3, 4]]);
    let p: *mut [u16; 2] = &mut b[1];
    unsafe { (*p)[0] = 9 };
    let w = unsafe { *(&b[1] as *const [u16; 2] as *const u32) };
    assert!(w == 0x0004_0009);
}

#[kani::proof]
fn bug_box_2d_row_store_wide_row_read() {
    let mut b = Box::new([[1u16, 2], [3, 4]]);
    let p: *mut [u16; 2] = &mut b[1];
    unsafe { (*p)[0] = 9 };
    let w = unsafe { *(&b[1] as *const [u16; 2] as *const u32) };
    assert!(w == 0x0004_0003);
}

trait T3 {
    fn get(&self, k: usize) -> u8;
}
struct A3 {
    xs: [u8; 3],
}
impl T3 for A3 {
    fn get(&self, k: usize) -> u8 {
        unsafe { *self.xs.as_ptr().add(k) }
    }
}
struct B3 {
    y: u8,
}
impl T3 for B3 {
    fn get(&self, k: usize) -> u8 {
        self.y
    }
}
fn make(c: bool) -> Box<dyn T3> {
    if c { Box::new(A3 { xs: [1, 2, 3] }) } else { Box::new(B3 { y: 4 }) }
}

#[kani::proof]
fn bug_dyn_from_call_oob() {
    let o = make(kani::any());
    let k: usize = kani::any();
    kani::assume(k <= 3);
    let v = o.get(k);
    assert!(v == v);
}

static SLICES: [&[u8]; 2] = [b"abcdefghij", b"klmnopqrst"];

#[kani::proof]
fn bug_static_slice_wrapping_oob() {
    let mut a: u8 = 0;
    let pa = &mut a as *mut u8;
    unsafe { *pa = 7 };
    let j: usize = kani::any();
    kani::assume(j < 2);
    let s = SLICES[j];
    let p = s.as_ptr().wrapping_add(10);
    let v = unsafe { *p };
    assert!(v == v);
}

#[kani::proof]
fn safe_static_slice_wrapping_inbounds() {
    let j: usize = kani::any();
    kani::assume(j < 2);
    let s = SLICES[j];
    let p = s.as_ptr().wrapping_add(9);
    let v = unsafe { *p };
    assert!(v == b'j' || v == b't');
}

#[kani::proof]
fn safe_box_u8x4_read_as_u32() {
    let bx: Box<[u8; 4]> = Box::new([1, 2, 3, 4]);
    let v = unsafe { *(bx.as_ptr() as *const u32) };
    assert!(v == 0x0403_0201);
}

#[kani::proof]
fn bug_box_u8x4_read_as_u32_wrong_value() {
    let bx: Box<[u8; 4]> = Box::new([1, 2, 3, 4]);
    let v = unsafe { *(bx.as_ptr() as *const u32) };
    assert!(v == 0x0403_0200);
}

#[kani::proof]
fn safe_vec_symbolic_len_ptr_read() {
    let n: usize = kani::any();
    kani::assume(n >= 1 && n <= 4);
    let v: Vec<u8> = vec![3u8; n];
    let p = v.as_ptr().wrapping_add(n - 1);
    let x = unsafe { *p };
    assert!(x == 3);
}

#[kani::proof]
fn bug_vec_symbolic_len_ptr_read_oob() {
    let n: usize = kani::any();
    kani::assume(n >= 1 && n <= 4);
    let v: Vec<u8> = vec![3u8; n];
    let p = v.as_ptr().wrapping_add(n);
    let x = unsafe { *p };
    assert!(x == x);
}

#[repr(align(32))]
struct A32([u8; 32]);

#[kani::proof]
fn safe_rc_align32_last_byte() {
    let rc = Rc::new(A32([3; 32]));
    let p = Rc::as_ptr(&rc) as *const u8;
    let v = unsafe { *p.wrapping_add(31) };
    assert!(v == 3);
}

#[kani::proof]
fn bug_rc_align32_past() {
    let rc = Rc::new(A32([3; 32]));
    let p = Rc::as_ptr(&rc) as *const u8;
    let v = unsafe { *p.wrapping_add(32) };
    assert!(v == v);
}
