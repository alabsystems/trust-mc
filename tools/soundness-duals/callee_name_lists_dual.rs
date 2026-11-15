// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a pun store or a static byte view handed to a callee whose
//! leaf name is on one of the untyped-view nets' callee lists (a user `add`,
//! `read`, `put`, `eq`; core's `PartialEq::eq` and `Ord::cmp`; trait-object
//! methods of the same names). The nets decide a call by its leaf name, and a
//! walked callee's body is scanned with its arguments addressing memory outside
//! it; these rows pin that such calls fail closed (review of fix/chc-lost-writes
//! round 3, finding 3: every row held on the round-8 bundle; main has missed
//! bugs and false certificates here).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_static_byte_in_callee_named_add         -> SUCCESSFUL
//!   bug_static_byte_in_callee_named_add          -> FAILED ('assertion failed: add(p, 2) == 2')
//!   safe_static_byte_in_callee_named_add_nostore -> SUCCESSFUL
//!   safe_static_byte_in_callee_named_eq          -> SUCCESSFUL
//!   bug_static_byte_in_callee_named_eq           -> FAILED ('assertion failed: eq(p, 2)')
//!   safe_static_byte_core_eq                     -> SUCCESSFUL
//!   bug_static_byte_core_eq                      -> FAILED ('assertion failed: r.eq(&2)')
//!   safe_static_byte_core_cmp                    -> SUCCESSFUL
//!   bug_static_byte_core_cmp                     -> FAILED ('assertion failed: r.cmp(&2) == Ordering::Equal')
//!   bug_pun_store_in_callee_named_add            -> FAILED ('assertion failed: *y != 7')
//!   safe_pun_store_in_callee_named_add           -> SUCCESSFUL
//!   bug_pun_store_in_callee_named_read           -> FAILED ('assertion failed: *y != 7')
//!   safe_pun_store_in_callee_named_read          -> SUCCESSFUL
//!   bug_pun_store_in_callee_named_put            -> FAILED ('assertion failed: *y != 7')
//!   safe_static_byte_dyn_add                     -> SUCCESSFUL
//!   bug_static_byte_dyn_add                      -> FAILED ('assertion failed: r.add(p, 2) == 2')
//!   safe_static_byte_dyn_add_nostore             -> SUCCESSFUL
//!   safe_static_byte_dyn_eq                      -> SUCCESSFUL
//!   bug_pun_store_dyn_read                       -> FAILED ('assertion failed: *y != 7')
//!   safe_pun_store_dyn_read                      -> SUCCESSFUL
//!
#![allow(static_mut_refs, unused)]
use std::cmp::Ordering;
use std::ptr::{addr_of, addr_of_mut};

// ---- net 2: the byte view of a static read inside a callee named `add` ----
static mut SA: [u16; 2] = [1, 0x0102];
static mut SB: [u16; 2] = [1, 0x0102];
static SC: [u16; 2] = [1, 0x0102];

#[inline(never)]
fn add(p: *const u8, k: usize) -> u8 {
    unsafe { *p.wrapping_add(k) }
}

#[kani::proof]
fn safe_static_byte_in_callee_named_add() {
    unsafe {
        SA[1] = 0x0304;
    }
    let p = unsafe { addr_of!(SA) } as *const u8;
    assert!(add(p, 2) == 4);
}

#[kani::proof]
fn bug_static_byte_in_callee_named_add() {
    unsafe {
        SB[1] = 0x0304;
    }
    let p = unsafe { addr_of!(SB) } as *const u8;
    assert!(add(p, 2) == 2);
}

#[kani::proof]
fn safe_static_byte_in_callee_named_add_nostore() {
    let p = addr_of!(SC) as *const u8;
    assert!(add(p, 2) == 2);
}

// ---- net 2: the byte view read inside a callee named `eq` ----
static mut SD: [u16; 2] = [1, 0x0102];
static mut SE: [u16; 2] = [1, 0x0102];

#[inline(never)]
fn eq(p: *const u8, v: u8) -> bool {
    unsafe { *p.add(2) == v }
}

#[kani::proof]
fn safe_static_byte_in_callee_named_eq() {
    unsafe {
        SD[1] = 0x0304;
    }
    let p = unsafe { addr_of!(SD) } as *const u8;
    assert!(eq(p, 4));
}

#[kani::proof]
fn bug_static_byte_in_callee_named_eq() {
    unsafe {
        SE[1] = 0x0304;
    }
    let p = unsafe { addr_of!(SE) } as *const u8;
    assert!(eq(p, 2));
}

// ---- net 2: the byte view read by core's PartialEq::eq / Ord::cmp ----
static mut SF: [u16; 2] = [1, 0x0102];
static mut SG: [u16; 2] = [1, 0x0102];
static mut SH: [u16; 2] = [1, 0x0102];
static mut SI: [u16; 2] = [1, 0x0102];

#[kani::proof]
fn safe_static_byte_core_eq() {
    unsafe {
        SF[1] = 0x0304;
    }
    let p = unsafe { addr_of!(SF) } as *const u8;
    let r: &u8 = unsafe { &*p.add(2) };
    assert!(r.eq(&4));
}

#[kani::proof]
fn bug_static_byte_core_eq() {
    unsafe {
        SG[1] = 0x0304;
    }
    let p = unsafe { addr_of!(SG) } as *const u8;
    let r: &u8 = unsafe { &*p.add(2) };
    assert!(r.eq(&2));
}

#[kani::proof]
fn safe_static_byte_core_cmp() {
    unsafe {
        SH[1] = 0x0304;
    }
    let p = unsafe { addr_of!(SH) } as *const u8;
    let r: &u8 = unsafe { &*p.add(2) };
    assert!(r.cmp(&4) == Ordering::Equal);
}

#[kani::proof]
fn bug_static_byte_core_cmp() {
    unsafe {
        SI[1] = 0x0304;
    }
    let p = unsafe { addr_of!(SI) } as *const u8;
    let r: &u8 = unsafe { &*p.add(2) };
    assert!(r.cmp(&2) == Ordering::Equal);
}

// ---- net 1: a pun written through inside a callee named `add` / `read` ----
mod w {
    #[inline(never)]
    pub fn add(q: *mut usize, v: usize) {
        unsafe {
            *q = v;
        }
    }
    #[inline(never)]
    pub fn read(q: *mut usize, v: usize) {
        unsafe {
            *q = v;
        }
    }
}

#[kani::proof]
fn bug_pun_store_in_callee_named_add() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q = addr_of_mut!(a) as *mut usize;
    w::add(q, yp as usize);
    unsafe {
        *a = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_pun_store_in_callee_named_add() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q = addr_of_mut!(a) as *mut usize;
    w::add(q, yp as usize);
    unsafe {
        *a = 7;
    }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_pun_store_in_callee_named_read() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q = addr_of_mut!(a) as *mut usize;
    w::read(q, yp as usize);
    unsafe {
        *a = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_pun_store_in_callee_named_read() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q = addr_of_mut!(a) as *mut usize;
    w::read(q, yp as usize);
    unsafe {
        *a = 7;
    }
    assert!(*bx == 0);
}

// control: the same helper under a name on no list
mod v {
    #[inline(never)]
    pub fn put(q: *mut usize, v: usize) {
        unsafe {
            *q = v;
        }
    }
}

#[kani::proof]
fn bug_pun_store_in_callee_named_put() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q = addr_of_mut!(a) as *mut usize;
    v::put(q, yp as usize);
    unsafe {
        *a = 7;
    }
    assert!(*y != 7);
}

pub trait Rd {
    fn add(&self, p: *const u8, k: usize) -> u8;
    fn eq(&self, p: *const u8, v: u8) -> bool;
    fn read(&self, q: *mut usize, v: usize);
}

pub struct Impl1;
impl Rd for Impl1 {
    fn add(&self, p: *const u8, k: usize) -> u8 {
        unsafe { *p.wrapping_add(k) }
    }
    fn eq(&self, p: *const u8, v: u8) -> bool {
        unsafe { *p.add(2) == v }
    }
    fn read(&self, q: *mut usize, v: usize) {
        unsafe {
            *q = v;
        }
    }
}

static mut DA: [u16; 2] = [1, 0x0102];
static mut DB: [u16; 2] = [1, 0x0102];
static DC: [u16; 2] = [1, 0x0102];
static mut DD: [u16; 2] = [1, 0x0102];

#[kani::proof]
fn safe_static_byte_dyn_add() {
    let r: &dyn Rd = &Impl1;
    unsafe {
        DA[1] = 0x0304;
    }
    let p = unsafe { addr_of!(DA) } as *const u8;
    assert!(r.add(p, 2) == 4);
}

#[kani::proof]
fn bug_static_byte_dyn_add() {
    let r: &dyn Rd = &Impl1;
    unsafe {
        DB[1] = 0x0304;
    }
    let p = unsafe { addr_of!(DB) } as *const u8;
    assert!(r.add(p, 2) == 2);
}

#[kani::proof]
fn safe_static_byte_dyn_add_nostore() {
    let r: &dyn Rd = &Impl1;
    let p = addr_of!(DC) as *const u8;
    assert!(r.add(p, 2) == 2);
}

#[kani::proof]
fn safe_static_byte_dyn_eq() {
    let r: &dyn Rd = &Impl1;
    unsafe {
        DD[1] = 0x0304;
    }
    let p = unsafe { addr_of!(DD) } as *const u8;
    assert!(r.eq(p, 4));
}

#[kani::proof]
fn bug_pun_store_dyn_read() {
    let r: &dyn Rd = &Impl1;
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q = addr_of_mut!(a) as *mut usize;
    r.read(q, yp as usize);
    unsafe {
        *a = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_pun_store_dyn_read() {
    let r: &dyn Rd = &Impl1;
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let q = addr_of_mut!(a) as *mut usize;
    r.read(q, yp as usize);
    unsafe {
        *a = 7;
    }
    assert!(*bx == 0);
}
