// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- value-preserving launders of an address: `u32` halves
//! re-joined by a transmute and the `f64` bits of an address, for both
//! untyped-view nets. Kani drops provenance through a float's bits, so its
//! verdicts on the `f64` rows are the oracle, not the row's name (review of
//! fix/chc-lost-writes round 3, finding 3).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   bug_pun_u32_array_rejoin                     -> FAILED ('assertion failed: *y != 7')
//!   safe_pun_u32_array_rejoin                    -> SUCCESSFUL
//!   bug_pun_f64_bits_transmute                   -> FAILED ('assertion failed: *bx == 0')
//!   safe_pun_f64_bits_transmute_read_back        -> SUCCESSFUL
//!   safe_static_u32_array_rejoin_elem_store      -> SUCCESSFUL
//!   bug_static_u32_array_rejoin_elem_store       -> FAILED ('assertion failed: unsafe { *p.add(2) } == 2')
//!   bug_static_f64_transmute_nostore             -> FAILED ('assertion failed: unsafe { *p.add(2) } == 2')
//!
#![allow(static_mut_refs, unused)]
use std::mem::transmute;
use std::ptr::{addr_of, addr_of_mut};

// ---- net 1 ----

#[kani::proof]
fn bug_pun_u32_array_rejoin() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let halves: [u32; 2] = unsafe { transmute(addr_of_mut!(a) as usize) };
    let back: usize = unsafe { transmute([halves[0], halves[1]]) };
    let q = back as *mut usize;
    unsafe {
        *q = yp as usize;
    }
    unsafe {
        *a = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_pun_u32_array_rejoin() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let halves: [u32; 2] = unsafe { transmute(addr_of_mut!(a) as usize) };
    let back: usize = unsafe { transmute([halves[0], halves[1]]) };
    let q = back as *mut usize;
    unsafe {
        *q = yp as usize;
    }
    unsafe {
        *a = 7;
    }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_pun_f64_bits_transmute() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let f: f64 = unsafe { transmute(addr_of_mut!(a) as usize) };
    let q: *mut usize = unsafe { transmute(f) };
    unsafe {
        *q = yp as usize;
    }
    unsafe {
        *a = 7;
    }
    assert!(*bx == 0);
}

#[kani::proof]
fn safe_pun_f64_bits_transmute_read_back() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let f: f64 = unsafe { transmute(addr_of_mut!(a) as usize) };
    let q: *mut usize = unsafe { transmute(f) };
    unsafe {
        *q = yp as usize;
    }
    unsafe {
        *a = 7;
    }
    assert!(*bx == 7);
}

// ---- net 2 ----
static mut SA: [u16; 2] = [1, 0x0102];
static mut SB: [u16; 2] = [1, 0x0102];
static SC: [u16; 2] = [1, 0x0102];

#[kani::proof]
fn safe_static_u32_array_rejoin_elem_store() {
    unsafe {
        SA[1] = 0x0304;
    }
    let halves: [u32; 2] = unsafe { transmute(addr_of!(SA) as usize) };
    let back: usize = unsafe { transmute([halves[0], halves[1]]) };
    let p = back as *const u8;
    assert!(unsafe { *p.add(2) } == 4);
}

#[kani::proof]
fn bug_static_u32_array_rejoin_elem_store() {
    unsafe {
        SB[1] = 0x0304;
    }
    let halves: [u32; 2] = unsafe { transmute(addr_of!(SB) as usize) };
    let back: usize = unsafe { transmute([halves[0], halves[1]]) };
    let p = back as *const u8;
    assert!(unsafe { *p.add(2) } == 2);
}

#[kani::proof]
fn bug_static_f64_transmute_nostore() {
    let f: f64 = unsafe { transmute(addr_of!(SC) as *const u8) };
    let p: *const u8 = unsafe { transmute(f) };
    assert!(unsafe { *p.add(2) } == 2);
}
