// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a struct element store into a static array, with a struct
//! rustc reorders (`y@0, x@4`), read back every way: the static itself, the
//! element through a raw pointer, one field through a raw pointer, a field
//! through a helper, a symbolic index (review of fix/chc-lost-writes round 3,
//! finding 3: exact on the round-8 bundle, OverApproximation on main).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_reordered_elem_store_direct_read        -> SUCCESSFUL
//!   bug_reordered_elem_store_direct_read         -> FAILED ('assertion failed: unsafe { GB[1].x == 2 }')
//!   safe_reordered_elem_store_raw_elem_read      -> SUCCESSFUL
//!   bug_reordered_elem_store_raw_elem_read       -> FAILED ('assertion failed: e.x == 2')
//!   safe_reordered_elem_store_raw_field_read     -> SUCCESSFUL
//!   bug_reordered_elem_store_raw_field_read      -> FAILED ('assertion failed: unsafe { (*p.add(1)).y } == 20')
//!   safe_reordered_elem_store_sym_index          -> SUCCESSFUL
//!   safe_reordered_elem_store_ref_helper         -> SUCCESSFUL
//!   bug_reordered_elem_store_ref_helper          -> FAILED ('assertion failed: read_x(unsafe { &GI[1] }) == 2')
//!
#![allow(static_mut_refs, unused)]
use std::ptr::addr_of;

#[derive(Clone, Copy)]
struct P2 {
    x: u8,
    y: u32,
}

static mut GA: [P2; 2] = [P2 { x: 1, y: 10 }, P2 { x: 2, y: 20 }];
static mut GB: [P2; 2] = [P2 { x: 1, y: 10 }, P2 { x: 2, y: 20 }];
static mut GC: [P2; 2] = [P2 { x: 1, y: 10 }, P2 { x: 2, y: 20 }];
static mut GD: [P2; 2] = [P2 { x: 1, y: 10 }, P2 { x: 2, y: 20 }];
static mut GE: [P2; 2] = [P2 { x: 1, y: 10 }, P2 { x: 2, y: 20 }];
static mut GF: [P2; 2] = [P2 { x: 1, y: 10 }, P2 { x: 2, y: 20 }];
static mut GG: [P2; 2] = [P2 { x: 1, y: 10 }, P2 { x: 2, y: 20 }];

#[kani::proof]
fn safe_reordered_elem_store_direct_read() {
    unsafe {
        GA[1] = P2 { x: 7, y: 70 };
    }
    assert!(unsafe { GA[1].x == 7 && GA[1].y == 70 && GA[0].x == 1 });
}

#[kani::proof]
fn bug_reordered_elem_store_direct_read() {
    unsafe {
        GB[1] = P2 { x: 7, y: 70 };
    }
    assert!(unsafe { GB[1].x == 2 });
}

#[kani::proof]
fn safe_reordered_elem_store_raw_elem_read() {
    unsafe {
        GC[1] = P2 { x: 7, y: 70 };
    }
    let p = unsafe { addr_of!(GC) } as *const P2;
    let e = unsafe { *p.add(1) };
    assert!(e.x == 7 && e.y == 70);
}

#[kani::proof]
fn bug_reordered_elem_store_raw_elem_read() {
    unsafe {
        GD[1] = P2 { x: 7, y: 70 };
    }
    let p = unsafe { addr_of!(GD) } as *const P2;
    let e = unsafe { *p.add(1) };
    assert!(e.x == 2);
}

#[kani::proof]
fn safe_reordered_elem_store_raw_field_read() {
    unsafe {
        GE[1] = P2 { x: 7, y: 70 };
    }
    let p = unsafe { addr_of!(GE) } as *const P2;
    assert!(unsafe { (*p.add(1)).x } == 7 && unsafe { (*p.add(1)).y } == 70);
}

#[kani::proof]
fn bug_reordered_elem_store_raw_field_read() {
    unsafe {
        GF[1] = P2 { x: 7, y: 70 };
    }
    let p = unsafe { addr_of!(GF) } as *const P2;
    assert!(unsafe { (*p.add(1)).y } == 20);
}

#[kani::proof]
fn safe_reordered_elem_store_sym_index() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    unsafe {
        GG[i] = P2 { x: 7, y: 70 };
    }
    let p = unsafe { addr_of!(GG) } as *const P2;
    assert!(unsafe { (*p.add(i)).x } == 7);
}

// the element's field read through a reference to the element
static mut GH: [P2; 2] = [P2 { x: 1, y: 10 }, P2 { x: 2, y: 20 }];
static mut GI: [P2; 2] = [P2 { x: 1, y: 10 }, P2 { x: 2, y: 20 }];

fn read_x(e: &P2) -> u8 {
    e.x
}

#[kani::proof]
fn safe_reordered_elem_store_ref_helper() {
    unsafe {
        GH[1] = P2 { x: 7, y: 70 };
    }
    assert!(read_x(unsafe { &GH[1] }) == 7);
}

#[kani::proof]
fn bug_reordered_elem_store_ref_helper() {
    unsafe {
        GI[1] = P2 { x: 7, y: 70 };
    }
    assert!(read_x(unsafe { &GI[1] }) == 2);
}
