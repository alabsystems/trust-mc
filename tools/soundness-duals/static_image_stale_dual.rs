// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- raw reads of a static through views the image seeds, after
//! store shapes the image writer may not follow: a struct static's field and
//! whole stores read through a pointer loaded from the heap or by a helper, a
//! field store into an array-of-struct element, an element store into a 2-D
//! array (review of fix/chc-lost-writes round 3, finding 3: fail-closed or exact
//! on the round-8 bundle; main certified the whole-store safe row Genuine).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_struct_static_field_store_heap_ptr      -> SUCCESSFUL
//!   bug_struct_static_field_store_heap_ptr       -> FAILED ('assertion failed: unsafe { (*p).b } == 2')
//!   safe_struct_static_whole_store_heap_ptr      -> SUCCESSFUL
//!   bug_struct_static_whole_store_heap_ptr       -> FAILED ('assertion failed: unsafe { (*p).b } == 2')
//!   safe_struct_static_field_store_helper        -> SUCCESSFUL
//!   bug_struct_static_field_store_helper         -> FAILED ('assertion failed: read_b(unsafe { addr_of!(GS6) }) == 2')
//!   safe_arr_struct_elem_field_store_raw_read    -> SUCCESSFUL
//!   bug_arr_struct_elem_field_store_raw_read     -> FAILED ('assertion failed: unsafe { (*p.add(1)).b } == 4')
//!   safe_2d_static_elem_store_raw_read           -> SUCCESSFUL
//!   bug_2d_static_elem_store_raw_read            -> FAILED ('assertion failed: unsafe { *p.add(2) } == 3')
//!   safe_2d_static_elem_store_row_ptr            -> SUCCESSFUL
//!   bug_2d_static_elem_store_row_ptr             -> FAILED ('assertion failed: unsafe { (*row.add(1))[0] } == 3')
//!   safe_struct_arr_field_store_raw_read         -> SUCCESSFUL
//!   bug_struct_arr_field_store_raw_read          -> FAILED ('assertion failed: unsafe { *p.add(1) } == 3')
//!
#![allow(static_mut_refs, unused)]
use std::ptr::{addr_of, addr_of_mut};

#[derive(Clone, Copy)]
#[repr(C)]
struct P {
    a: u32,
    b: u32,
}

// ---- struct static, field store, read through a pointer loaded from the heap ----
static mut GS1: P = P { a: 1, b: 2 };
static mut GS2: P = P { a: 1, b: 2 };

#[kani::proof]
fn safe_struct_static_field_store_heap_ptr() {
    unsafe {
        GS1.b = 5;
    }
    let bx: Box<*const P> = Box::new(unsafe { addr_of!(GS1) });
    let p: *const P = *bx;
    assert!(unsafe { (*p).b } == 5);
}

#[kani::proof]
fn bug_struct_static_field_store_heap_ptr() {
    unsafe {
        GS2.b = 5;
    }
    let bx: Box<*const P> = Box::new(unsafe { addr_of!(GS2) });
    let p: *const P = *bx;
    assert!(unsafe { (*p).b } == 2);
}

// ---- struct static, whole store, read through a pointer loaded from the heap ----
static mut GS3: P = P { a: 1, b: 2 };
static mut GS4: P = P { a: 1, b: 2 };

#[kani::proof]
fn safe_struct_static_whole_store_heap_ptr() {
    unsafe {
        GS3 = P { a: 3, b: 4 };
    }
    let bx: Box<*const P> = Box::new(unsafe { addr_of!(GS3) });
    let p: *const P = *bx;
    assert!(unsafe { (*p).b } == 4);
}

#[kani::proof]
fn bug_struct_static_whole_store_heap_ptr() {
    unsafe {
        GS4 = P { a: 3, b: 4 };
    }
    let bx: Box<*const P> = Box::new(unsafe { addr_of!(GS4) });
    let p: *const P = *bx;
    assert!(unsafe { (*p).b } == 2);
}

// ---- struct static, field store, read by a helper the MIR inliner keeps out ----
static mut GS5: P = P { a: 1, b: 2 };
static mut GS6: P = P { a: 1, b: 2 };

#[inline(never)]
fn read_b(p: *const P) -> u32 {
    unsafe { (*p).b }
}

#[kani::proof]
fn safe_struct_static_field_store_helper() {
    unsafe {
        GS5.b = 5;
    }
    assert!(read_b(unsafe { addr_of!(GS5) }) == 5);
}

#[kani::proof]
fn bug_struct_static_field_store_helper() {
    unsafe {
        GS6.b = 5;
    }
    assert!(read_b(unsafe { addr_of!(GS6) }) == 2);
}

// ---- array-of-struct static, field store into an element, raw element read ----
static mut GA1: [P; 2] = [P { a: 1, b: 2 }, P { a: 3, b: 4 }];
static mut GA2: [P; 2] = [P { a: 1, b: 2 }, P { a: 3, b: 4 }];

#[kani::proof]
fn safe_arr_struct_elem_field_store_raw_read() {
    unsafe {
        GA1[1].b = 9;
    }
    let p: *const P = unsafe { addr_of!(GA1) } as *const P;
    assert!(unsafe { (*p.add(1)).b } == 9);
}

#[kani::proof]
fn bug_arr_struct_elem_field_store_raw_read() {
    unsafe {
        GA2[1].b = 9;
    }
    let p: *const P = unsafe { addr_of!(GA2) } as *const P;
    assert!(unsafe { (*p.add(1)).b } == 4);
}

// ---- 2-D array static, element store, raw read through the element view ----
static mut G2A: [[u16; 2]; 2] = [[1, 2], [3, 4]];
static mut G2B: [[u16; 2]; 2] = [[1, 2], [3, 4]];

#[kani::proof]
fn safe_2d_static_elem_store_raw_read() {
    unsafe {
        G2A[1][0] = 7;
    }
    let p: *const u16 = unsafe { addr_of!(G2A) } as *const u16;
    assert!(unsafe { *p.add(2) } == 7);
}

#[kani::proof]
fn bug_2d_static_elem_store_raw_read() {
    unsafe {
        G2B[1][0] = 7;
    }
    let p: *const u16 = unsafe { addr_of!(G2B) } as *const u16;
    assert!(unsafe { *p.add(2) } == 3);
}

// ---- 2-D array static, element store, read through a row pointer ----
static mut G2C: [[u16; 2]; 2] = [[1, 2], [3, 4]];
static mut G2D: [[u16; 2]; 2] = [[1, 2], [3, 4]];

#[kani::proof]
fn safe_2d_static_elem_store_row_ptr() {
    unsafe {
        G2C[1][0] = 7;
    }
    let row: *const [u16; 2] = unsafe { addr_of!(G2C) } as *const [u16; 2];
    assert!(unsafe { (*row.add(1))[0] } == 7);
}

#[kani::proof]
fn bug_2d_static_elem_store_row_ptr() {
    unsafe {
        G2D[1][0] = 7;
    }
    let row: *const [u16; 2] = unsafe { addr_of!(G2D) } as *const [u16; 2];
    assert!(unsafe { (*row.add(1))[0] } == 3);
}

// ---- struct static with an array field, element store, raw read ----
#[derive(Clone, Copy)]
#[repr(C)]
struct Q {
    n: u32,
    arr: [u16; 2],
}
static mut GQ1: Q = Q { n: 1, arr: [2, 3] };
static mut GQ2: Q = Q { n: 1, arr: [2, 3] };

#[kani::proof]
fn safe_struct_arr_field_store_raw_read() {
    unsafe {
        GQ1.arr[1] = 8;
    }
    let p: *const u16 = unsafe { addr_of!(GQ1.arr) } as *const u16;
    assert!(unsafe { *p.add(1) } == 8);
}

#[kani::proof]
fn bug_struct_arr_field_store_raw_read() {
    unsafe {
        GQ2.arr[1] = 8;
    }
    let p: *const u16 = unsafe { addr_of!(GQ2.arr) } as *const u16;
    assert!(unsafe { *p.add(1) } == 3);
}
