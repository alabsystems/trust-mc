// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a raw read of a static's memory under a view the entry
//! rule never seeds (`*(addr_of!(G) as *const u8).add(2)` for `G: [u16; 2]`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_u16_bytes_nostore           -> FAILED ('assertion failed: *p.add(2) != 2')
//!   safe_u16_bytes_nostore          -> SUCCESSFUL
//!   bug_u16_whole_store_bytes       -> FAILED ('assertion failed: *p.add(2) != 2')
//!   safe_u16_whole_store_bytes      -> SUCCESSFUL
//!   bug_u16_elem_store_bytes        -> FAILED ('assertion failed: *p.add(2) != 2')
//!   safe_u16_elem_store_bytes       -> SUCCESSFUL
//!   bug_u32_elem_store_bytes        -> FAILED ('assertion failed: *p.add(4) != 0x0D')
//!   safe_u32_elem_store_bytes       -> SUCCESSFUL
//!   safe_u16_elem_bytes_sym_value   -> SUCCESSFUL
//!   safe_u16_elem_bytes_sym_index   -> SUCCESSFUL
//!   safe_helper_raw_byte_ptr        -> SUCCESSFUL
//!   safe_immutable_static_bytes     -> SUCCESSFUL
//!   safe_u32_cast_method_bytes      -> SUCCESSFUL
//!   bug_u16_elem_own_view           -> FAILED ('assertion failed: *p.add(1) != 0x0102'; control)
//!   safe_u16_elem_own_view          -> SUCCESSFUL (control)
//!   bug_u8_array_own_view           -> FAILED ('assertion failed: *p.add(3) != 9'; control)
//!   safe_u8_array_own_view          -> SUCCESSFUL (control)
//!
//! MECHANISM. A static's memory image is seeded by the entry rule
//! (`register_static_memory_init_entries`) and written by the static store
//! lanes (`static_image.rs`) under the views its type decomposes into: the
//! static's own type, each array element, each struct field. A read through a
//! pointer cast to another view selects a typed-memory cell nothing
//! constrains, a free value. The safe rows with no store or a whole-array
//! store were certified Genuine on main (pre-existing, review of
//! fix/chc-lost-writes round 6, finding 4); after an element store main failed
//! closed, and the branch's element lane, which writes the image, turned that
//! into a Genuine certificate (finding 2).
//!
//! FIX (fix/chc-lost-writes round 7): such a read records the SoundHavoc
//! reason `static_memory_read_unseeded_view`
//! (stmt/codegen_stmt_store/untyped_view_scan.rs). The encoding is unchanged,
//! so a proof over the free value stands, but no counterexample in the
//! harness is certified Genuine. The safe rows that depend on the free byte
//! are known-red false failures (FAILED OverApproximation); the element-view
//! and byte-array controls are seeded views and stay exact.

#![allow(unused, static_mut_refs)]
use std::ptr::{addr_of, addr_of_mut};

static mut GA: [u16; 2] = [1, 0x0102];
static mut GB: [u16; 2] = [1, 2];
static mut GC: [u16; 2] = [1, 2];
static mut GD: [u32; 2] = [1, 2];
static mut GE: [u16; 2] = [1, 2];
static mut GF: [u16; 2] = [1, 2];
static mut GG: [u16; 2] = [1, 0x0102];
static GH: [u16; 2] = [1, 0x0102];
static mut GI: u32 = 0x0A0B0C0D;
static mut GJ: [u16; 2] = [1, 2];
static mut GK: [u8; 4] = [1, 2, 3, 4];

fn rd_byte2(p: *const u8) -> u8 {
    unsafe { *p.add(2) }
}

#[kani::proof]
fn bug_u16_bytes_nostore() {
    unsafe {
        let p = addr_of!(GA) as *const u8;
        assert!(*p.add(2) != 2);
    }
}

#[kani::proof]
fn safe_u16_bytes_nostore() {
    unsafe {
        let p = addr_of!(GA) as *const u8;
        assert!(*p.add(2) == 2);
    }
}

#[kani::proof]
fn bug_u16_whole_store_bytes() {
    unsafe {
        GB = [1, 0x0102];
        let p = addr_of!(GB) as *const u8;
        assert!(*p.add(2) != 2);
    }
}

#[kani::proof]
fn safe_u16_whole_store_bytes() {
    unsafe {
        GB = [1, 0x0102];
        let p = addr_of!(GB) as *const u8;
        assert!(*p.add(2) == 2);
    }
}

#[kani::proof]
fn bug_u16_elem_store_bytes() {
    unsafe {
        GC[1] = 0x0102;
        let p = addr_of!(GC) as *const u8;
        assert!(*p.add(2) != 2);
    }
}

#[kani::proof]
fn safe_u16_elem_store_bytes() {
    unsafe {
        GC[1] = 0x0102;
        let p = addr_of!(GC) as *const u8;
        assert!(*p.add(2) == 2);
    }
}

#[kani::proof]
fn bug_u32_elem_store_bytes() {
    unsafe {
        GD[1] = 0x0A0B0C0D;
        let p = addr_of!(GD) as *const u8;
        assert!(*p.add(4) != 0x0D);
    }
}

#[kani::proof]
fn safe_u32_elem_store_bytes() {
    unsafe {
        GD[1] = 0x0A0B0C0D;
        let p = addr_of!(GD) as *const u8;
        assert!(*p.add(4) == 0x0D);
    }
}

#[kani::proof]
fn safe_u16_elem_bytes_sym_value() {
    let v: u16 = kani::any();
    unsafe {
        GE[1] = v;
        let p = addr_of!(GE) as *const u8;
        assert!(*p.add(2) == (v & 0xff) as u8);
    }
}

#[kani::proof]
fn safe_u16_elem_bytes_sym_index() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    unsafe {
        GF[i] = 0x0102;
        let p = addr_of!(GF) as *const u8;
        assert!(*p.add(2 * i) == 2);
    }
}

#[kani::proof]
fn safe_helper_raw_byte_ptr() {
    unsafe { assert!(rd_byte2(addr_of!(GG) as *const u8) == 2); }
}

#[kani::proof]
fn safe_immutable_static_bytes() {
    let p = addr_of!(GH) as *const u8;
    assert!(unsafe { *p.add(2) } == 2);
}

#[kani::proof]
fn safe_u32_cast_method_bytes() {
    unsafe {
        let p = addr_of!(GI).cast::<u8>();
        assert!(*p.add(1) == 0x0C);
    }
}

#[kani::proof]
fn bug_u16_elem_own_view() {
    unsafe {
        GJ[1] = 0x0102;
        let p = addr_of!(GJ) as *const u16;
        assert!(*p.add(1) != 0x0102);
    }
}

#[kani::proof]
fn safe_u16_elem_own_view() {
    unsafe {
        GJ[1] = 0x0102;
        let p = addr_of!(GJ) as *const u16;
        assert!(*p.add(1) == 0x0102);
    }
}

#[kani::proof]
fn bug_u8_array_own_view() {
    unsafe {
        GK[3] = 9;
        let p = addr_of!(GK) as *const u8;
        assert!(*p.add(3) != 9);
    }
}

#[kani::proof]
fn safe_u8_array_own_view() {
    unsafe {
        GK[3] = 9;
        let p = addr_of!(GK) as *const u8;
        assert!(*p.add(3) == 9);
    }
}
