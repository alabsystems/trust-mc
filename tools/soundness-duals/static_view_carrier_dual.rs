// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a static array read under a byte view through a pointer
//! that travels through a carrier: a reference to the pointer local (`&q`,
//! `&mut q`, `&raw const q`), a helper taking that reference, a closure
//! capture, a struct, tuple or array field or an `Option` payload holding the
//! static's typed pointer, cast to bytes after it is loaded.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-28):
//!   bug_static_pun_through_ref               -> FAILED ('assertion failed: unsafe { *(*rq).add(2) } == 2')
//!   safe_static_pun_through_ref              -> SUCCESSFUL
//!   bug_static_mut_ref_carrier               -> FAILED ('assertion failed: unsafe { *(*rq).add(2) } == 2')
//!   safe_static_mut_ref_carrier              -> SUCCESSFUL
//!   bug_static_raw_addr_carrier              -> FAILED ('assertion failed: unsafe { *(*pq).add(2) } == 2')
//!   safe_static_raw_addr_carrier             -> SUCCESSFUL
//!   bug_static_ref_to_helper                 -> FAILED ('assertion failed: read_third(&q) == 2')
//!   safe_static_ref_to_helper                -> SUCCESSFUL
//!   bug_static_u32_ref_carrier               -> FAILED ('assertion failed: unsafe { *(*rq).add(5) } == 0x0C')
//!   safe_static_u32_ref_carrier              -> SUCCESSFUL
//!   bug_static_ref_carrier_sym_value         -> FAILED ('assertion failed: unsafe { *(*rq).add(2) } == 2')
//!   safe_static_ref_carrier_sym_value        -> SUCCESSFUL
//!   bug_static_closure_ref_capture           -> FAILED ('assertion failed: rd() == 2')
//!   safe_static_closure_ref_capture          -> SUCCESSFUL
//!   bug_via_struct_field_elem_store          -> FAILED ('assertion failed: unsafe { *q.add(2) } == 2')
//!   safe_via_struct_field_elem_store         -> SUCCESSFUL
//!   bug_typed_ptr_in_tuple_elem_store        -> FAILED ('assertion failed: unsafe { *q.add(2) } == 2')
//!   safe_typed_ptr_in_tuple_elem_store       -> SUCCESSFUL
//!   bug_typed_ptr_in_option_elem_store       -> FAILED ('assertion failed: unsafe { *q.add(2) } == 2')
//!   safe_typed_ptr_in_option_elem_store      -> SUCCESSFUL
//!   bug_typed_ptr_in_array_elem_store        -> FAILED ('assertion failed: unsafe { *q.add(2) } == 2')
//!   safe_typed_ptr_in_array_elem_store       -> SUCCESSFUL
//!   bug_static_pun_through_ref_nostore       -> FAILED ('assertion failed: unsafe { *(*rq).add(2) } == 1')
//!   safe_static_pun_through_ref_nostore      -> SUCCESSFUL
//!   bug_via_struct_field_nostore             -> FAILED ('assertion failed: unsafe { *q.add(2) } == 3')
//!   safe_via_struct_field_nostore            -> SUCCESSFUL
//!   bug_carried_element_view                 -> FAILED ('assertion failed: unsafe { *q.add(1) } == 1')
//!   safe_carried_element_view                -> SUCCESSFUL
//!
//! MECHANISM. A static's memory image is seeded under the views its type
//! decomposes into; a byte of a `[u16; 2]` is not one of them, so the read
//! selects a free value. The round-7 untyped-view net 2 recorded
//! `static_memory_read_unseeded_view` (SoundHavoc) for such a read, but it
//! followed the static's pointer only through direct copies and casts: after
//! the element store (which the round-7 branch writes into the image; main
//! dropped it and failed closed) the rows through a reference, `&mut`, a
//! struct field and a tuple field were certified Genuine on the round-7 branch
//! (review of fix/chc-lost-writes round 7, finding 1), and the rows with no
//! store were Genuine on main and on the branch (finding 3).
//!
//! FIX (fix/chc-lost-writes round 8): net 2 runs on a value flow that follows
//! every carrier (stmt/codegen_stmt_store/untyped_view_flow.rs), so the read
//! records the reason however the pointer got there; a call that may read
//! through its arguments and receives such a pointer, or a reference to one,
//! records it too. No counterexample in these harnesses is certified Genuine;
//! the safe rows are known-red false failures.

#![allow(unused, static_mut_refs)]
use std::ptr::addr_of;

static mut SA: [u16; 2] = [1, 0x0102];
static mut SB: [u16; 2] = [1, 0x0102];
static mut SC: [u16; 2] = [1, 0x0102];
static mut SD: [u16; 2] = [1, 0x0102];
static mut SE: [u32; 2] = [1, 0x0A0B_0C0D];
static mut SF: [u16; 2] = [1, 0x0102];
static mut SG: [u16; 2] = [1, 0x0102];
static mut SH: [u16; 2] = [1, 0x0102];
static mut SI: [u16; 2] = [1, 0x0102];
static mut SJ: [u16; 2] = [1, 0x0102];
static mut SK: [u16; 2] = [1, 0x0102];
static SL: [u16; 2] = [1, 0x0102];

#[kani::proof]
fn bug_static_pun_through_ref() {
    unsafe { SA[1] = 0x0304; }
    let q: *const u8 = unsafe { addr_of!(SA) } as *const u8;
    let rq = &q;
    assert!(unsafe { *(*rq).add(2) } == 2);
}

#[kani::proof]
fn safe_static_pun_through_ref() {
    unsafe { SA[1] = 0x0304; }
    let q: *const u8 = unsafe { addr_of!(SA) } as *const u8;
    let rq = &q;
    assert!(unsafe { *(*rq).add(2) } == 4);
}

#[kani::proof]
fn bug_static_mut_ref_carrier() {
    unsafe { SB[1] = 0x0304; }
    let mut q: *const u8 = unsafe { addr_of!(SB) } as *const u8;
    let rq = &mut q;
    assert!(unsafe { *(*rq).add(2) } == 2);
}

#[kani::proof]
fn safe_static_mut_ref_carrier() {
    unsafe { SB[1] = 0x0304; }
    let mut q: *const u8 = unsafe { addr_of!(SB) } as *const u8;
    let rq = &mut q;
    assert!(unsafe { *(*rq).add(2) } == 4);
}

#[kani::proof]
fn bug_static_raw_addr_carrier() {
    unsafe { SC[1] = 0x0304; }
    let q: *const u8 = unsafe { addr_of!(SC) } as *const u8;
    let pq: *const *const u8 = &raw const q;
    assert!(unsafe { *(*pq).add(2) } == 2);
}

#[kani::proof]
fn safe_static_raw_addr_carrier() {
    unsafe { SC[1] = 0x0304; }
    let q: *const u8 = unsafe { addr_of!(SC) } as *const u8;
    let pq: *const *const u8 = &raw const q;
    assert!(unsafe { *(*pq).add(2) } == 4);
}

#[inline(never)]
fn read_third(p: &*const u8) -> u8 {
    unsafe { *(*p).add(2) }
}

#[kani::proof]
fn bug_static_ref_to_helper() {
    unsafe { SD[1] = 0x0304; }
    let q: *const u8 = unsafe { addr_of!(SD) } as *const u8;
    assert!(read_third(&q) == 2);
}

#[kani::proof]
fn safe_static_ref_to_helper() {
    unsafe { SD[1] = 0x0304; }
    let q: *const u8 = unsafe { addr_of!(SD) } as *const u8;
    assert!(read_third(&q) == 4);
}

#[kani::proof]
fn bug_static_u32_ref_carrier() {
    unsafe { SE[1] = 0x0102_0304; }
    let q: *const u8 = unsafe { addr_of!(SE) } as *const u8;
    let rq = &q;
    assert!(unsafe { *(*rq).add(5) } == 0x0C);
}

#[kani::proof]
fn safe_static_u32_ref_carrier() {
    unsafe { SE[1] = 0x0102_0304; }
    let q: *const u8 = unsafe { addr_of!(SE) } as *const u8;
    let rq = &q;
    assert!(unsafe { *(*rq).add(5) } == 3);
}

#[kani::proof]
fn bug_static_ref_carrier_sym_value() {
    let v: u16 = kani::any();
    unsafe { SF[1] = v; }
    let q: *const u8 = unsafe { addr_of!(SF) } as *const u8;
    let rq = &q;
    assert!(unsafe { *(*rq).add(2) } == 2);
}

#[kani::proof]
fn safe_static_ref_carrier_sym_value() {
    let v: u16 = kani::any();
    unsafe { SF[1] = v; }
    let q: *const u8 = unsafe { addr_of!(SF) } as *const u8;
    let rq = &q;
    assert!(unsafe { *(*rq).add(2) } == (v & 0xff) as u8);
}

#[kani::proof]
fn bug_static_closure_ref_capture() {
    unsafe { SG[1] = 0x0304; }
    let q: *const u8 = unsafe { addr_of!(SG) } as *const u8;
    let rd = || unsafe { *q.add(2) };
    assert!(rd() == 2);
}

#[kani::proof]
fn safe_static_closure_ref_capture() {
    unsafe { SG[1] = 0x0304; }
    let q: *const u8 = unsafe { addr_of!(SG) } as *const u8;
    let rd = || unsafe { *q.add(2) };
    assert!(rd() == 4);
}

struct Holder {
    p: *const [u16; 2],
    n: u8,
}

#[kani::proof]
fn bug_via_struct_field_elem_store() {
    unsafe { SH[1] = 0x0304; }
    let h = Holder { p: unsafe { addr_of!(SH) }, n: 1 };
    let q = h.p as *const u8;
    assert!(unsafe { *q.add(2) } == 2);
}

#[kani::proof]
fn safe_via_struct_field_elem_store() {
    unsafe { SH[1] = 0x0304; }
    let h = Holder { p: unsafe { addr_of!(SH) }, n: 1 };
    let q = h.p as *const u8;
    assert!(unsafe { *q.add(2) } == 4);
}

#[kani::proof]
fn bug_typed_ptr_in_tuple_elem_store() {
    unsafe { SI[1] = 0x0304; }
    let t = (unsafe { addr_of!(SI) }, 7u8);
    let q = t.0 as *const u8;
    assert!(unsafe { *q.add(2) } == 2);
}

#[kani::proof]
fn safe_typed_ptr_in_tuple_elem_store() {
    unsafe { SI[1] = 0x0304; }
    let t = (unsafe { addr_of!(SI) }, 7u8);
    let q = t.0 as *const u8;
    assert!(unsafe { *q.add(2) } == 4);
}

#[kani::proof]
fn bug_typed_ptr_in_option_elem_store() {
    unsafe { SJ[1] = 0x0304; }
    let o = Some(unsafe { addr_of!(SJ) });
    if let Some(p) = o {
        let q = p as *const u8;
        assert!(unsafe { *q.add(2) } == 2);
    }
}

#[kani::proof]
fn safe_typed_ptr_in_option_elem_store() {
    unsafe { SJ[1] = 0x0304; }
    let o = Some(unsafe { addr_of!(SJ) });
    if let Some(p) = o {
        let q = p as *const u8;
        assert!(unsafe { *q.add(2) } == 4);
    }
}

#[kani::proof]
fn bug_typed_ptr_in_array_elem_store() {
    unsafe { SK[1] = 0x0304; }
    let arr = [unsafe { addr_of!(SK) }, unsafe { addr_of!(SK) }];
    let q = arr[1] as *const u8;
    assert!(unsafe { *q.add(2) } == 2);
}

#[kani::proof]
fn safe_typed_ptr_in_array_elem_store() {
    unsafe { SK[1] = 0x0304; }
    let arr = [unsafe { addr_of!(SK) }, unsafe { addr_of!(SK) }];
    let q = arr[1] as *const u8;
    assert!(unsafe { *q.add(2) } == 4);
}

// No store (finding 3): the free byte was certified Genuine on main too.
#[kani::proof]
fn bug_static_pun_through_ref_nostore() {
    let q: *const u8 = addr_of!(SL) as *const u8;
    let rq = &q;
    assert!(unsafe { *(*rq).add(2) } == 1);
}

#[kani::proof]
fn safe_static_pun_through_ref_nostore() {
    let q: *const u8 = addr_of!(SL) as *const u8;
    let rq = &q;
    assert!(unsafe { *(*rq).add(2) } == 2);
}

struct HolderI {
    p: *const [u16; 2],
    n: u8,
}

#[kani::proof]
fn bug_via_struct_field_nostore() {
    let h = HolderI { p: addr_of!(SL), n: 1 };
    let q = h.p as *const u8;
    assert!(unsafe { *q.add(2) } == 3);
}

#[kani::proof]
fn safe_via_struct_field_nostore() {
    let h = HolderI { p: addr_of!(SL), n: 1 };
    let q = h.p as *const u8;
    assert!(unsafe { *q.add(2) } == 2);
}

// Controls: the carried typed pointer read under its element view is seeded.
#[kani::proof]
fn bug_carried_element_view() {
    let h = HolderI { p: addr_of!(SL), n: 1 };
    let q = h.p as *const u16;
    assert!(unsafe { *q.add(1) } == 1);
}

#[kani::proof]
fn safe_carried_element_view() {
    let h = HolderI { p: addr_of!(SL), n: 1 };
    let q = h.p as *const u16;
    assert!(unsafe { *q.add(1) } == 0x0102);
}
