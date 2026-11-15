// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a pointer rebuilt from an integer: an exposed address
//! (`with_exposed_provenance(p.expose_provenance() + k)`, `(p as usize + k) as
//! *const T`), an address joined back from two `u32` halves, an integer
//! transmuted into a pointer, a union's integer field read as its pointer
//! field, or a nondeterministic integer.
//!
//! The CHC integer-to-pointer lane invalidates `obj_valid` of the object the
//! result names (#3350): the model keeps no set of exposed allocations, and
//! `obj_valid` starts all-true. For a live object that is fail-closed, not
//! exact (Kani keeps the pointer's bits and proves the round trips), and main
//! recorded no reason for it, so the memory-safety failure of a program Kani
//! proves was certified Genuine whenever nothing else tainted the harness
//! (review of fix/chc-lost-writes round 3, finding 1: the branch's exact
//! element stores removed the one reason main had). The lane now records
//! `int_to_ptr_obj_invalidated` (SoundHavoc, unaccounted): proofs stand, no
//! counterexample resting on it is certified. A transmute of an integer into a
//! pointer takes the same lane (it read past its object unchecked on main).
//! The null object (a constant address below 2^32) records nothing: nothing
//! lives there, so its invalidation is exact.
//!
//! A LITERAL address whose high word names a model object (the model numbers
//! objects from 1) reads that object, and the invalidation does not reach a
//! stack local (always valid): main verified such reads Kani reports as
//! invalid. The untyped-view net 3 follows the literal (through a local, into
//! a helper, out of one) and fails closed (`const_pointer_names_model_object`)
//! where a pointer made from it may be read; a literal pointer compared and
//! never read, or the literal used as a number, keeps its proof, and such a
//! literal invalidates no object (it names none in Kani), so an unrelated
//! failure beside it stays certifiable.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_box_elem_store_exposed                  -> SUCCESSFUL
//!   bug_box_elem_store_exposed                   -> FAILED ('assertion failed: unsafe { *q } == 0x0102')
//!   safe_box_elem_store_exposed_elem0            -> SUCCESSFUL
//!   bug_box_elem_store_exposed_elem0             -> FAILED ('assertion failed: unsafe { *q } == 1')
//!   safe_box_elem_store_as_cast_arith            -> SUCCESSFUL
//!   bug_box_elem_store_as_cast_arith             -> FAILED ('assertion failed: unsafe { *q } == 0x0102')
//!   safe_box_elem_store_direct_roundtrip         -> SUCCESSFUL
//!   bug_box_elem_store_direct_roundtrip          -> FAILED ('assertion failed: unsafe { *p.add(1) } == 0x0102')
//!   safe_box_nostore_exposed                     -> SUCCESSFUL
//!   bug_box_nostore_exposed                      -> FAILED ('assertion failed: unsafe { *q } == 1')
//!   safe_box_scalar_exposed                      -> SUCCESSFUL
//!   bug_box_scalar_exposed                       -> FAILED ('assertion failed: unsafe { *q } == 8')
//!   safe_vec_elem_store_exposed                  -> SUCCESSFUL
//!   bug_vec_elem_store_exposed                   -> FAILED ('assertion failed: unsafe { *q } == 0x0102')
//!   safe_stack_elem_store_exposed                -> SUCCESSFUL
//!   bug_stack_elem_store_exposed                 -> FAILED ('assertion failed: unsafe { *q } == 0x0102')
//!   safe_box_nostore_as_cast_arith               -> SUCCESSFUL
//!   bug_box_nostore_as_cast_arith                -> FAILED ('assertion failed: unsafe { *q } == 1')
//!   safe_original_pointer_after_roundtrip        -> SUCCESSFUL
//!   bug_original_pointer_after_roundtrip         -> FAILED ('assertion failed: unsafe { *p } == 2')
//!   bug_int_roundtrip_oob                        -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_cast_roundtrip_after_free                -> FAILED ('dereference failure: deallocated dynamic object')
//!   bug_cast_nondet_with_box                     -> FAILED ('null pointer dereference occurred')
//!   safe_transmute_roundtrip_box                 -> SUCCESSFUL
//!   bug_transmute_roundtrip_box_value            -> FAILED ('assertion failed: unsafe { *q } == 1')
//!   bug_transmute_roundtrip_box_oob              -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_transmute_roundtrip_after_free           -> FAILED ('dereference failure: deallocated dynamic object')
//!   safe_static_elem_store_halves_elem_view      -> SUCCESSFUL
//!   bug_static_elem_store_halves_elem_view       -> FAILED ('assertion failed: unsafe { *p.add(1) } == 0x0102')
//!   safe_static_nostore_halves_elem_view         -> SUCCESSFUL
//!   bug_static_nostore_halves_elem_view          -> FAILED ('assertion failed: unsafe { *p.add(1) } == 1')
//!   safe_static_u32_halves_elem_store            -> SUCCESSFUL
//!   bug_static_u32_halves_elem_store             -> FAILED ('assertion failed: unsafe { *p.add(2) } == 2')
//!   safe_static_u32_halves_nostore               -> SUCCESSFUL
//!   bug_static_u32_halves_nostore                -> FAILED ('assertion failed: unsafe { *p.add(2) } == 1')
//!   safe_static_halves_transmute_bytes           -> SUCCESSFUL
//!   bug_static_halves_transmute_bytes            -> FAILED ('assertion failed: unsafe { *p.add(2) } == 2')
//!   safe_static_halves_union_bytes               -> SUCCESSFUL
//!   bug_static_halves_union_bytes                -> FAILED ('assertion failed: unsafe { *p.add(2) } == 2')
//!   bug_crafted_const_names_heap_id              -> FAILED ('dereference failure: invalid integer address')
//!   bug_crafted_const_transmute_names_heap_id    -> FAILED ('dereference failure: pointer NULL')
//!   safe_wrapping_byte_add_in_bounds             -> SUCCESSFUL
//!   bug_wrapping_byte_add_oob                    -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_wrapping_add_in_bounds                  -> SUCCESSFUL
//!   bug_wrapping_add_oob                         -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_wrapping_offset_in_bounds               -> SUCCESSFUL
//!   bug_wrapping_offset_oob                      -> FAILED ('dereference failure: pointer outside object bounds')
//!   safe_vec_wrapping_add_in_bounds              -> SUCCESSFUL
//!   bug_vec_wrapping_add_oob                     -> FAILED ('dereference failure: pointer outside object bounds')
//!   bug_const_small_address_read                 -> FAILED ('dereference failure: invalid integer address')
//!   bug_crafted_const_through_local              -> FAILED ('dereference failure: pointer NULL')
//!   bug_crafted_const_helper_reader              -> FAILED ('dereference failure: pointer NULL')
//!   bug_crafted_const_helper_returns             -> FAILED ('dereference failure: pointer NULL')
//!   bug_crafted_const_without_provenance         -> FAILED ('dereference failure: pointer NULL')
//!   bug_crafted_const_names_stack_slot           -> FAILED ('dereference failure: invalid integer address')
//!   bug_crafted_const_write                      -> FAILED ('dereference failure: invalid integer address')
//!   safe_crafted_const_compared_only             -> SUCCESSFUL
//!   safe_const_literal_as_a_number               -> SUCCESSFUL
//!   bug_crafted_const_stored_in_static           -> FAILED ('dereference failure: pointer NULL')
//!   bug_crafted_const_beside_box_assertion       -> FAILED ('assertion failed: bx[2] == 8')
//!   safe_crafted_const_beside_box_assertion      -> SUCCESSFUL
//!   bug_crafted_const_into_harness_type          -> FAILED ('dereference failure: pointer NULL')
//!   safe_const_count_offsets_a_pointer           -> SUCCESSFUL
//!   bug_crafted_const_reference_printed          -> FAILED ('dereference failure: pointer invalid')
//!
#![allow(unused, static_mut_refs)]
use std::ptr::addr_of;

// ---- a Box element store, then a read through the exposed address ----

#[kani::proof]
fn safe_box_elem_store_exposed() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    bx[1] = 0x0304;
    let p = addr_of!(*bx) as *const u16;
    let q = std::ptr::with_exposed_provenance::<u16>(p.expose_provenance() + 2);
    assert!(unsafe { *q } == 0x0304);
}

#[kani::proof]
fn bug_box_elem_store_exposed() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    bx[1] = 0x0304;
    let p = addr_of!(*bx) as *const u16;
    let q = std::ptr::with_exposed_provenance::<u16>(p.expose_provenance() + 2);
    assert!(unsafe { *q } == 0x0102);
}

#[kani::proof]
fn safe_box_elem_store_exposed_elem0() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    bx[0] = 5;
    let p = addr_of!(*bx) as *const u16;
    let q = std::ptr::with_exposed_provenance::<u16>(p.expose_provenance());
    assert!(unsafe { *q } == 5);
}

#[kani::proof]
fn bug_box_elem_store_exposed_elem0() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    bx[0] = 5;
    let p = addr_of!(*bx) as *const u16;
    let q = std::ptr::with_exposed_provenance::<u16>(p.expose_provenance());
    assert!(unsafe { *q } == 1);
}

#[kani::proof]
fn safe_box_elem_store_as_cast_arith() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    bx[1] = 0x0304;
    let q = (addr_of!(*bx) as *const u16 as usize + 2) as *const u16;
    assert!(unsafe { *q } == 0x0304);
}

#[kani::proof]
fn bug_box_elem_store_as_cast_arith() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    bx[1] = 0x0304;
    let q = (addr_of!(*bx) as *const u16 as usize + 2) as *const u16;
    assert!(unsafe { *q } == 0x0102);
}

#[kani::proof]
fn safe_box_elem_store_direct_roundtrip() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    bx[1] = 0x0304;
    let p = (addr_of!(*bx) as usize) as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0304);
}

#[kani::proof]
fn bug_box_elem_store_direct_roundtrip() {
    let mut bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    bx[1] = 0x0304;
    let p = (addr_of!(*bx) as usize) as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0102);
}

// ---- the same reads with no element store (Genuine on main and round 8) ----

#[kani::proof]
fn safe_box_nostore_exposed() {
    let bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    let p = addr_of!(*bx) as *const u16;
    let q = std::ptr::with_exposed_provenance::<u16>(p.expose_provenance() + 2);
    assert!(unsafe { *q } == 0x0102);
}

#[kani::proof]
fn bug_box_nostore_exposed() {
    let bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    let p = addr_of!(*bx) as *const u16;
    let q = std::ptr::with_exposed_provenance::<u16>(p.expose_provenance() + 2);
    assert!(unsafe { *q } == 1);
}

#[kani::proof]
fn safe_box_scalar_exposed() {
    let bx: Box<u32> = Box::new(7);
    let p: *const u32 = &*bx;
    let q = std::ptr::with_exposed_provenance::<u32>(p.expose_provenance());
    assert!(unsafe { *q } == 7);
}

#[kani::proof]
fn bug_box_scalar_exposed() {
    let bx: Box<u32> = Box::new(7);
    let p: *const u32 = &*bx;
    let q = std::ptr::with_exposed_provenance::<u32>(p.expose_provenance());
    assert!(unsafe { *q } == 8);
}

#[kani::proof]
fn safe_vec_elem_store_exposed() {
    let mut v: Vec<u16> = vec![1, 0x0102];
    v[1] = 0x0304;
    let p = v.as_ptr();
    let q = std::ptr::with_exposed_provenance::<u16>(p.expose_provenance() + 2);
    assert!(unsafe { *q } == 0x0304);
}

#[kani::proof]
fn bug_vec_elem_store_exposed() {
    let mut v: Vec<u16> = vec![1, 0x0102];
    v[1] = 0x0304;
    let p = v.as_ptr();
    let q = std::ptr::with_exposed_provenance::<u16>(p.expose_provenance() + 2);
    assert!(unsafe { *q } == 0x0102);
}

#[kani::proof]
fn safe_stack_elem_store_exposed() {
    let mut arr: [u16; 2] = [1, 0x0102];
    arr[1] = 0x0304;
    let p = addr_of!(arr) as *const u16;
    let q = std::ptr::with_exposed_provenance::<u16>(p.expose_provenance() + 2);
    assert!(unsafe { *q } == 0x0304);
}

#[kani::proof]
fn bug_stack_elem_store_exposed() {
    let mut arr: [u16; 2] = [1, 0x0102];
    arr[1] = 0x0304;
    let p = addr_of!(arr) as *const u16;
    let q = std::ptr::with_exposed_provenance::<u16>(p.expose_provenance() + 2);
    assert!(unsafe { *q } == 0x0102);
}

#[kani::proof]
fn safe_box_nostore_as_cast_arith() {
    let bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    let q = (addr_of!(*bx) as *const u16 as usize + 2) as *const u16;
    assert!(unsafe { *q } == 0x0102);
}

#[kani::proof]
fn bug_box_nostore_as_cast_arith() {
    let bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    let q = (addr_of!(*bx) as *const u16 as usize + 2) as *const u16;
    assert!(unsafe { *q } == 1);
}

// The rebuilt pointer is never read; the original is.
#[kani::proof]
fn safe_original_pointer_after_roundtrip() {
    let bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    let p = addr_of!(*bx) as *const u16;
    let _q = (p as usize + 2) as *const u16;
    assert!(unsafe { *p } == 1);
}

#[kani::proof]
fn bug_original_pointer_after_roundtrip() {
    let bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
    let p = addr_of!(*bx) as *const u16;
    let _q = (p as usize + 2) as *const u16;
    assert!(unsafe { *p } == 2);
}

// ---- out of bounds, after free, nondeterministic: must fail ----

#[kani::proof]
fn bug_int_roundtrip_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let q = (addr_of!(*bx) as *const u16 as usize + 4) as *const u16;
    let v = unsafe { *q };
}

#[kani::proof]
fn bug_cast_roundtrip_after_free() {
    let bx: Box<u32> = Box::new(5);
    let a = &*bx as *const u32 as usize;
    drop(bx);
    let q = a as *const u32;
    let v = unsafe { *q };
}

#[kani::proof]
fn bug_cast_nondet_with_box() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let a: usize = kani::any();
    let q = a as *const u8;
    let v = unsafe { *q };
}

// ---- integer transmuted into a pointer ----

#[kani::proof]
fn safe_transmute_roundtrip_box() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let q: *const u16 = unsafe { std::mem::transmute(a + 2) };
    assert!(unsafe { *q } == 2);
}

#[kani::proof]
fn bug_transmute_roundtrip_box_value() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let q: *const u16 = unsafe { std::mem::transmute(a + 2) };
    assert!(unsafe { *q } == 1);
}

#[kani::proof]
fn bug_transmute_roundtrip_box_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let a = addr_of!(*bx) as *const u16 as usize;
    let q: *const u16 = unsafe { std::mem::transmute(a + 4) };
    let v = unsafe { *q };
}

#[kani::proof]
fn bug_transmute_roundtrip_after_free() {
    let bx: Box<u32> = Box::new(5);
    let a = &*bx as *const u32 as usize;
    drop(bx);
    let q: *const u32 = unsafe { std::mem::transmute(a) };
    let v = unsafe { *q };
}

// ---- a static array read through an address joined from u32 halves ----

static mut SB: [u16; 2] = [1, 0x0102];
static mut SB2: [u16; 2] = [1, 0x0102];
static SC: [u16; 2] = [1, 0x0102];
static SC2: [u16; 2] = [1, 0x0102];
static mut SA: [u16; 2] = [1, 0x0102];
static mut SA2: [u16; 2] = [1, 0x0102];
static SE: [u16; 2] = [1, 0x0102];
static SE2: [u16; 2] = [1, 0x0102];
static mut SF: [u16; 2] = [1, 0x0102];
static mut SF2: [u16; 2] = [1, 0x0102];
static mut SG: [u16; 2] = [1, 0x0102];
static mut SG2: [u16; 2] = [1, 0x0102];

#[kani::proof]
fn safe_static_elem_store_halves_elem_view() {
    unsafe {
        SB[1] = 0x0304;
    }
    let addr = unsafe { addr_of!(SB) } as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let p = (((hi as usize) << 32) | (lo as usize)) as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0304);
}

#[kani::proof]
fn bug_static_elem_store_halves_elem_view() {
    unsafe {
        SB2[1] = 0x0304;
    }
    let addr = unsafe { addr_of!(SB2) } as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let p = (((hi as usize) << 32) | (lo as usize)) as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0102);
}

#[kani::proof]
fn safe_static_nostore_halves_elem_view() {
    let addr = addr_of!(SC) as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let p = (((hi as usize) << 32) | (lo as usize)) as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0102);
}

#[kani::proof]
fn bug_static_nostore_halves_elem_view() {
    let addr = addr_of!(SC2) as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let p = (((hi as usize) << 32) | (lo as usize)) as *const u16;
    assert!(unsafe { *p.add(1) } == 1);
}

#[kani::proof]
fn safe_static_u32_halves_elem_store() {
    unsafe {
        SA[1] = 0x0304;
    }
    let addr = unsafe { addr_of!(SA) } as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let p = (((hi as usize) << 32) | (lo as usize)) as *const u8;
    assert!(unsafe { *p.add(2) } == 4);
}

#[kani::proof]
fn bug_static_u32_halves_elem_store() {
    unsafe {
        SA2[1] = 0x0304;
    }
    let addr = unsafe { addr_of!(SA2) } as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let p = (((hi as usize) << 32) | (lo as usize)) as *const u8;
    assert!(unsafe { *p.add(2) } == 2);
}

#[kani::proof]
fn safe_static_u32_halves_nostore() {
    let addr = addr_of!(SE) as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let p = (((hi as usize) << 32) | (lo as usize)) as *const u8;
    assert!(unsafe { *p.add(2) } == 2);
}

#[kani::proof]
fn bug_static_u32_halves_nostore() {
    let addr = addr_of!(SE2) as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let p = (((hi as usize) << 32) | (lo as usize)) as *const u8;
    assert!(unsafe { *p.add(2) } == 1);
}

// ---- the same halves, back through a transmute and through a union ----

#[kani::proof]
fn safe_static_halves_transmute_bytes() {
    unsafe {
        SF[1] = 0x0304;
    }
    let addr = unsafe { addr_of!(SF) } as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let p: *const u8 = unsafe { std::mem::transmute(((hi as usize) << 32) | (lo as usize)) };
    assert!(unsafe { *p.add(2) } == 4);
}

#[kani::proof]
fn bug_static_halves_transmute_bytes() {
    unsafe {
        SF2[1] = 0x0304;
    }
    let addr = unsafe { addr_of!(SF2) } as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let p: *const u8 = unsafe { std::mem::transmute(((hi as usize) << 32) | (lo as usize)) };
    assert!(unsafe { *p.add(2) } == 2);
}

union AddrOrPtr {
    a: usize,
    p: *const u8,
}

#[kani::proof]
fn safe_static_halves_union_bytes() {
    unsafe {
        SG[1] = 0x0304;
    }
    let addr = unsafe { addr_of!(SG) } as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let u = AddrOrPtr { a: ((hi as usize) << 32) | (lo as usize) };
    let p = unsafe { u.p };
    assert!(unsafe { *p.add(2) } == 4);
}

#[kani::proof]
fn bug_static_halves_union_bytes() {
    unsafe {
        SG2[1] = 0x0304;
    }
    let addr = unsafe { addr_of!(SG2) } as usize;
    let lo = addr as u32;
    let hi = (addr >> 32) as u32;
    let u = AddrOrPtr { a: ((hi as usize) << 32) | (lo as usize) };
    let p = unsafe { u.p };
    assert!(unsafe { *p.add(2) } == 2);
}

// ---- a constant address naming a model object (the model numbers objects
// from 1 in the high word of a pointer): fails closed where it is read ----

#[kani::proof]
fn bug_crafted_const_names_heap_id() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let q = 0x2_0000_0000usize as *const u8;
    let v = unsafe { *q };
}

#[kani::proof]
fn bug_crafted_const_transmute_names_heap_id() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let q: *const u8 = unsafe { std::mem::transmute(0x2_0000_0000usize) };
    let v = unsafe { *q };
}

// ---- wrapping pointer arithmetic past the object (no integer involved): the
// deref check has no bounds for a symbolic object lane, the reason the round
// trips above keep their fail-closed invalidation. The bug rows are known-red
// missed bugs, identical on main: a heap pointer stepped by the wrapping family
// (`wrapping_add`, `wrapping_offset`, `wrapping_byte_add`) has a symbolic object
// lane, `heap_access_checks` skips the bounds check for it, and nothing records
// a reason (the in-bounds family's step records offset_provenance_unresolved) ----

#[kani::proof]
fn safe_wrapping_byte_add_in_bounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u16;
    let q = p.wrapping_byte_add(2);
    assert!(unsafe { *q } == 2);
}

#[kani::proof]
fn bug_wrapping_byte_add_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u16;
    let q = p.wrapping_byte_add(4);
    let v = unsafe { *q };
}

#[kani::proof]
fn safe_wrapping_add_in_bounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u16;
    let q = p.wrapping_add(1);
    assert!(unsafe { *q } == 2);
}

#[kani::proof]
fn bug_wrapping_add_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u16;
    let q = p.wrapping_add(2);
    let v = unsafe { *q };
}

#[kani::proof]
fn safe_wrapping_offset_in_bounds() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u16;
    let q = p.wrapping_offset(1);
    assert!(unsafe { *q } == 2);
}

#[kani::proof]
fn bug_wrapping_offset_oob() {
    let bx: Box<[u16; 2]> = Box::new([1, 2]);
    let p = addr_of!(*bx) as *const u16;
    let q = p.wrapping_offset(2);
    let v = unsafe { *q };
}

#[kani::proof]
fn safe_vec_wrapping_add_in_bounds() {
    let v: Vec<u16> = vec![1, 2];
    let p = v.as_ptr();
    let q = p.wrapping_add(1);
    assert!(unsafe { *q } == 2);
}

#[kani::proof]
fn bug_vec_wrapping_add_oob() {
    let v: Vec<u16> = vec![1, 2];
    let p = v.as_ptr();
    let q = p.wrapping_add(2);
    let x = unsafe { *q };
}

// ---- the null object: a constant address below 2^32 stays exact ----

#[kani::proof]
fn bug_const_small_address_read() {
    let q = 0x1000 as *const u8;
    let v = unsafe { *q };
}

// ---- a literal address naming a model object, reaching the dereference
// another way (net 3 follows each) ----

#[kani::proof]
fn bug_crafted_const_through_local() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let a: usize = 0x2_0000_0000;
    let q = a as *const u8;
    let v = unsafe { *q };
}

#[inline(never)]
fn read_at(a: usize) -> u8 {
    unsafe { *(a as *const u8) }
}

#[kani::proof]
fn bug_crafted_const_helper_reader() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let v = read_at(0x2_0000_0000);
}

#[inline(never)]
fn crafted_pointer() -> *const u8 {
    0x2_0000_0000usize as *const u8
}

#[kani::proof]
fn bug_crafted_const_helper_returns() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let v = unsafe { *crafted_pointer() };
}

#[kani::proof]
fn bug_crafted_const_without_provenance() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let q: *const u8 = std::ptr::without_provenance(0x2_0000_0000);
    let v = unsafe { *q };
}

#[kani::proof]
fn bug_crafted_const_names_stack_slot() {
    let x: [u8; 8] = [7; 8];
    let y: [u8; 8] = [9; 8];
    let q = 0x1_0000_0000usize as *const u8;
    let v = unsafe { *q };
    let w = unsafe { *(0x2_0000_0000usize as *const u8) };
}

#[kani::proof]
fn bug_crafted_const_write() {
    let mut x: [u8; 8] = [7; 8];
    let q = 0x1_0000_0000usize as *mut u8;
    unsafe { *q = 3 };
}

// ---- the literal never dereferenced, or used as a number: proofs stand ----

#[kani::proof]
fn safe_crafted_const_compared_only() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let q = 0x2_0000_0000usize as *const u8;
    assert!(!q.is_null());
    assert!(q as usize == 0x2_0000_0000);
    assert!(bx[3] == 7);
}

#[kani::proof]
fn safe_const_literal_as_a_number() {
    let a: u64 = 0x2_0000_0000;
    assert!(a.checked_add(1) == Some(0x2_0000_0001));
    assert!(a.wrapping_mul(2) == 0x4_0000_0000);
}

// ---- stored where another body loads it; and literal pointers beside an
// unrelated assertion (a literal names no object, so it invalidates nothing) ----

static mut CRAFTED: *const u8 = std::ptr::null();

#[inline(never)]
fn read_crafted() -> u8 {
    unsafe { *CRAFTED }
}

#[kani::proof]
fn bug_crafted_const_stored_in_static() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    unsafe { CRAFTED = 0x2_0000_0000usize as *const u8 };
    let v = read_crafted();
}

#[kani::proof]
fn bug_crafted_const_beside_box_assertion() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let q = 0x1_0000_0000usize as *const u8;
    let r = 0x2_0000_0000usize as *const u8;
    assert!(q != r);
    assert!(bx[2] == 8);
}

#[kani::proof]
fn safe_crafted_const_beside_box_assertion() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let q = 0x1_0000_0000usize as *const u8;
    let r = 0x2_0000_0000usize as *const u8;
    assert!(q != r);
    assert!(bx[2] == 7);
}

// ---- the literal handed as a number: to the standard library on its own data
// it is a number; into a harness type whose From reads it, it fails closed ----

use std::convert::TryFrom;

struct ReadAt(u8);

impl From<usize> for ReadAt {
    fn from(a: usize) -> Self {
        ReadAt(unsafe { *(a as *const u8) })
    }
}

#[kani::proof]
fn bug_crafted_const_into_harness_type() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let r: ReadAt = 0x2_0000_0000usize.into();
}

#[kani::proof]
fn safe_const_count_offsets_a_pointer() {
    let a = [0u32; 4];
    let count: usize = 0x2_0000_0008;
    let bytes = count.checked_mul(4).unwrap();
    assert!(isize::try_from(bytes).is_ok());
    let q = a.as_ptr().wrapping_add(count);
    assert!(!q.is_null());
}

// ---- a reference made through such a pointer, handed to the formatting
// machinery (which reads it where no scan looks): a read ----

#[kani::proof]
fn bug_crafted_const_reference_printed() {
    let bx: Box<[u8; 8]> = Box::new([7; 8]);
    let q = 0x2_0000_0000usize as *const u8;
    let r = unsafe { &*q };
    println!("{}", r);
}
