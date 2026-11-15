// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_u32_into_u16_pair         -> VERIFICATION:- SUCCESSFUL
//   bug_u32_into_u16_pair          -> VERIFICATION:- FAILED (assertion)
//   safe_u32_into_u16_pair_read_b  -> VERIFICATION:- SUCCESSFUL
//   bug_u32_into_u16_pair_read_b   -> VERIFICATION:- FAILED (assertion)
//   safe_u32_into_mixed_struct     -> VERIFICATION:- SUCCESSFUL
//   bug_u32_into_mixed_struct      -> VERIFICATION:- FAILED (assertion)
//   safe_u32_into_u16_tuple        -> VERIFICATION:- SUCCESSFUL
//   bug_u32_into_u16_tuple         -> VERIFICATION:- FAILED (assertion)
//   safe_u32_into_u16_array        -> VERIFICATION:- SUCCESSFUL
//   bug_u32_into_u16_array         -> VERIFICATION:- FAILED (assertion)
//   safe_u32_into_u8_array         -> VERIFICATION:- SUCCESSFUL
//   bug_u32_into_u8_array          -> VERIFICATION:- FAILED (assertion)
//   safe_u16_pair_into_u32         -> VERIFICATION:- SUCCESSFUL
//   bug_u16_pair_into_u32          -> VERIFICATION:- FAILED (assertion)
//   safe_u32_into_i32              -> VERIFICATION:- SUCCESSFUL
//   bug_u32_into_i32               -> VERIFICATION:- FAILED (assertion)
//
// A store of size_of the static's bytes, of ANOTHER type, at the base of a
// static mut (round-3 review of fix/chc-atomic-as-ptr-live, high finding):
// `*(addr_of_mut!(PS) as *mut u32) = 0x0005_0006` into a repr(C)
// `{ a: u16, b: u16 }` gives `a = 6, b = 5` (little-endian memory order). The
// scalar store lane (#428) returned the u32 as the struct's whole value, and
// the constraint unflattened it in declaration order (`a = 5, b = 6`), so the
// safe rows were certified Genuine. The arrays, the struct-into-integer row
// and the integer-into-integer row are the controls the fix must keep.
#![allow(dead_code, static_mut_refs)]
use std::ptr::addr_of_mut;

#[repr(C)]
struct P2 {
    a: u16,
    b: u16,
}
#[repr(C)]
struct P3 {
    a: u8,
    b: u8,
    c: u16,
}

static mut PS: P2 = P2 { a: 1, b: 2 };
static mut PT: P3 = P3 { a: 1, b: 2, c: 3 };
static mut TU: (u16, u16) = (1, 2);
static mut AR2: [u16; 2] = [1, 2];
static mut AR4: [u8; 4] = [1, 2, 3, 4];
static mut N: u32 = 0x0102_0304;
static mut I: i32 = 1;

#[kani::proof]
fn safe_u32_into_u16_pair() {
    unsafe { *(addr_of_mut!(PS) as *mut u32) = 0x0005_0006 };
    assert!(unsafe { PS.a } == 6 && unsafe { PS.b } == 5);
}
#[kani::proof]
fn bug_u32_into_u16_pair() {
    unsafe { *(addr_of_mut!(PS) as *mut u32) = 0x0005_0006 };
    assert!(unsafe { PS.a } == 5);
}
#[kani::proof]
fn safe_u32_into_u16_pair_read_b() {
    unsafe { *(addr_of_mut!(PS) as *mut u32) = 0x0005_0006 };
    assert!(unsafe { PS.b } == 5);
}
#[kani::proof]
fn bug_u32_into_u16_pair_read_b() {
    unsafe { *(addr_of_mut!(PS) as *mut u32) = 0x0005_0006 };
    assert!(unsafe { PS.b } == 6);
}
#[kani::proof]
fn safe_u32_into_mixed_struct() {
    unsafe { *(addr_of_mut!(PT) as *mut u32) = 0x0009_0807 };
    assert!(unsafe { PT.a } == 7 && unsafe { PT.b } == 8 && unsafe { PT.c } == 9);
}
#[kani::proof]
fn bug_u32_into_mixed_struct() {
    unsafe { *(addr_of_mut!(PT) as *mut u32) = 0x0009_0807 };
    assert!(unsafe { PT.c } == 3);
}
#[kani::proof]
fn safe_u32_into_u16_tuple() {
    unsafe { *(addr_of_mut!(TU) as *mut u32) = 0x0005_0006 };
    assert!(unsafe { TU.0 } == 6 && unsafe { TU.1 } == 5);
}
#[kani::proof]
fn bug_u32_into_u16_tuple() {
    unsafe { *(addr_of_mut!(TU) as *mut u32) = 0x0005_0006 };
    assert!(unsafe { TU.1 } == 6);
}
#[kani::proof]
fn safe_u32_into_u16_array() {
    unsafe { *(addr_of_mut!(AR2) as *mut u32) = 0x0005_0006 };
    assert!(unsafe { AR2[0] } == 6 && unsafe { AR2[1] } == 5);
}
#[kani::proof]
fn bug_u32_into_u16_array() {
    unsafe { *(addr_of_mut!(AR2) as *mut u32) = 0x0005_0006 };
    assert!(unsafe { AR2[1] } == 2);
}
#[kani::proof]
fn safe_u32_into_u8_array() {
    unsafe { *(addr_of_mut!(AR4) as *mut u32) = 0x0A0B_0C0D };
    assert!(unsafe { AR4[0] } == 0x0D && unsafe { AR4[3] } == 0x0A);
}
#[kani::proof]
fn bug_u32_into_u8_array() {
    unsafe { *(addr_of_mut!(AR4) as *mut u32) = 0x0A0B_0C0D };
    assert!(unsafe { AR4[3] } == 4);
}
#[kani::proof]
fn safe_u16_pair_into_u32() {
    unsafe { *(addr_of_mut!(N) as *mut P2) = P2 { a: 6, b: 5 } };
    assert!(unsafe { N } == 0x0005_0006);
}
#[kani::proof]
fn bug_u16_pair_into_u32() {
    unsafe { *(addr_of_mut!(N) as *mut P2) = P2 { a: 6, b: 5 } };
    assert!(unsafe { N } == 0x0006_0005);
}
#[kani::proof]
fn safe_u32_into_i32() {
    unsafe { *(addr_of_mut!(I) as *mut u32) = 0xFFFF_FFFE };
    assert!(unsafe { I } == -2);
}
#[kani::proof]
fn bug_u32_into_i32() {
    unsafe { *(addr_of_mut!(I) as *mut u32) = 0xFFFF_FFFE };
    assert!(unsafe { I } == 1);
}
