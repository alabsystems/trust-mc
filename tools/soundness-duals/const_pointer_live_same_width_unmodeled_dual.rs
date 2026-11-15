// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_u32_into_struct_with_bool  -> VERIFICATION:- SUCCESSFUL
//   bug_u32_into_struct_with_bool   -> VERIFICATION:- FAILED (assertion)
//   safe_u32_into_nested_struct     -> VERIFICATION:- SUCCESSFUL
//   bug_u32_into_nested_struct      -> VERIFICATION:- FAILED (assertion)
//
// A store of size_of the static's bytes, of ANOTHER type, at the base of a
// struct static mut whose layout the memory-order lane does not model: a
// `bool` field (whose byte may not be 0 or 1) and a nested struct (round-3
// review of fix/chc-atomic-as-ptr-live, high finding, the shapes beside
// const_pointer_live_same_width_dual.rs). The scalar store lane (#428)
// unflattened the u32 in declaration order and certified the safe rows
// Genuine; the CHC lane now havocs the static and fails closed. CHC only: the
// BMC lane certifies both safe rows Genuine, on main too (its code is
// unchanged here), which a row marked for the CHC lane's false failure could
// not also record.
#![allow(dead_code, static_mut_refs)]
use std::ptr::addr_of_mut;

#[repr(C)]
struct PB {
    a: u8,
    flag: bool,
    c: u16,
}
#[repr(C)]
struct Inner {
    a: u8,
    b: u8,
}
#[repr(C)]
struct Nested {
    inner: Inner,
    c: u16,
}

static mut PF: PB = PB { a: 1, flag: false, c: 3 };
static mut NS: Nested = Nested { inner: Inner { a: 1, b: 2 }, c: 3 };

#[kani::proof]
fn safe_u32_into_struct_with_bool() {
    unsafe { *(addr_of_mut!(PF) as *mut u32) = 0x0009_0107 };
    assert!(unsafe { PF.a } == 7 && unsafe { PF.flag } && unsafe { PF.c } == 9);
}
#[kani::proof]
fn bug_u32_into_struct_with_bool() {
    unsafe { *(addr_of_mut!(PF) as *mut u32) = 0x0009_0107 };
    assert!(unsafe { PF.c } == 3);
}
#[kani::proof]
fn safe_u32_into_nested_struct() {
    unsafe { *(addr_of_mut!(NS) as *mut u32) = 0x0009_0807 };
    assert!(unsafe { NS.inner.a } == 7 && unsafe { NS.inner.b } == 8 && unsafe { NS.c } == 9);
}
#[kani::proof]
fn bug_u32_into_nested_struct() {
    unsafe { *(addr_of_mut!(NS) as *mut u32) = 0x0009_0807 };
    assert!(unsafe { NS.inner.b } == 2);
}
