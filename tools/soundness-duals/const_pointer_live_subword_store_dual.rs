// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_direct_byte_write_read      -> VERIFICATION:- SUCCESSFUL
//   bug_direct_byte_write_read       -> VERIFICATION:- FAILED (assertion)
//   safe_direct_byte1_write_read     -> VERIFICATION:- SUCCESSFUL
//   bug_direct_byte1_write_read      -> VERIFICATION:- FAILED (assertion)
//   safe_direct_half2_write_read     -> VERIFICATION:- SUCCESSFUL
//   bug_direct_half2_write_read      -> VERIFICATION:- FAILED (assertion)
//   safe_signed_byte_write_read      -> VERIFICATION:- SUCCESSFUL
//   bug_signed_byte_write_read       -> VERIFICATION:- FAILED (assertion)
//   safe_byte_store_volatile_read    -> VERIFICATION:- SUCCESSFUL
//   bug_byte_store_volatile_read     -> VERIFICATION:- FAILED (assertion)
//   safe_byte_store_ptr_read         -> VERIFICATION:- SUCCESSFUL
//   bug_byte_store_ptr_read          -> VERIFICATION:- FAILED (assertion)
//   safe_byte_store_read_byte1       -> VERIFICATION:- SUCCESSFUL
//   bug_byte_store_read_byte1        -> VERIFICATION:- FAILED (assertion)
//   safe_half_store_volatile_read    -> VERIFICATION:- SUCCESSFUL
//   bug_half_store_volatile_read     -> VERIFICATION:- FAILED (assertion)
//   safe_callee_byte_write_read      -> VERIFICATION:- SUCCESSFUL
//   bug_callee_byte_write_read       -> VERIFICATION:- FAILED (assertion)
//   safe_callee_byte1_write_read     -> VERIFICATION:- SUCCESSFUL
//   bug_callee_byte1_write_read      -> VERIFICATION:- FAILED (assertion)
//   safe_dyn_byte_write_read         -> VERIFICATION:- SUCCESSFUL
//   bug_dyn_byte_write_read          -> VERIFICATION:- FAILED (assertion)
//   safe_dyn_byte_write_raw_read     -> VERIFICATION:- SUCCESSFUL
//   bug_dyn_byte_write_raw_read      -> VERIFICATION:- FAILED (assertion)
//   safe_callee_half_write_raw_read  -> VERIFICATION:- SUCCESSFUL
//   bug_callee_half_write_raw_read   -> VERIFICATION:- FAILED (assertion)
//   safe_callee_byte_atomic_load     -> VERIFICATION:- SUCCESSFUL
//   bug_callee_byte_atomic_load      -> VERIFICATION:- FAILED (assertion)
//   safe_direct_byte_atomic_load     -> VERIFICATION:- SUCCESSFUL
//   bug_direct_byte_atomic_load      -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. A store of fewer bytes than an integer static holds
// writes only those bytes. The CHC lane's scalar store through a pointer to
// a static's base (#428) and the inline walker's static mirror coerced the
// stored value to the static's width, so `*(addr_of_mut!(N) as *mut u8) = 9`
// set `static mut N: u32 = 0x01020304` to 9: `N == 9` PROVED and the safe
// `N == 0x01020309` was certified Genuine (round-2 review of
// fix/chc-atomic-as-ptr-live). The statement lane now replaces the stored
// bytes in the static's value (`splice_integer_bytes`); the walker leaves the
// static's state stale and fails closed.
#![allow(dead_code, static_mut_refs)]
use std::ptr::{addr_of, addr_of_mut};
use std::sync::atomic::{AtomicU32, Ordering};

static mut N1: u32 = 0x0102_0304;
static mut N2: u32 = 0x0102_0304;
static mut N3: u32 = 0x0102_0304;
static mut N4: u32 = 0x0102_0304;
static mut N5: u32 = 0x0102_0304;
static mut N6: u32 = 0x0102_0304;
static mut N7: u32 = 0x0102_0304;
static mut N8: u32 = 0x0102_0304;
static mut H1: u64 = 0x0102_0304_0506_0708;
static mut H2: u64 = 0x0102_0304_0506_0708;
static mut I1: i32 = -1;
static mut I2: i32 = -1;
static AT: AtomicU32 = AtomicU32::new(0x0102_0304);
static AT2: AtomicU32 = AtomicU32::new(0x0102_0304);

trait W {
    fn w(&self, p: *mut u8);
}
struct S;
impl W for S {
    fn w(&self, p: *mut u8) {
        unsafe { *p = 9 }
    }
}
fn wb(p: *mut u8) {
    unsafe { *p = 9 }
}
fn wh(p: *mut u16) {
    unsafe { *p = 9 }
}

// a byte at offset 0, written in the harness, read back as the static
#[kani::proof]
fn safe_direct_byte_write_read() {
    unsafe { *(addr_of_mut!(N1) as *mut u8) = 9 };
    assert!(unsafe { N1 } == 0x0102_0309);
}
#[kani::proof]
fn bug_direct_byte_write_read() {
    unsafe { *(addr_of_mut!(N2) as *mut u8) = 9 };
    assert!(unsafe { N2 } == 9);
}
// a byte at offset 1, written in the harness
#[kani::proof]
fn safe_direct_byte1_write_read() {
    unsafe { *(addr_of_mut!(N3) as *mut u8).add(1) = 9 };
    assert!(unsafe { N3 } == 0x0102_0904);
}
#[kani::proof]
fn bug_direct_byte1_write_read() {
    unsafe { *(addr_of_mut!(N4) as *mut u8).add(1) = 9 };
    assert!(unsafe { N4 } == 0x0102_0304);
}
// a u16 at offset 2
#[kani::proof]
fn safe_direct_half2_write_read() {
    unsafe { *(addr_of_mut!(N5) as *mut u16).add(1) = 9 };
    assert!(unsafe { N5 } == 0x0009_0304);
}
#[kani::proof]
fn bug_direct_half2_write_read() {
    unsafe { *(addr_of_mut!(N6) as *mut u16).add(1) = 9 };
    assert!(unsafe { N6 } == 9);
}
// a signed byte into a signed static
#[kani::proof]
fn safe_signed_byte_write_read() {
    unsafe { *(addr_of_mut!(I1) as *mut i8) = 0 };
    assert!(unsafe { I1 } == -256);
}
#[kani::proof]
fn bug_signed_byte_write_read() {
    unsafe { *(addr_of_mut!(I2) as *mut i8) = 0 };
    assert!(unsafe { I2 } == 0);
}
// a byte at offset 0, then a volatile read of the whole static
#[kani::proof]
fn safe_byte_store_volatile_read() {
    unsafe { *(addr_of_mut!(N7) as *mut u8) = 9 };
    let v = unsafe { std::ptr::read_volatile(addr_of!(N7)) };
    assert!(v == 0x0102_0309);
}
#[kani::proof]
fn bug_byte_store_volatile_read() {
    unsafe { *(addr_of_mut!(N8) as *mut u8) = 9 };
    let v = unsafe { std::ptr::read_volatile(addr_of!(N8)) };
    assert!(v == 9);
}
// a byte at offset 0, then ptr::read
#[kani::proof]
fn safe_byte_store_ptr_read() {
    unsafe { *(addr_of_mut!(N1) as *mut u8) = 9 };
    let v = unsafe { std::ptr::read(addr_of!(N1)) };
    assert!(v == 0x0102_0309);
}
#[kani::proof]
fn bug_byte_store_ptr_read() {
    unsafe { *(addr_of_mut!(N2) as *mut u8) = 9 };
    let v = unsafe { std::ptr::read(addr_of!(N2)) };
    assert!(v == 9);
}
// a byte at offset 0, then read byte 1
#[kani::proof]
fn safe_byte_store_read_byte1() {
    unsafe { *(addr_of_mut!(N3) as *mut u8) = 9 };
    let v = unsafe { *(addr_of!(N3) as *const u8).add(1) };
    assert!(v == 3);
}
#[kani::proof]
fn bug_byte_store_read_byte1() {
    unsafe { *(addr_of_mut!(N4) as *mut u8) = 9 };
    let v = unsafe { *(addr_of!(N4) as *const u8).add(1) };
    assert!(v == 0);
}
// a u32 at offset 0 of a u64, then a volatile read
#[kani::proof]
fn safe_half_store_volatile_read() {
    unsafe { *(addr_of_mut!(H1) as *mut u32) = 9 };
    let v = unsafe { std::ptr::read_volatile(addr_of!(H1)) };
    assert!(v == 0x0102_0304_0000_0009);
}
#[kani::proof]
fn bug_half_store_volatile_read() {
    unsafe { *(addr_of_mut!(H2) as *mut u32) = 9 };
    let v = unsafe { std::ptr::read_volatile(addr_of!(H2)) };
    assert!(v == 9);
}
// a byte at offset 0 through a callee
#[kani::proof]
fn safe_callee_byte_write_read() {
    wb(addr_of_mut!(N5) as *mut u8);
    assert!(unsafe { N5 } == 0x0102_0309);
}
#[kani::proof]
fn bug_callee_byte_write_read() {
    wb(addr_of_mut!(N6) as *mut u8);
    assert!(unsafe { N6 } == 9);
}
// a byte at offset 1 through a callee
#[kani::proof]
fn safe_callee_byte1_write_read() {
    wb(unsafe { (addr_of_mut!(N7) as *mut u8).add(1) });
    assert!(unsafe { N7 } == 0x0102_0904);
}
#[kani::proof]
fn bug_callee_byte1_write_read() {
    wb(unsafe { (addr_of_mut!(N8) as *mut u8).add(1) });
    assert!(unsafe { N8 } == 0x0102_0304);
}
// a byte at offset 0 through a dyn method (the inline walker)
#[kani::proof]
fn safe_dyn_byte_write_read() {
    let s: &dyn W = &S;
    s.w(addr_of_mut!(N1) as *mut u8);
    assert!(unsafe { N1 } == 0x0102_0309);
}
#[kani::proof]
fn bug_dyn_byte_write_read() {
    let s: &dyn W = &S;
    s.w(addr_of_mut!(N2) as *mut u8);
    assert!(unsafe { N2 } == 9);
}
// through a dyn method, then a raw read of the static
#[kani::proof]
fn safe_dyn_byte_write_raw_read() {
    let s: &dyn W = &S;
    s.w(addr_of_mut!(N3) as *mut u8);
    assert!(unsafe { *addr_of!(N3) } == 0x0102_0309);
}
#[kani::proof]
fn bug_dyn_byte_write_raw_read() {
    let s: &dyn W = &S;
    s.w(addr_of_mut!(N4) as *mut u8);
    assert!(unsafe { *addr_of!(N4) } == 9);
}
// a u16 at offset 0 of a u64 through a callee, then a raw read
#[kani::proof]
fn safe_callee_half_write_raw_read() {
    wh(addr_of_mut!(H1) as *mut u16);
    assert!(unsafe { *addr_of!(H1) } == 0x0102_0304_0506_0009);
}
#[kani::proof]
fn bug_callee_half_write_raw_read() {
    wh(addr_of_mut!(H2) as *mut u16);
    assert!(unsafe { *addr_of!(H2) } == 9);
}
// a byte at offset 0 of an atomic static through a callee, then load
#[kani::proof]
fn safe_callee_byte_atomic_load() {
    wb(AT.as_ptr() as *mut u8);
    assert!(AT.load(Ordering::SeqCst) == 0x0102_0309);
}
#[kani::proof]
fn bug_callee_byte_atomic_load() {
    wb(AT2.as_ptr() as *mut u8);
    assert!(AT2.load(Ordering::SeqCst) == 9);
}
// a byte at offset 0 of an atomic static in the harness, then load
#[kani::proof]
fn safe_direct_byte_atomic_load() {
    unsafe { *(AT.as_ptr() as *mut u8) = 9 };
    assert!(AT.load(Ordering::SeqCst) == 0x0102_0309);
}
#[kani::proof]
fn bug_direct_byte_atomic_load() {
    unsafe { *(AT2.as_ptr() as *mut u8) = 9 };
    assert!(AT2.load(Ordering::SeqCst) == 9);
}
