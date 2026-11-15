// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: the far-pointer walk (heap/stack_address.rs) took
// every `Box`'s data pointer as a fresh allocation of the box's pointee type at
// its offset 0, "whatever wrote the box": `Box::from_raw` of anything else is
// undefined behavior, but Kani does not report it, and the pointer a box built
// that way holds is the one it was built from. A far pointer round-tripped
// through `Box::from_raw` / `Box::into_raw` was compared as never far, and a
// 4-byte heap block taken as a `Box<[u8; 16]>` was bounded by 16 bytes: clean
// proofs where Kani fails. The walk followed no pointer through the box either,
// so a far pointer stepped back after the round trip drew a free far bit and a
// program Kani and main prove failed closed. Found by the first review of round
// 9 of fix/chc-false-certificates (2026-10-14, probes rv_far_obs.rs,
// rv_box_bound.rs, rv_alloc_far.rs). A box's pointer is now its source's:
// `Box::new` (a fresh allocation) or `Box::from_raw`'s argument, followed.

fn far_k() -> usize {
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    k
}

#[kani::proof]
fn bug_far_pointer_box_round_trip_ne() {
    let mut a = [1u8; 4];
    let p = a.as_mut_ptr();
    let q = p.wrapping_byte_add(far_k());
    let b: Box<u8> = unsafe { Box::from_raw(q) };
    let r = Box::into_raw(b);
    assert!(r != p);
}

#[kani::proof]
fn bug_heap4_as_box16_step_reads_past_end() {
    let small = Box::into_raw(Box::new([7u8; 4]));
    let b: Box<[u8; 16]> = unsafe { Box::from_raw(small as *mut [u8; 16]) };
    let p = Box::into_raw(b) as *mut u8;
    let k: usize = kani::any();
    kani::assume(k >= 8 && k < 12);
    let q = p.wrapping_add(k);
    let v = unsafe { *q };
    assert!(v == v);
}

#[kani::proof]
fn safe_stack16_as_box_u8_deref() {
    let mut a = [7u8; 16];
    let b: Box<u8> = unsafe { Box::from_raw(a.as_mut_ptr()) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 7);
}

#[kani::proof]
fn bug_stack16_as_box_u8_deref() {
    let mut a = [7u8; 16];
    let b: Box<u8> = unsafe { Box::from_raw(a.as_mut_ptr()) };
    let p = Box::into_raw(b);
    assert!(unsafe { *p } == 8);
}

#[kani::proof]
fn safe_box_leak_step_in_bounds() {
    let r: &'static mut [u16; 4] = Box::leak(Box::new([9u16; 4]));
    let p = r as *mut [u16; 4] as *mut u16;
    let k: usize = kani::any();
    kani::assume(k < 4);
    assert!(unsafe { *p.wrapping_add(k) } == 9);
}

#[kani::proof]
fn bug_box_leak_step_out_of_bounds() {
    let r: &'static mut [u16; 4] = Box::leak(Box::new([9u16; 4]));
    let p = r as *mut [u16; 4] as *mut u16;
    let k: usize = kani::any();
    kani::assume(k >= 4 && k < 6);
    let v = unsafe { *p.wrapping_add(k) };
    assert!(v == v);
}

#[kani::proof]
fn bug_stack4_as_box16_step_reads_past_end() {
    let mut a = [7u8; 4];
    let b: Box<[u8; 16]> = unsafe { Box::from_raw(&mut a as *mut [u8; 4] as *mut [u8; 16]) };
    let p = Box::into_raw(b) as *mut u8;
    let k: usize = kani::any();
    kani::assume(k >= 8 && k < 12);
    let q = p.wrapping_add(k);
    let v = unsafe { *q };
    assert!(v == v);
}

#[kani::proof]
fn safe_stack16_as_box_u8_step_in_bounds() {
    let mut a = [7u8; 16];
    let b: Box<u8> = unsafe { Box::from_raw(a.as_mut_ptr()) };
    let p = Box::into_raw(b);
    let k: usize = kani::any();
    kani::assume(k < 16);
    let q = p.wrapping_add(k);
    assert!(unsafe { *q } == 7);
}

#[kani::proof]
fn safe_zst_box_round_trip_far_step_back() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k = far_k();
    let q = p.wrapping_byte_add(k) as *mut ();
    let b: Box<()> = unsafe { Box::from_raw(q) };
    let r = (Box::into_raw(b) as *const u8).wrapping_byte_sub(k);
    assert!(unsafe { *r } == 1);
}

#[kani::proof]
fn bug_zst_box_round_trip_far_step_back() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k = far_k();
    let q = p.wrapping_byte_add(k) as *mut ();
    let b: Box<()> = unsafe { Box::from_raw(q) };
    let r = (Box::into_raw(b) as *const u8).wrapping_byte_sub(k);
    assert!(unsafe { *r } == 2);
}

#[kani::proof]
fn bug_zst_box_round_trip_far_ne() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_add(far_k()) as *mut ();
    let b: Box<()> = unsafe { Box::from_raw(q) };
    let r = Box::into_raw(b) as *const u8;
    assert!(r != p);
}

#[kani::proof]
fn safe_box_new_step_in_bounds() {
    let b = Box::new([3u32; 4]);
    let p = Box::into_raw(b) as *mut u32;
    let k: usize = kani::any();
    kani::assume(k < 4);
    let q = p.wrapping_add(k);
    assert!(unsafe { *q } == 3);
}

#[kani::proof]
fn bug_box_new_step_out_of_bounds() {
    let b = Box::new([3u32; 4]);
    let p = Box::into_raw(b) as *mut u32;
    let k: usize = kani::any();
    kani::assume(k >= 4 && k < 6);
    let q = p.wrapping_add(k);
    let v = unsafe { *q };
    assert!(v == v);
}
