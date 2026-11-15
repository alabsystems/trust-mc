// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: full-width accesses through a raw pointer moved by a
// byte step that its ref-target metadata does not record (`(&mut p.a as *mut
// u32 as *mut u8).byte_add(4) as *mut u32`). The ref target names `p.a`, and a
// store, a read, `ptr::write` or `ptr::read` of the referent's own type took
// `p.a` whatever the pointer's offset: clean proofs where Kani reads or writes
// `p.b`, and certified false counterexamples for the safe twins, on main
// f5dfb8d48 and round 9 alike (self-review of round 10 of
// fix/chc-false-certificates, 2026-10-15). The narrower-store rule of the third
// review covered only stores of another width. A same-type access whose
// definition chain puts the pointer at a nonzero byte offset no metadata
// records is now read from, or spliced into, the containing local's bytes at
// that offset, or fails closed. Round 10's typed-store lowering of one-element
// copies goes through the same handlers (`*_copy_*` rows).
//
// Two more rows were holes the same self-review found under it, the first
// introduced before round 9 and the second the same on main: a store past the
// local's end through such a pointer as the function's last statement (the
// block's out-of-bounds violation had no rule to attach to and was dropped),
// and a byte step on an array element pointer, whose metadata added the byte
// count to the element index (`a[4]` for `byte_add(4)` on a `[u32; 3]`).

#![allow(invalid_reference_casting)]

#[repr(C)]
struct Pair {
    a: u32,
    b: u32,
}

#[kani::proof]
fn safe_store_byte_stepped() {
    let mut p = Pair { a: 1, b: 2 };
    let d = unsafe { (&mut p.a as *mut u32 as *mut u8).byte_add(4) } as *mut u32;
    unsafe { *d = 7 };
    assert!(p.a == 1 && p.b == 7);
}

#[kani::proof]
fn bug_store_byte_stepped() {
    let mut p = Pair { a: 1, b: 2 };
    let d = unsafe { (&mut p.a as *mut u32 as *mut u8).byte_add(4) } as *mut u32;
    unsafe { *d = 7 };
    assert!(p.a == 7);
}

#[kani::proof]
fn safe_read_byte_stepped() {
    let p = Pair { a: 1, b: 2 };
    let s = unsafe { (&p.a as *const u32 as *const u8).byte_add(4) } as *const u32;
    assert!(unsafe { *s } == 2);
}

#[kani::proof]
fn bug_read_byte_stepped() {
    let p = Pair { a: 1, b: 2 };
    let s = unsafe { (&p.a as *const u32 as *const u8).byte_add(4) } as *const u32;
    assert!(unsafe { *s } == 1);
}

#[kani::proof]
fn safe_ptr_write_byte_stepped() {
    let mut p = Pair { a: 1, b: 2 };
    let d = unsafe { (&mut p.a as *mut u32 as *mut u8).byte_add(4) } as *mut u32;
    unsafe { std::ptr::write(d, 7) };
    assert!(p.a == 1 && p.b == 7);
}

#[kani::proof]
fn bug_ptr_write_byte_stepped() {
    let mut p = Pair { a: 1, b: 2 };
    let d = unsafe { (&mut p.a as *mut u32 as *mut u8).byte_add(4) } as *mut u32;
    unsafe { std::ptr::write(d, 7) };
    assert!(p.a == 7);
}

#[kani::proof]
fn safe_ptr_read_byte_stepped() {
    let p = Pair { a: 1, b: 2 };
    let s = unsafe { (&p.a as *const u32 as *const u8).byte_add(4) } as *const u32;
    assert!(unsafe { std::ptr::read(s) } == 2);
}

#[kani::proof]
fn bug_ptr_read_byte_stepped() {
    let p = Pair { a: 1, b: 2 };
    let s = unsafe { (&p.a as *const u32 as *const u8).byte_add(4) } as *const u32;
    assert!(unsafe { std::ptr::read(s) } == 1);
}

#[kani::proof]
fn safe_copy_from_byte_stepped_src() {
    let p = Pair { a: 1, b: 2 };
    let s = unsafe { (&p.a as *const u32 as *const u8).byte_add(4) } as *const u32;
    let mut y: u32 = 0;
    unsafe { std::ptr::copy_nonoverlapping(s, &mut y, 1) };
    assert!(y == 2);
}

#[kani::proof]
fn bug_copy_from_byte_stepped_src() {
    let p = Pair { a: 1, b: 2 };
    let s = unsafe { (&p.a as *const u32 as *const u8).byte_add(4) } as *const u32;
    let mut y: u32 = 0;
    unsafe { std::ptr::copy_nonoverlapping(s, &mut y, 1) };
    assert!(y == 1);
}

#[kani::proof]
fn safe_copy_into_byte_stepped_dst() {
    let mut p = Pair { a: 1, b: 2 };
    let d = unsafe { (&mut p.a as *mut u32 as *mut u8).byte_add(4) } as *mut u32;
    unsafe { std::ptr::copy_nonoverlapping(&7u32, d, 1) };
    assert!(p.a == 1 && p.b == 7);
}

#[kani::proof]
fn bug_copy_into_byte_stepped_dst() {
    let mut p = Pair { a: 1, b: 2 };
    let d = unsafe { (&mut p.a as *mut u32 as *mut u8).byte_add(4) } as *mut u32;
    unsafe { std::ptr::copy_nonoverlapping(&7u32, d, 1) };
    assert!(p.a == 7);
}

#[kani::proof]
fn safe_store_byte_step_back_to_start() {
    let mut p = Pair { a: 1, b: 2 };
    let d = unsafe { (&mut p.a as *mut u32 as *mut u8).byte_add(4).byte_sub(4) } as *mut u32;
    unsafe { *d = 7 };
    assert!(p.a == 7 && p.b == 2);
}

#[kani::proof]
fn safe_copy_into_byte_array_at_offset4() {
    let mut a = [0u8; 8];
    let p = unsafe { a.as_mut_ptr().add(4) } as *mut u32;
    let x: u32 = 0x0403_0201;
    unsafe { std::ptr::copy_nonoverlapping(&x, p, 1) };
    assert!(a[4] == 1 && a[7] == 4 && a[0] == 0);
}

#[kani::proof]
fn bug_copy_into_byte_array_at_offset4() {
    let mut a = [0u8; 8];
    let p = unsafe { a.as_mut_ptr().add(4) } as *mut u32;
    let x: u32 = 0x0403_0201;
    unsafe { std::ptr::copy_nonoverlapping(&x, p, 1) };
    assert!(a[0] == 1);
}

// A store past the local's end as the last statement.
#[kani::proof]
fn bug_store_byte_step_past_end() {
    let mut p = Pair { a: 1, b: 2 };
    let d = unsafe { (&mut p.a as *mut u32 as *mut u8).byte_add(8) } as *mut u32;
    unsafe { *d = 7 };
}

// An array element pointer's byte step.
#[kani::proof]
fn safe_read_array_elem_byte_step() {
    let a = [1u32, 2, 3];
    let s = unsafe { (&a[0] as *const u32 as *const u8).byte_add(4) } as *const u32;
    assert!(unsafe { *s } == 2);
}

#[kani::proof]
fn bug_read_array_elem_byte_step() {
    let a = [1u32, 2, 3];
    let s = unsafe { (&a[0] as *const u32 as *const u8).byte_add(4) } as *const u32;
    assert!(unsafe { *s } == 1);
}

// A wider store past the local's end as the last statement.
#[kani::proof]
fn bug_wider_store_past_end_last_statement() {
    let mut x: u32 = 0;
    unsafe { *(&mut x as *mut u32 as *mut u64) = 1 };
}
