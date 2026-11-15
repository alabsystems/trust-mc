// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle: corpus-rev Kani (/home/ayates/tmc-measure/kani-src), run on this file
// (see the manifest entry): every `bug_` harness FAILS, every `safe_` harness is
// SUCCESSFUL, and every `sp_` harness (`#[kani::should_panic]` over a program
// that never panics) FAILS.
//
// WHY THIS FILE EXISTS: stores and reads through a pointer cast WIDER than the
// referent (stmt/codegen_stmt_store/deref_mem_mirror.rs
// `ref_store_reinterpretation`). A wider store inside the local that contains
// the referent is spliced across that local's whole image at the offset the
// pointer's definition chain establishes; past the local's end it is a
// memory-safety violation of the block (`record_block_violation`); an offset
// the chain does not establish fails closed. `ptr::write`'s local writeback
// takes the same reinterpretation.
//
// The first review of the sixth round of fix/chc-false-certificates
// (2026-10-02) measured: a wider store was mirrored as the referent's own type,
// with no allocation bound and no bytes past the referent. main and the fifth
// round's merged bundle hid it behind a misaligned-pointer failure Kani does not
// report; once bases were 2^48-aligned the out-of-bounds stores proved clean
// (finding 3; `bug_scalar_wide_store_oob` is a round-6 review probe that went
// from FAILED Genuine to SUCCESSFUL), a widened field store did not reach the
// next field, and a wide `ptr::write` into a local was a clean proof on every
// bundle (finding 5, `bug_wide_store_symbolic_ptr_field`).
//
// Reads wider than the referent field (`*(&s.a as *const u16 as *const u32)`)
// take the bytes of the containing local from the field's offset plus the
// pointer's chain offset when they stay in the local and its register is
// authoritative (expr/codegen_expr_deref_field.rs `wider_ref_target_read`); the
// memory lane read the bytes past the field from a cell no store wrote, a
// certified false counterexample on main (`safe_field_widen_read*`, the `QA`
// rows). After a store through a raw pointer into the local the read still
// fails closed (`*_after_raw_store`, `*_after_wide_store`, known red). A store
// of the referent's own size at a nonzero offset from it is a wider store too
// (`bug_wide_store_last_elem`).

#![allow(invalid_reference_casting)]
#![allow(clippy::all)]

#[repr(C)]
struct P {
    a: u16,
    b: u16,
}

#[repr(C)]
struct Q {
    x: u32,
    y: u32,
}

#[repr(C, align(8))]
struct S {
    a: u32,
    b: u32,
}

fn store_wide(p: *mut u16) {
    unsafe { *(p as *mut u32) = 1 };
}

#[kani::proof]
fn bug_wide_store_u32_as_u64() {
    let mut x: u32 = 0;
    let y: u32 = 9;
    unsafe { *(&mut x as *mut u32 as *mut u64) = 1 };
    assert!(y == 9);
}

#[kani::proof]
fn bug_wide_store_u8_as_u16() {
    let mut x: u8 = 0;
    unsafe { *(&mut x as *mut u8 as *mut u16) = 1 };
    assert!(x == x);
}

#[kani::proof]
fn bug_wide_store_last_elem() {
    let mut a = [0u32; 2];
    unsafe { *(a.as_mut_ptr().add(1) as *mut u64) = 1 };
    assert!(a[0] == 0);
}

#[kani::proof]
fn bug_wide_store_heap() {
    let mut b = Box::new(0u32);
    unsafe { *(&mut *b as *mut u32 as *mut u64) = 1 };
    assert!(*b == *b);
}

#[kani::proof]
fn bug_wide_write_unaligned() {
    let mut x: u32 = 5;
    unsafe { core::ptr::write_unaligned(&mut x as *mut u32 as *mut u64, 7) };
    assert!(x == x);
}

#[kani::proof]
fn bug_wide_store_struct_u64() {
    let mut s = P { a: 1, b: 2 };
    unsafe { *(&mut s as *mut P as *mut u64) = 3 };
    assert!(s.a == s.a);
}

#[kani::proof]
fn safe_exact_store_struct_u32() {
    let mut s = P { a: 1, b: 2 };
    unsafe { *(&mut s as *mut P as *mut u32) = 0x0004_0003 };
    assert!(s.a == 3 && s.b == 4);
}

#[kani::proof]
#[kani::should_panic]
fn sp_exact_store_struct_u32() {
    let mut s = P { a: 1, b: 2 };
    unsafe { *(&mut s as *mut P as *mut u32) = 0x0004_0003 };
    assert!(s.a == 3 && s.b == 4);
}

#[kani::proof]
fn bug_wide_store_u32_as_u64_then_read() {
    let mut x: u32 = 0;
    unsafe { *(&mut x as *mut u32 as *mut u64) = 0x1_0000_0002 };
    assert!(x == 2);
}

#[kani::proof]
fn safe_field_widen_store_crosses() {
    let mut s = P { a: 1, b: 2 };
    unsafe { *(&mut s.a as *mut u16 as *mut u32) = 0x0007_0005 };
    assert!(s.a == 5 && s.b == 7);
}

#[kani::proof]
#[kani::should_panic]
fn sp_field_widen_store_crosses() {
    let mut s = P { a: 1, b: 2 };
    unsafe { *(&mut s.a as *mut u16 as *mut u32) = 0x0007_0005 };
    assert!(s.a == 5 && s.b == 7);
}

#[kani::proof]
fn bug_field_widen_store_crosses_b_kept() {
    let mut s = P { a: 1, b: 2 };
    unsafe { *(&mut s.a as *mut u16 as *mut u32) = 0x0007_0005 };
    assert!(s.b == 2);
}

#[kani::proof]
fn bug_field_widen_store_oob() {
    let mut s = P { a: 1, b: 2 };
    unsafe { *(&mut s.b as *mut u16 as *mut u32) = 0x0007_0005 };
    assert!(s.a == s.a);
}

#[kani::proof]
fn bug_byte_array_wide_store_oob() {
    let mut a = [0u8; 4];
    unsafe { *(a.as_mut_ptr() as *mut u64) = 1 };
    assert!(a[0] == a[0]);
}

#[kani::proof]
fn safe_byte_array_exact_store() {
    let mut a = [0u8; 4];
    unsafe { *(a.as_mut_ptr() as *mut u32) = 0x0403_0201 };
    assert!(a == [1, 2, 3, 4]);
}

#[kani::proof]
#[kani::should_panic]
fn sp_byte_array_exact_store() {
    let mut a = [0u8; 4];
    unsafe { *(a.as_mut_ptr() as *mut u32) = 0x0403_0201 };
    assert!(a == [1, 2, 3, 4]);
}

#[kani::proof]
fn bug_wide_store_two_locals() {
    let mut x: u32 = 0;
    let mut y: u32 = 9;
    let py = &mut y as *mut u32;
    unsafe { *(&mut x as *mut u32 as *mut u64) = 0xFFFF_FFFF_FFFF_FFFF };
    unsafe { *py = 10 };
    assert!(y == 10);
}

#[kani::proof]
fn bug_wide_store_read_back() {
    let mut x: u32 = 0;
    let p = &mut x as *mut u32 as *mut u64;
    unsafe { *p = 0x1_0000_0002 };
    let v = unsafe { *p };
    assert!(v == 0x1_0000_0002);
}

#[kani::proof]
fn bug_wide_store_in_helper() {
    let mut x: u16 = 0;
    store_wide(&mut x);
    assert!(x == x);
}

#[kani::proof]
fn safe_field_widen_store_u64() {
    let mut s = Q { x: 1, y: 2 };
    unsafe { *(&mut s.x as *mut u32 as *mut u64) = 0x0000_0009_0000_0008 };
    assert!(s.x == 8 && s.y == 9);
}

#[kani::proof]
#[kani::should_panic]
fn sp_field_widen_store_u64() {
    let mut s = Q { x: 1, y: 2 };
    unsafe { *(&mut s.x as *mut u32 as *mut u64) = 0x0000_0009_0000_0008 };
    assert!(s.x == 8 && s.y == 9);
}

#[kani::proof]
fn bug_field_widen_store_u64_y_kept() {
    let mut s = Q { x: 1, y: 2 };
    unsafe { *(&mut s.x as *mut u32 as *mut u64) = 0x0000_0009_0000_0008 };
    assert!(s.y == 2);
}

#[kani::proof]
fn bug_wide_store_reach() {
    let mut x: u32 = 0;
    unsafe { *(&mut x as *mut u32 as *mut u64) = 1 };
    assert!(false);
}

#[kani::proof]
fn bug_scalar_wide_store_oob() { let mut x: u32 = 0; let y: u32 = 9; unsafe { *(&mut x as *mut u32 as *mut u64) = 1 }; assert!(y == 9); }

#[kani::proof]
fn bug_struct_wide_store_oob() { let mut s = S { a: 0, b: 0 }; unsafe { *(&mut s as *mut S as *mut u128) = 1 }; assert!(s.b == 0); }

#[kani::proof]
fn safe_narrow_store_struct() { let mut s = S { a: 0xAAAA_AAAA, b: 7 }; unsafe { *(&mut s as *mut S as *mut u16) = 5 }; assert!(s.a == 0xAAAA_0005 && s.b == 7); }

#[kani::proof]
#[kani::should_panic]
fn sp_narrow_store_struct() { let mut s = S { a: 0xAAAA_AAAA, b: 7 }; unsafe { *(&mut s as *mut S as *mut u16) = 5 }; assert!(s.a == 0xAAAA_0005 && s.b == 7); }

#[kani::proof]
fn bug_narrow_store_struct() { let mut s = S { a: 0xAAAA_AAAA, b: 7 }; unsafe { *(&mut s as *mut S as *mut u16) = 5 }; assert!(s.a == 5); }

#[kani::proof]
fn safe_partial_store_scalar() { let mut x: u64 = 0xAAAA_AAAA_AAAA_AAAA; unsafe { *(&mut x as *mut u64 as *mut u32) = 5 }; assert!(x == 0xAAAA_AAAA_0000_0005); }

#[kani::proof]
#[kani::should_panic]
fn sp_partial_store_scalar() { let mut x: u64 = 0xAAAA_AAAA_AAAA_AAAA; unsafe { *(&mut x as *mut u64 as *mut u32) = 5 }; assert!(x == 0xAAAA_AAAA_0000_0005); }

#[kani::proof]
fn bug_partial_store_scalar() { let mut x: u64 = 0xAAAA_AAAA_AAAA_AAAA; unsafe { *(&mut x as *mut u64 as *mut u32) = 5 }; assert!(x == 5); }

#[kani::proof]
fn bug_wide_store_symbolic_ptr_field() {
    let mut x: u32 = 0;
    let p = &mut x as *mut u32;
    let q = p as *mut u64;
    unsafe { q.write(1) };
    assert!(x == x);
}

#[kani::proof]
fn bug_wide_read_u32_as_u64() {
    let x: u32 = 5;
    let v = unsafe { *(&x as *const u32 as *const u64) };
    assert!(v == v);
}

#[kani::proof]
fn bug_wide_read_u8_as_u32() {
    let x: u8 = 5;
    let v = unsafe { *(&x as *const u8 as *const u32) };
    assert!(v == v);
}

#[kani::proof]
fn bug_wide_read_unaligned() {
    let x: u32 = 5;
    let v = unsafe { core::ptr::read_unaligned(&x as *const u32 as *const u64) };
    assert!(v == v);
}

#[kani::proof]
fn safe_field_widen_read() {
    let s = P { a: 5, b: 7 };
    let v = unsafe { *(&s.a as *const u16 as *const u32) };
    assert!(v == 0x0007_0005);
}

#[kani::proof]
fn bug_field_widen_read() {
    let s = P { a: 5, b: 7 };
    let v = unsafe { *(&s.a as *const u16 as *const u32) };
    assert!(v == 5);
}

#[kani::proof]
fn safe_field_widen_read_u64() {
    let s = Q { x: 1, y: 2 };
    let v = unsafe { *(&s.x as *const u32 as *const u64) };
    assert!(v == 0x0000_0002_0000_0001);
}

#[kani::proof]
fn bug_field_widen_read_u64() {
    let s = Q { x: 1, y: 2 };
    let v = unsafe { *(&s.x as *const u32 as *const u64) };
    assert!(v == 1);
}

#[kani::proof]
fn bug_field_widen_read_oob() {
    let s = Q { x: 1, y: 2 };
    let v = unsafe { *(&s.y as *const u32 as *const u64) };
    assert!(v == v);
}

#[repr(C, align(8))]
struct QA {
    x: u16,
    y: u16,
    z: u16,
    w: u16,
}

#[kani::proof]
fn safe_array_same_size_store_at_start() {
    let mut a = [0u32; 2];
    unsafe { *(a.as_mut_ptr() as *mut u64) = 0x0000_0002_0000_0001 };
    assert!(a[0] == 1 && a[1] == 2);
}

#[kani::proof]
#[kani::should_panic]
fn sp_array_same_size_store_at_start() {
    let mut a = [0u32; 2];
    unsafe { *(a.as_mut_ptr() as *mut u64) = 0x0000_0002_0000_0001 };
    assert!(a[0] == 1 && a[1] == 2);
}

#[kani::proof]
fn bug_array_same_size_store_at_start() {
    let mut a = [0u32; 2];
    unsafe { *(a.as_mut_ptr() as *mut u64) = 0x0000_0002_0000_0001 };
    assert!(a[0] == 2);
}

#[kani::proof]
fn safe_field_widen_read_upper() {
    let s = QA { x: 1, y: 2, z: 3, w: 4 };
    let v = unsafe { *(&s.z as *const u16 as *const u32) };
    assert!(v == 0x0004_0003);
}

#[kani::proof]
#[kani::should_panic]
fn sp_field_widen_read_upper() {
    let s = QA { x: 1, y: 2, z: 3, w: 4 };
    let v = unsafe { *(&s.z as *const u16 as *const u32) };
    assert!(v == 0x0004_0003);
}

#[kani::proof]
fn bug_field_widen_read_upper() {
    let s = QA { x: 1, y: 2, z: 3, w: 4 };
    let v = unsafe { *(&s.z as *const u16 as *const u32) };
    assert!(v == 3);
}

#[kani::proof]
fn safe_field_widen_read_whole() {
    let s = QA { x: 1, y: 2, z: 3, w: 4 };
    let v = unsafe { *(&s.x as *const u16 as *const u64) };
    assert!(v == 0x0004_0003_0002_0001);
}

#[kani::proof]
#[kani::should_panic]
fn sp_field_widen_read_whole() {
    let s = QA { x: 1, y: 2, z: 3, w: 4 };
    let v = unsafe { *(&s.x as *const u16 as *const u64) };
    assert!(v == 0x0004_0003_0002_0001);
}

#[kani::proof]
fn bug_field_widen_read_whole() {
    let s = QA { x: 1, y: 2, z: 3, w: 4 };
    let v = unsafe { *(&s.x as *const u16 as *const u64) };
    assert!(v == 1);
}

#[kani::proof]
fn safe_field_widen_read_symbolic() {
    let s = QA { x: kani::any(), y: kani::any(), z: kani::any(), w: kani::any() };
    let v = unsafe { *(&s.z as *const u16 as *const u32) };
    assert!(v == (s.z as u32) | ((s.w as u32) << 16));
}

#[kani::proof]
#[kani::should_panic]
fn sp_field_widen_read_symbolic() {
    let s = QA { x: kani::any(), y: kani::any(), z: kani::any(), w: kani::any() };
    let v = unsafe { *(&s.z as *const u16 as *const u32) };
    assert!(v == (s.z as u32) | ((s.w as u32) << 16));
}

#[kani::proof]
fn bug_field_widen_read_symbolic() {
    let s = QA { x: kani::any(), y: kani::any(), z: kani::any(), w: kani::any() };
    let v = unsafe { *(&s.z as *const u16 as *const u32) };
    assert!(v == (s.z as u32) | ((s.y as u32) << 16));
}

#[kani::proof]
fn safe_field_widen_read_after_store() {
    let mut s = QA { x: 1, y: 2, z: 3, w: 4 };
    s.w = 9;
    let v = unsafe { *(&s.z as *const u16 as *const u32) };
    assert!(v == 0x0009_0003);
}

#[kani::proof]
#[kani::should_panic]
fn sp_field_widen_read_after_store() {
    let mut s = QA { x: 1, y: 2, z: 3, w: 4 };
    s.w = 9;
    let v = unsafe { *(&s.z as *const u16 as *const u32) };
    assert!(v == 0x0009_0003);
}

#[kani::proof]
fn bug_field_widen_read_after_store_stale() {
    let mut s = QA { x: 1, y: 2, z: 3, w: 4 };
    s.w = 9;
    let v = unsafe { *(&s.z as *const u16 as *const u32) };
    assert!(v == 0x0004_0003);
}

#[kani::proof]
fn safe_field_widen_read_after_raw_store() {
    let mut s = QA { x: 1, y: 2, z: 3, w: 4 };
    let p = &mut s.w as *mut u16;
    unsafe { *p = 9 };
    let v = unsafe { *(&s.z as *const u16 as *const u32) };
    assert!(v == 0x0009_0003);
}

#[kani::proof]
fn bug_field_widen_read_after_raw_store_stale() {
    let mut s = QA { x: 1, y: 2, z: 3, w: 4 };
    let p = &mut s.w as *mut u16;
    unsafe { *p = 9 };
    let v = unsafe { *(&s.z as *const u16 as *const u32) };
    assert!(v == 0x0004_0003);
}

#[kani::proof]
fn safe_field_widen_read_after_wide_store() {
    let mut s = QA { x: 1, y: 2, z: 3, w: 4 };
    unsafe { *(&mut s.z as *mut u16 as *mut u32) = 0x0007_0006 };
    let v = unsafe { *(&s.x as *const u16 as *const u64) };
    assert!(v == 0x0007_0006_0002_0001);
}

#[kani::proof]
fn bug_field_widen_read_after_wide_store() {
    let mut s = QA { x: 1, y: 2, z: 3, w: 4 };
    unsafe { *(&mut s.z as *mut u16 as *mut u32) = 0x0007_0006 };
    let v = unsafe { *(&s.x as *const u16 as *const u64) };
    assert!(v == 0x0004_0003_0002_0001);
}

#[kani::proof]
fn bug_field_widen_read_past_end_misaligned() {
    let s = QA { x: 1, y: 2, z: 3, w: 4 };
    let v = unsafe { *(&s.z as *const u16 as *const u64) };
    assert!(v == v);
}
