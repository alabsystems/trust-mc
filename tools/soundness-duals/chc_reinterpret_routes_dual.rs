// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS, every `safe_` harness is SUCCESSFUL, and every `sp_`
// harness (`#[kani::should_panic]` over a program that never panics) FAILS.
//
// WHY THIS FILE EXISTS: reinterpreting a value's bytes by a route other than
// the transmute cast of a struct (chc_transmute_memory_order_dual.rs) or a
// union (chc_union_memory_order_dual.rs). Each shape below was measured wrong
// by the review of fix/chc-false-certificates (2026-09-27; baseline a15de6272
// and the first branch bundle alike, ay 09b0371c6, chc, 30 s):
// - a FIELD read after a pointer cast, `(*(&x as *const u128 as *const
//   Words)).hi`, resolved to `x.1: u64` (a field projection carries its own
//   type, so the cast was invisible) and read the u128 register's field 1 as
//   the LOW half: bug_ptr_cast_field_read SUCCESSFUL (missed bug),
//   safe_ptr_cast_field_read FAILED certified Genuine;
// - a store through a cast pointer, `*(&mut w as *mut Words as *mut u128) =
//   v`, left the struct's fields stale (safe_ptr_cast_write_through FAILED
//   certified Genuine);
// - a whole-value read through a cast pointer of a MUTABLY borrowed referent
//   read a stale typed cell (safe_ptr_cast_mut_read FAILED certified Genuine);
//   the value is built from the referent's register when no write in the body
//   can reach memory around it (no store through any pointer, no `&mut`/`*mut`
//   argument to a call: the `mut_nondet`/`mut_then_direct_write` rows), and is a
//   fresh value with a booking otherwise (`mut_via_other_ref`,
//   `mut_write_via_cast_then_read`: fail closed, known-red false failures);
// - an integer transmuted to an array (`u32::to_le_bytes`, `[u16; 2]` from a
//   `u32`) mapped the bytes onto the elements in the wrong order
//   (safe_to_le_bytes FAILED certified Genuine);
// - `copy_nonoverlapping` through a pointer punned to another element type
//   counted the room checks in the array's elements, not the pointer's, and
//   copied u32 values into u64 slots (safe_punned_copy_* FAILED certified
//   Genuine; `bug_punned_copy_byte_into_element_a0` SUCCESSFUL, a missed
//   bug); a constant-count copy between integer arrays through casts of an
//   element address is now a byte splice of the two memory images;
// - `<[T]>::rotate_left` matched by name as the integer rotation is in
//   chc_slice_rotate_dual.rs.
// Under `#[kani::should_panic]` a certified counterexample is the proof, so a
// false certificate there is a false PASS; the sp_ rows pin that.
//
// ALIGNMENT: every pointer-cast read below is aligned on every execution
// (AWords has the alignment of u128, and a u64 read of a Words field is
// 8-aligned), so the rows ask only about the reinterpretation.

use std::ptr::copy_nonoverlapping;

#[repr(C)]
#[derive(Clone, Copy)]
struct Words {
    lo: u64,
    hi: u64,
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
struct AWords {
    lo: u64,
    hi: u64,
}

// ---- a field read after a pointer cast ----

#[kani::proof]
fn safe_ptr_cast_field_read() {
    let x: u128 = 1 | (7 << 64);
    let p = &x as *const u128 as *const Words;
    assert!(unsafe { (*p).hi } == 7);
}

#[kani::proof]
fn bug_ptr_cast_field_read() {
    let x: u128 = 1 | (7 << 64);
    let p = &x as *const u128 as *const Words;
    assert!(unsafe { (*p).hi } == 1);
}

// ---- a store through a pointer cast ----

#[kani::proof]
fn safe_ptr_cast_write_through() {
    let mut w = AWords { lo: 0, hi: 0 };
    let p = &mut w as *mut AWords as *mut u128;
    unsafe {
        *p = 5 | (6 << 64);
    }
    assert!(w.lo == 5 && w.hi == 6);
}

#[kani::proof]
fn bug_ptr_cast_write_through() {
    let mut w = AWords { lo: 0, hi: 0 };
    let p = &mut w as *mut AWords as *mut u128;
    unsafe {
        *p = 5 | (6 << 64);
    }
    assert!(w.hi == 0);
}

// ---- a read through a pointer cast of a mutably borrowed referent ----

#[kani::proof]
fn safe_ptr_cast_mut_read() {
    let mut w = AWords { lo: 1, hi: 0 };
    let p = &mut w as *mut AWords as *mut u128;
    assert!(unsafe { *p } == 1);
}

#[kani::proof]
fn bug_ptr_cast_mut_read() {
    let mut w = AWords { lo: 1, hi: 0 };
    let p = &mut w as *mut AWords as *mut u128;
    assert!(unsafe { *p } != 1);
}

// ---- an integer transmuted to an array ----

#[kani::proof]
fn safe_to_le_bytes() {
    let x: u32 = 0x0403_0201;
    assert!(x.to_le_bytes() == [1, 2, 3, 4]);
}

#[kani::proof]
fn bug_to_le_bytes() {
    let x: u32 = 0x0403_0201;
    assert!(x.to_le_bytes() == [4, 3, 2, 1]);
}

#[kani::proof]
fn safe_to_le_bytes_nondet() {
    let x: u16 = kani::any();
    let b = x.to_le_bytes();
    assert!(b[0] == x as u8 && b[1] == (x >> 8) as u8);
}

#[kani::proof]
fn bug_to_le_bytes_nondet() {
    let x: u16 = kani::any();
    let b = x.to_le_bytes();
    assert!(b[0] == (x >> 8) as u8);
}

#[kani::proof]
fn safe_to_be_bytes() {
    let x: u32 = 0x0403_0201;
    assert!(x.to_be_bytes() == [4, 3, 2, 1]);
}

#[kani::proof]
fn safe_transmute_to_u16_array() {
    let a: [u16; 2] = unsafe { core::mem::transmute(0x0002_0001u32) };
    assert!(a == [1, 2]);
}

#[kani::proof]
fn bug_transmute_to_u16_array() {
    let a: [u16; 2] = unsafe { core::mem::transmute(0x0002_0001u32) };
    assert!(a == [2, 1]);
}

// ---- copy_nonoverlapping through a punned pointer ----

#[kani::proof]
fn safe_punned_copy_into_wider_elements() {
    let mut a = [0u64; 3];
    let src = [5u32, 6];
    let q = &mut a[1] as *mut u64 as *mut u32;
    unsafe {
        copy_nonoverlapping(src.as_ptr(), q, 2);
    }
    assert!(a[1] == 5 | (6 << 32) && a[0] == 0 && a[2] == 0);
}

#[kani::proof]
fn bug_punned_copy_into_wider_elements() {
    let mut a = [0u64; 3];
    let src = [5u32, 6];
    let q = &mut a[1] as *mut u64 as *mut u32;
    unsafe {
        copy_nonoverlapping(src.as_ptr(), q, 2);
    }
    assert!(a[1] == 5);
}

#[kani::proof]
fn safe_punned_copy_bytes_into_element() {
    let mut a = [0u32; 3];
    let src = [1u8, 0, 0, 0];
    let q = &mut a[1] as *mut u32 as *mut u8;
    unsafe {
        copy_nonoverlapping(src.as_ptr(), q, 4);
    }
    assert!(a == [0, 1, 0]);
}

#[kani::proof]
fn safe_punned_copy_from_element_bytes() {
    let a = [0x0403_0201u32, 0x0807_0605];
    let p = &a[1] as *const u32 as *const u8;
    let mut d = [0u8; 2];
    unsafe {
        copy_nonoverlapping(p, d.as_mut_ptr(), 2);
    }
    assert!(d == [5, 6]);
}

#[kani::proof]
fn bug_punned_copy_from_element_bytes() {
    let a = [0x0403_0201u32, 0x0807_0605];
    let p = &a[1] as *const u32 as *const u8;
    let mut d = [0u8; 2];
    unsafe {
        copy_nonoverlapping(p, d.as_mut_ptr(), 2);
    }
    assert!(d == [1, 2]);
}

#[kani::proof]
fn bug_punned_copy_byte_into_element_a0() {
    let mut a = [0u32; 3];
    let src = [1u8];
    let q = &mut a[1] as *mut u32 as *mut u8;
    unsafe {
        copy_nonoverlapping(src.as_ptr(), q, 1);
    }
    assert!(a[1] == 0);
}

// ---- a pointer-cast read of a mutably borrowed referent, continued ----

#[kani::proof]
fn safe_ptr_cast_mut_nondet() {
    let lo: u64 = kani::any();
    let mut w = AWords { lo, hi: 3 };
    let p = &mut w as *mut AWords as *mut u128;
    let x = unsafe { *p };
    assert!(x as u64 == lo && (x >> 64) as u64 == 3);
}

#[kani::proof]
fn bug_ptr_cast_mut_nondet() {
    let lo: u64 = kani::any();
    let mut w = AWords { lo, hi: 3 };
    let p = &mut w as *mut AWords as *mut u128;
    let x = unsafe { *p };
    assert!((x >> 64) as u64 == lo);
}

#[kani::proof]
fn safe_ptr_cast_mut_then_direct_write() {
    let mut w = AWords { lo: 1, hi: 0 };
    let p = &mut w as *mut AWords as *mut u128;
    w.hi = 4;
    let x = unsafe { *(&w as *const AWords as *const u128) };
    let _ = p;
    assert!(x == 1 | (4 << 64));
}

#[kani::proof]
fn bug_ptr_cast_mut_then_direct_write() {
    let mut w = AWords { lo: 1, hi: 0 };
    let p = &mut w as *mut AWords as *mut u128;
    w.hi = 4;
    let x = unsafe { *(&w as *const AWords as *const u128) };
    let _ = p;
    assert!(x == 1);
}

#[kani::proof]
fn safe_ptr_cast_mut_via_other_ref() {
    let mut w = AWords { lo: 1, hi: 0 };
    {
        let q = &mut w;
        q.lo = 2;
    }
    let p = &mut w as *mut AWords as *mut u128;
    let x = unsafe { *p };
    assert!(x == 2);
}

#[kani::proof]
fn bug_ptr_cast_mut_via_other_ref() {
    let mut w = AWords { lo: 1, hi: 0 };
    {
        let q = &mut w;
        q.lo = 2;
    }
    let p = &mut w as *mut AWords as *mut u128;
    let x = unsafe { *p };
    assert!(x == 1);
}

#[kani::proof]
fn safe_ptr_cast_mut_write_via_cast_then_read() {
    let mut w = AWords { lo: 1, hi: 0 };
    let p = &mut w as *mut AWords as *mut u128;
    unsafe {
        *p = 9;
    }
    let x = unsafe { *p };
    assert!(x == 9);
}

#[kani::proof]
fn bug_ptr_cast_mut_write_via_cast_then_read() {
    let mut w = AWords { lo: 1, hi: 0 };
    let p = &mut w as *mut AWords as *mut u128;
    unsafe {
        *p = 9;
    }
    let x = unsafe { *p };
    assert!(x == 1);
}

// ---- should_panic twins: each body never panics ----

#[kani::proof]
#[kani::should_panic]
fn sp_ptr_cast_field_read() {
    let x: u128 = 1 | (7 << 64);
    let p = &x as *const u128 as *const Words;
    assert!(unsafe { (*p).hi } == 7);
}

#[kani::proof]
#[kani::should_panic]
fn sp_ptr_cast_write_through() {
    let mut w = AWords { lo: 0, hi: 0 };
    let p = &mut w as *mut AWords as *mut u128;
    unsafe {
        *p = 5 | (6 << 64);
    }
    assert!(w.lo == 5 && w.hi == 6);
}

#[kani::proof]
#[kani::should_panic]
fn sp_ptr_cast_mut_read() {
    let mut w = AWords { lo: 1, hi: 0 };
    let p = &mut w as *mut AWords as *mut u128;
    assert!(unsafe { *p } == 1);
}

#[kani::proof]
#[kani::should_panic]
fn sp_to_le_bytes() {
    let x: u32 = 0x0403_0201;
    assert!(x.to_le_bytes() == [1, 2, 3, 4]);
}

#[kani::proof]
#[kani::should_panic]
fn sp_punned_copy_into_wider_elements() {
    let mut a = [0u64; 3];
    let src = [5u32, 6];
    let q = &mut a[1] as *mut u64 as *mut u32;
    unsafe {
        copy_nonoverlapping(src.as_ptr(), q, 2);
    }
    assert!(a[1] == 5 | (6 << 32) && a[0] == 0 && a[2] == 0);
}

// ---- second review (2026-09-27): punned copies inside one array ----
//
// The byte splice of a punned `copy_nonoverlapping` returned before the
// tracked-array path emitted its same-array disjointness and room checks, so
// an overlapping punned copy (UB; Kani: `memcpy src/dst overlap`) proved clean
// and an out-of-bounds one kept no violated check of its own. Both are byte
// obligations of the punned path now.

#[kani::proof]
fn bug_punned_overlap_u16() {
    let mut a = [0x0201u16, 0x0403, 0, 0];
    let s = a.as_ptr() as *const u8;
    let d = &mut a[1] as *mut u16 as *mut u8;
    unsafe { copy_nonoverlapping(s, d, 4) };
    assert!(a[3] == 0);
}

#[kani::proof]
fn bug_punned_overlap_full_u32() {
    let mut a = [0x0403_0201u32, 0];
    let s = a.as_ptr() as *const u8;
    let d = a.as_mut_ptr() as *mut u8;
    unsafe { copy_nonoverlapping(s, d, 4) };
    assert!(a[0] == 0x0403_0201);
}

#[kani::proof]
fn bug_punned_overlap_dst_only() {
    let mut a = [0x0403_0201u32, 0];
    let s = &a[0] as *const u32 as *const u16;
    let d = &mut a[0] as *mut u32 as *mut u16;
    unsafe { copy_nonoverlapping(s, d, 2) };
    assert!(a[1] == 0);
}

#[kani::proof]
fn safe_punned_disjoint_u16() {
    let mut a = [0x0201u16, 0x0403, 0, 0];
    let s = a.as_ptr() as *const u8;
    let d = &mut a[2] as *mut u16 as *mut u8;
    unsafe { copy_nonoverlapping(s, d, 4) };
    assert!(a[2] == 0x0201 && a[3] == 0x0403);
}

#[kani::proof]
fn bug_punned_dst_elem_oob() {
    let src = [1u8; 8];
    let mut a = [0u32; 2];
    unsafe { copy_nonoverlapping(src.as_ptr(), &mut a[1] as *mut u32 as *mut u8, 8) };
    assert!(a[0] == 0);
}

#[kani::proof]
fn bug_punned_dst_oob() {
    let src = [1u8; 12];
    let mut a = [0u32; 2];
    unsafe { copy_nonoverlapping(src.as_ptr(), a.as_mut_ptr() as *mut u8, 12) };
    assert!(a[0] != 0);
}

#[kani::proof]
fn bug_punned_src_oob() {
    let src = [1u8; 4];
    let mut a = [0u32; 2];
    unsafe { copy_nonoverlapping(src.as_ptr(), a.as_mut_ptr() as *mut u8, 8) };
    assert!(a[0] != 0);
}

// ---- second review (2026-09-27): a NARROWER store through a pointer cast ----
//
// When the written type was smaller than the referent the store was mirrored
// as the same type: the narrow value replaced the whole register,
// zero-extended. A `u16` into a struct or a `u32` into a `u64` now writes the
// referent's first bytes into its memory image.

#[repr(C, align(8))]
#[derive(Clone, Copy)]
struct Pair32 {
    a: u32,
    b: u32,
}

#[kani::proof]
fn safe_ptr_cast_u16_store_into_struct() {
    let mut s = Pair32 { a: 0xAAAA_AAAA, b: 7 };
    unsafe { *(&mut s as *mut Pair32 as *mut u16) = 5 };
    assert!(s.a == 0xAAAA_0005 && s.b == 7);
}

#[kani::proof]
fn bug_ptr_cast_u16_store_into_struct() {
    let mut s = Pair32 { a: 0xAAAA_AAAA, b: 7 };
    unsafe { *(&mut s as *mut Pair32 as *mut u16) = 5 };
    assert!(s.a == 5);
}

#[kani::proof]
fn safe_ptr_cast_u32_store_into_u64() {
    let mut x: u64 = 0xAAAA_AAAA_AAAA_AAAA;
    unsafe { *(&mut x as *mut u64 as *mut u32) = 5 };
    assert!(x == 0xAAAA_AAAA_0000_0005);
}

#[kani::proof]
fn bug_ptr_cast_u32_store_into_u64() {
    let mut x: u64 = 0xAAAA_AAAA_AAAA_AAAA;
    unsafe { *(&mut x as *mut u64 as *mut u32) = 5 };
    assert!(x == 5);
}

#[kani::proof]
fn safe_ptr_cast_u32_store_into_awords() {
    let mut w = AWords { lo: 0xAAAA_AAAA_AAAA_AAAA, hi: 7 };
    unsafe { *(&mut w as *mut AWords as *mut u32) = 5 };
    assert!(w.lo == 0xAAAA_AAAA_0000_0005 && w.hi == 7);
}

#[kani::proof]
fn bug_ptr_cast_u32_store_into_awords() {
    let mut w = AWords { lo: 0xAAAA_AAAA_AAAA_AAAA, hi: 7 };
    unsafe { *(&mut w as *mut AWords as *mut u32) = 5 };
    assert!(w.lo == 5);
}

#[kani::proof]
fn safe_ptr_cast_u64_store_into_awords() {
    let mut w = AWords { lo: 0, hi: 7 };
    unsafe { *(&mut w as *mut AWords as *mut u64) = 5 };
    assert!(w.lo == 5 && w.hi == 7);
}

#[kani::proof]
#[kani::should_panic]
fn sp_punned_disjoint_u16() {
    let mut a = [0x0201u16, 0x0403, 0, 0];
    let s = a.as_ptr() as *const u8;
    let d = &mut a[2] as *mut u16 as *mut u8;
    unsafe { copy_nonoverlapping(s, d, 4) };
    assert!(a[2] == 0x0201 && a[3] == 0x0403);
}

#[kani::proof]
#[kani::should_panic]
fn sp_ptr_cast_u16_store_into_struct() {
    let mut s = Pair32 { a: 0xAAAA_AAAA, b: 7 };
    unsafe { *(&mut s as *mut Pair32 as *mut u16) = 5 };
    assert!(s.a == 0xAAAA_0005 && s.b == 7);
}

#[kani::proof]
#[kani::should_panic]
fn sp_ptr_cast_u32_store_into_u64() {
    let mut x: u64 = 0xAAAA_AAAA_AAAA_AAAA;
    unsafe { *(&mut x as *mut u64 as *mut u32) = 5 };
    assert!(x == 0xAAAA_AAAA_0000_0005);
}

// Measured precision cost (fourth review of fix/chc-false-certificates,
// 2026-09-28): a byte store into an Option<u8>'s payload through a cast pointer
// and a usize store over an Option<&u8> fail closed (the enum's image is not
// modeled: transmute_layout_fallback) where main was exact on these programs;
// main certifies Genuine false counterexamples on sibling shapes (an
// Option<u32> payload). The safe rows expect Kani's SUCCESSFUL and are known-red
// false failures (decision C7, 2026-10-14).
#[kani::proof]
fn safe_opt_u8_payload_byte_store() {
    let mut o: Option<u8> = Some(5);
    let p = &mut o as *mut Option<u8> as *mut u8;
    unsafe { *p.byte_add(1) = 9 };
    assert!(o == Some(9));
}

#[kani::proof]
fn bug_opt_u8_payload_byte_store() {
    let mut o: Option<u8> = Some(5);
    let p = &mut o as *mut Option<u8> as *mut u8;
    unsafe { *p.byte_add(1) = 9 };
    assert!(o == Some(5));
}

#[kani::proof]
fn safe_opt_ref_usize_store_none() {
    let m = 1u8;
    let mut o: Option<&u8> = Some(&m);
    unsafe { *(&mut o as *mut Option<&u8> as *mut usize) = 0 };
    assert!(o.is_none());
}

#[kani::proof]
fn bug_opt_ref_usize_store_none() {
    let m = 1u8;
    let mut o: Option<&u8> = Some(&m);
    unsafe { *(&mut o as *mut Option<&u8> as *mut usize) = 0 };
    assert!(o.is_some());
}
