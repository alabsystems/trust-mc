// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS, every `safe_` harness is SUCCESSFUL, and every `sp_`
// harness (`#[kani::should_panic]` over a program that never panics) FAILS.
//
// WHY THIS FILE EXISTS: a store or read through a CAST pointer that was moved
// by a byte step before the access. A ref target names the referent, not where
// in it the pointer points, and `byte_add` / `byte_sub` / `byte_offset` (and
// `cast::<u8>().byte_add`) inherit the whole referent without recording the
// step. The third review of fix/chc-false-certificates (2026-09-27; main
// c22e1022e and the branch bundle bb9a5efcfb57, ay 22db3bcc1, chc, 30 s)
// measured:
// - a NARROWER store spliced into the referent's FIRST bytes on the branch:
//   `*(&mut x as *mut u32 as *mut u8).byte_add(3) = 0` cleared x's low byte,
//   so bug_byte_add_u8_store SUCCESSFUL clean (main: FAILED Genuine, but only
//   because main replaced the whole register), and the safe twins FAILED
//   certified Genuine on both;
// - an ELEMENT store (`*mut u16` into a `[u16; 4]`) moved by `byte_add(2)`
//   landed on element 0 on both (bug_elem_byte_add_store a missed bug);
// - `write_volatile` through a narrower cast pointer overwrote the whole
//   referent on both (bug_write_volatile_narrow a clean proof);
// - `p.byte_add(2).read_unaligned()` read the referent's first bytes on both
//   (bug_read_unaligned_byte_add a clean proof).
// The pointer's definition chain in the body now establishes the offset
// (stmt/codegen_stmt_store/store_pointer_offset.rs): the narrow store is
// spliced at it, the element store and the copy path must agree with the
// offset metadata, and anything the chain cannot establish fails closed.
// Under `#[kani::should_panic]` a certified counterexample is the proof, so a
// false certificate there is a false PASS; the sp_ rows pin that.

#[repr(C)]
#[derive(Clone, Copy)]
struct Halves {
    a: u16,
    b: u16,
}

// ---- a narrower store at a byte offset ----

#[kani::proof]
fn safe_byte_add_u8_store() {
    let mut x: u32 = 0x1111_1111;
    let p = &mut x as *mut u32 as *mut u8;
    unsafe { *p.byte_add(3) = 0 };
    assert!(x == 0x0011_1111);
}

#[kani::proof]
fn bug_byte_add_u8_store() {
    let mut x: u32 = 0x1111_1111;
    let p = &mut x as *mut u32 as *mut u8;
    unsafe { *p.byte_add(3) = 0 };
    assert!(x == 0x1111_1100);
}

#[kani::proof]
fn safe_struct_byte_add_store() {
    let mut s = Halves { a: 0x1111, b: 0x2222 };
    let p = &mut s as *mut Halves as *mut u8;
    unsafe { *p.byte_add(2) = 0 };
    assert!(s.a == 0x1111 && s.b == 0x2200);
}

#[kani::proof]
fn bug_struct_byte_add_store() {
    let mut s = Halves { a: 0x1111, b: 0x2222 };
    let p = &mut s as *mut Halves as *mut u8;
    unsafe { *p.byte_add(2) = 0 };
    assert!(s.a == 0x1100 && s.b == 0x2222);
}

#[kani::proof]
fn safe_byte_offset_u16_store() {
    let mut x: u64 = 0;
    let p = &mut x as *mut u64 as *mut u16;
    unsafe { *p.byte_offset(2) = 0xFFFF };
    assert!(x == 0xFFFF_0000);
}

#[kani::proof]
fn bug_byte_offset_u16_store() {
    let mut x: u64 = 0;
    let p = &mut x as *mut u64 as *mut u16;
    unsafe { *p.byte_offset(2) = 0xFFFF };
    assert!(x == 0xFFFF);
}

#[kani::proof]
fn safe_byte_sub_store() {
    let mut x: u32 = 0x1111_1111;
    let p = &mut x as *mut u32 as *mut u8;
    unsafe { *p.byte_add(2).byte_sub(1) = 0 };
    assert!(x == 0x1111_0011);
}

#[kani::proof]
fn bug_byte_sub_store() {
    let mut x: u32 = 0x1111_1111;
    let p = &mut x as *mut u32 as *mut u8;
    unsafe { *p.byte_add(2).byte_sub(1) = 0 };
    assert!(x == 0x1111_1100);
}

#[kani::proof]
fn safe_cast_method_byte_add_store() {
    let mut x: u32 = 0x1111_1111;
    let p = core::ptr::addr_of_mut!(x).cast::<u8>();
    unsafe { *p.byte_add(1) = 0 };
    assert!(x == 0x1111_0011);
}

#[kani::proof]
fn bug_cast_method_byte_add_store() {
    let mut x: u32 = 0x1111_1111;
    let p = core::ptr::addr_of_mut!(x).cast::<u8>();
    unsafe { *p.byte_add(1) = 0 };
    assert!(x == 0x1111_1100);
}

#[kani::proof]
fn safe_refvar_byte_add_store() {
    let mut x: u32 = 0x1111_1111;
    let r = &mut x;
    let p = r as *mut u32 as *mut u8;
    unsafe { *p.byte_add(1) = 0 };
    assert!(x == 0x1111_0011);
}

#[kani::proof]
fn bug_refvar_byte_add_store() {
    let mut x: u32 = 0x1111_1111;
    let r = &mut x;
    let p = r as *mut u32 as *mut u8;
    unsafe { *p.byte_add(1) = 0 };
    assert!(x == 0x1111_1100);
}

#[kani::proof]
fn safe_u128_u64_hi_store() {
    let mut x: u128 = 0;
    let p = &mut x as *mut u128 as *mut u64;
    unsafe { *p.byte_add(8) = 1 };
    assert!(x == 1 << 64);
}

#[kani::proof]
fn bug_u128_u64_hi_store() {
    let mut x: u128 = 0;
    let p = &mut x as *mut u128 as *mut u64;
    unsafe { *p.byte_add(8) = 1 };
    assert!(x == 1);
}

// ---- into an array, at a byte offset ----

#[kani::proof]
fn safe_u8_byte_add_into_u16_array() {
    let mut a = [0u16; 2];
    let p = &mut a as *mut [u16; 2] as *mut u8;
    unsafe { *p.byte_add(3) = 0xFF };
    assert!(a[0] == 0 && a[1] == 0xFF00);
}

#[kani::proof]
fn bug_u8_byte_add_into_u16_array() {
    let mut a = [0u16; 2];
    let p = &mut a as *mut [u16; 2] as *mut u8;
    unsafe { *p.byte_add(3) = 0xFF };
    assert!(a[0] == 0xFF);
}

#[kani::proof]
fn safe_elem_byte_add_store() {
    let mut a = [0u16; 4];
    let p = &mut a as *mut [u16; 4] as *mut u16;
    unsafe { *p.byte_add(2) = 7 };
    assert!(a[0] == 0 && a[1] == 7);
}

#[kani::proof]
fn bug_elem_byte_add_store() {
    let mut a = [0u16; 4];
    let p = &mut a as *mut [u16; 4] as *mut u16;
    unsafe { *p.byte_add(2) = 7 };
    assert!(a[0] == 7);
}

// ---- other store and read routes ----

#[kani::proof]
fn safe_write_volatile_narrow() {
    let mut x: u32 = 0xFFFF_FFFF;
    let p = &mut x as *mut u32 as *mut u8;
    unsafe { core::ptr::write_volatile(p, 0) };
    assert!(x == 0xFFFF_FF00);
}

#[kani::proof]
fn bug_write_volatile_narrow() {
    let mut x: u32 = 0xFFFF_FFFF;
    let p = &mut x as *mut u32 as *mut u8;
    unsafe { core::ptr::write_volatile(p, 0) };
    assert!(x == 0);
}

#[kani::proof]
fn safe_read_unaligned_byte_add() {
    let x: u32 = 0x4433_2211;
    let p = &x as *const u32 as *const u8;
    assert!(unsafe { p.byte_add(2).read_unaligned() } == 0x33);
}

#[kani::proof]
fn bug_read_unaligned_byte_add() {
    let x: u32 = 0x4433_2211;
    let p = &x as *const u32 as *const u8;
    assert!(unsafe { p.byte_add(2).read_unaligned() } == 0x11);
}

// ---- should_panic twins: each body never panics ----

#[kani::proof]
#[kani::should_panic]
fn sp_byte_add_u8_store() {
    let mut x: u32 = 0x1111_1111;
    let p = &mut x as *mut u32 as *mut u8;
    unsafe { *p.byte_add(3) = 0 };
    assert!(x == 0x0011_1111);
}

#[kani::proof]
#[kani::should_panic]
fn sp_struct_byte_add_store() {
    let mut s = Halves { a: 0x1111, b: 0x2222 };
    let p = &mut s as *mut Halves as *mut u8;
    unsafe { *p.byte_add(2) = 0 };
    assert!(s.a == 0x1111 && s.b == 0x2200);
}

#[kani::proof]
#[kani::should_panic]
fn sp_byte_offset_u16_store() {
    let mut x: u64 = 0;
    let p = &mut x as *mut u64 as *mut u16;
    unsafe { *p.byte_offset(2) = 0xFFFF };
    assert!(x == 0xFFFF_0000);
}

#[kani::proof]
#[kani::should_panic]
fn sp_u8_byte_add_into_u16_array() {
    let mut a = [0u16; 2];
    let p = &mut a as *mut [u16; 2] as *mut u8;
    unsafe { *p.byte_add(3) = 0xFF };
    assert!(a[0] == 0 && a[1] == 0xFF00);
}

#[kani::proof]
#[kani::should_panic]
fn sp_elem_byte_add_store() {
    let mut a = [0u16; 4];
    let p = &mut a as *mut [u16; 4] as *mut u16;
    unsafe { *p.byte_add(2) = 7 };
    assert!(a[0] == 0 && a[1] == 7);
}

#[kani::proof]
#[kani::should_panic]
fn sp_write_volatile_narrow() {
    let mut x: u32 = 0xFFFF_FFFF;
    let p = &mut x as *mut u32 as *mut u8;
    unsafe { core::ptr::write_volatile(p, 0) };
    assert!(x == 0xFFFF_FF00);
}

// ---- copies and element stores through a pointer the chain did not follow ----
//
// Fourth review of fix/chc-false-certificates (2026-09-28), on main c22e1022e
// and the third-review branch alike:
// - a copy (read_unaligned, write_unaligned, copy_nonoverlapping) through a
//   pointer carried in a tuple or struct field or a reborrowed slot kept its
//   old route with no chain answer, and so lost the byte step:
//   bug_field_read_unaligned, bug_field_u16_read_unaligned,
//   bug_field_write_unaligned, bug_struct_write_unaligned, bug_slot_read_unaligned
//   and bug_struct_copy_nonoverlapping were clean proofs where Kani fails, and
//   safe_field_write_unaligned certified a Genuine counterexample. The chain now
//   follows a field of a local its aggregate built; a copy with no chain answer
//   leaves the tracked path, and one whose chain names an element of an array
//   of the pointee type copies that element.
// - an element store through a pointer whose offset metadata missed a byte step
//   (`p.byte_add(2).add(1)`) or a step of a pointer to another type
//   (`(p.add(1) as *mut u8).add(2) as *mut u16`) wrote the element the metadata
//   counted: bug_byte_add_then_add_store a clean proof, safe_byte_add_then_add_store
//   and safe_add_cast_add_store Genuine counterexamples; through a helper the
//   inliner left as a call, the same (bug_helper_byte_add_store). The element
//   store now requires the pointer's definition chain to confirm the metadata.

#[inline(never)]
unsafe fn put_u16_at(p: *mut u16, i: usize, v: u16) {
    unsafe { *p.add(i) = v };
}

#[inline(never)]
unsafe fn put_u32_at(p: *mut u32, i: usize, v: u32) {
    unsafe { *p.add(i) = v };
}

struct PtrBox {
    p: *mut u8,
}

#[kani::proof]
fn safe_field_read_unaligned() {
    let x: u32 = 0x1122_3344;
    let p = &x as *const u32 as *const u8;
    let s = (unsafe { p.byte_add(2) },);
    let v = unsafe { s.0.read_unaligned() };
    assert!(v == 0x22);
}

#[kani::proof]
fn bug_field_read_unaligned() {
    let x: u32 = 0x1122_3344;
    let p = &x as *const u32 as *const u8;
    let s = (unsafe { p.byte_add(2) },);
    let v = unsafe { s.0.read_unaligned() };
    assert!(v == 0x44);
}

#[kani::proof]
fn safe_field_u16_read_unaligned() {
    let x: u64 = 0x1111_2222_3333_4444;
    let p = &x as *const u64 as *const u16;
    let s = (unsafe { p.byte_add(4) },);
    let v = unsafe { s.0.read_unaligned() };
    assert!(v == 0x2222);
}

#[kani::proof]
fn bug_field_u16_read_unaligned() {
    let x: u64 = 0x1111_2222_3333_4444;
    let p = &x as *const u64 as *const u16;
    let s = (unsafe { p.byte_add(4) },);
    let v = unsafe { s.0.read_unaligned() };
    assert!(v == 0x4444);
}

#[kani::proof]
fn safe_field_write_unaligned() {
    let mut x: u32 = 0;
    let p = &mut x as *mut u32 as *mut u8;
    let s = (unsafe { p.byte_add(3) },);
    unsafe { s.0.write_unaligned(1) };
    assert!(x == 0x0100_0000);
}

#[kani::proof]
fn bug_field_write_unaligned() {
    let mut x: u32 = 0;
    let p = &mut x as *mut u32 as *mut u8;
    let s = (unsafe { p.byte_add(3) },);
    unsafe { s.0.write_unaligned(1) };
    assert!(x == 1);
}

#[kani::proof]
fn safe_struct_write_unaligned() {
    let mut x: u32 = 0;
    let p = &mut x as *mut u32 as *mut u8;
    let s = PtrBox { p: unsafe { p.byte_add(1) } };
    unsafe { s.p.write_unaligned(5) };
    assert!(x == 0x0500);
}

#[kani::proof]
fn bug_struct_write_unaligned() {
    let mut x: u32 = 0;
    let p = &mut x as *mut u32 as *mut u8;
    let s = PtrBox { p: unsafe { p.byte_add(1) } };
    unsafe { s.p.write_unaligned(5) };
    assert!(x == 5);
}

#[kani::proof]
fn safe_slot_read_unaligned() {
    let x: u32 = 0x1122_3344;
    let p = &x as *const u32 as *const u8;
    let mut slot = unsafe { p.byte_add(3) };
    let r = &mut slot;
    let q = *r;
    let v = unsafe { q.read_unaligned() };
    assert!(v == 0x11);
}

#[kani::proof]
fn bug_slot_read_unaligned() {
    let x: u32 = 0x1122_3344;
    let p = &x as *const u32 as *const u8;
    let mut slot = unsafe { p.byte_add(3) };
    let r = &mut slot;
    let q = *r;
    let v = unsafe { q.read_unaligned() };
    assert!(v == 0x44);
}

#[kani::proof]
fn safe_struct_copy_nonoverlapping() {
    let mut x: [u8; 4] = [0; 4];
    let src: [u8; 2] = [7, 8];
    let s = PtrBox { p: unsafe { x.as_mut_ptr().byte_add(2) } };
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), s.p, 2) };
    assert!(x == [0, 0, 7, 8]);
}

#[kani::proof]
fn bug_struct_copy_nonoverlapping() {
    let mut x: [u8; 4] = [0; 4];
    let src: [u8; 2] = [7, 8];
    let s = PtrBox { p: unsafe { x.as_mut_ptr().byte_add(2) } };
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), s.p, 2) };
    assert!(x[0] == 7);
}

#[kani::proof]
fn safe_byte_add_then_add_store() {
    let mut a = [0u16; 4];
    let p = a.as_mut_ptr();
    unsafe { *p.byte_add(2).add(1) = 7 };
    assert!(a[2] == 7 && a[1] == 0);
}

#[kani::proof]
fn bug_byte_add_then_add_store() {
    let mut a = [0u16; 4];
    let p = a.as_mut_ptr();
    unsafe { *p.byte_add(2).add(1) = 7 };
    assert!(a[1] == 7);
}

#[kani::proof]
fn safe_add_cast_add_store() {
    let mut a = [0u16; 4];
    let p = a.as_mut_ptr();
    let q = unsafe { p.add(1) } as *mut u8;
    unsafe { *(q.add(2) as *mut u16) = 7 };
    assert!(a[2] == 7 && a[1] == 0);
}

#[kani::proof]
fn bug_add_cast_add_store() {
    let mut a = [0u16; 4];
    let p = a.as_mut_ptr();
    let q = unsafe { p.add(1) } as *mut u8;
    unsafe { *(q.add(2) as *mut u16) = 7 };
    assert!(a[1] == 7);
}

#[kani::proof]
fn safe_helper_byte_add_store() {
    let mut a = [0u16; 4];
    unsafe { put_u16_at(a.as_mut_ptr().byte_add(2), 1, 9) };
    assert!(a[2] == 9 && a[1] == 0);
}

#[kani::proof]
fn bug_helper_byte_add_store() {
    let mut a = [0u16; 4];
    unsafe { put_u16_at(a.as_mut_ptr().byte_add(2), 1, 9) };
    assert!(a[1] == 9);
}

#[kani::proof]
fn safe_helper_add_store() {
    let mut a = [0u32; 4];
    unsafe { put_u32_at(a.as_mut_ptr(), 2, 9) };
    assert!(a[2] == 9 && a[1] == 0);
}

#[kani::proof]
fn bug_helper_add_store() {
    let mut a = [0u32; 4];
    unsafe { put_u32_at(a.as_mut_ptr(), 2, 9) };
    assert!(a[1] == 9);
}

#[kani::proof]
fn safe_read_byte_add_then_add() {
    let a = [1u16, 2, 3, 4];
    let p = a.as_ptr();
    let v = unsafe { *p.byte_add(2).add(1) };
    assert!(v == 3);
}

#[kani::proof]
fn bug_read_byte_add_then_add() {
    let a = [1u16, 2, 3, 4];
    let p = a.as_ptr();
    let v = unsafe { *p.byte_add(2).add(1) };
    assert!(v == 2);
}

#[kani::proof]
#[kani::should_panic]
fn sp_field_read_unaligned() {
    let x: u32 = 0x1122_3344;
    let p = &x as *const u32 as *const u8;
    let s = (unsafe { p.byte_add(2) },);
    let v = unsafe { s.0.read_unaligned() };
    assert!(v == 0x22);
}

#[kani::proof]
#[kani::should_panic]
fn sp_field_write_unaligned() {
    let mut x: u32 = 0;
    let p = &mut x as *mut u32 as *mut u8;
    let s = (unsafe { p.byte_add(3) },);
    unsafe { s.0.write_unaligned(1) };
    assert!(x == 0x0100_0000);
}

#[kani::proof]
#[kani::should_panic]
fn sp_struct_copy_nonoverlapping() {
    let mut x: [u8; 4] = [0; 4];
    let src: [u8; 2] = [7, 8];
    let s = PtrBox { p: unsafe { x.as_mut_ptr().byte_add(2) } };
    unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), s.p, 2) };
    assert!(x == [0, 0, 7, 8]);
}

#[kani::proof]
#[kani::should_panic]
fn sp_byte_add_then_add_store() {
    let mut a = [0u16; 4];
    let p = a.as_mut_ptr();
    unsafe { *p.byte_add(2).add(1) = 7 };
    assert!(a[2] == 7 && a[1] == 0);
}

#[kani::proof]
#[kani::should_panic]
fn sp_add_cast_add_store() {
    let mut a = [0u16; 4];
    let p = a.as_mut_ptr();
    let q = unsafe { p.add(1) } as *mut u8;
    unsafe { *(q.add(2) as *mut u16) = 7 };
    assert!(a[2] == 7 && a[1] == 0);
}

#[kani::proof]
#[kani::should_panic]
fn sp_helper_byte_add_store() {
    let mut a = [0u16; 4];
    unsafe { put_u16_at(a.as_mut_ptr().byte_add(2), 1, 9) };
    assert!(a[2] == 9 && a[1] == 0);
}
