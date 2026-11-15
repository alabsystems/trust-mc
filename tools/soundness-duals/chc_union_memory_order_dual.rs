// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS, every `safe_` harness is SUCCESSFUL, and every `sp_`
// harness (`#[kani::should_panic]` over a program that never panics) FAILS.
//
// WHY THIS FILE EXISTS: a union is one bitvector of its size and every field
// sits at offset 0, so writing a field writes its bytes into the low end and
// reading a field reads them back as the field's type, in MEMORY order. The
// write direction of chc_aggregate_reinterpret_dual.rs was fixed first, with
// values below bit 64 only. The review of fix/chc-false-certificates
// (2026-09-27) found every other route wrong on the baseline a15de6272 and on
// the first branch bundle alike (ay 09b0371c6, chc, 30 s):
// - a READ of a struct field out of a union went through type-blind
//   selectors: a 128-bit container is read as `Layout { size, align }` (field
//   0 the high half, field 1 the low half) and a 64-bit one as a pointer
//   wrapper (field 0 the whole value), so `u.w` of `U { x: v }` put `v`'s high
//   word into `lo` and never defined `hi` (bug_read_words_lo SUCCESSFUL, a
//   missed bug; safe_read_words FAILED certified Genuine);
// - `u.x` of a 128-bit union kept only the low 64 bits (bug_write_hi_only);
// - `u.w.hi` extracted the low 64 bits (bug_read_nested_field);
// - `u.q.b = 1` wrote the whole union (bug_subfield_write);
// - a narrow field write zeroed the union's tail (bug_narrow_write);
// - a union aggregate zero-extended its field, so the uninitialized tail read
//   as zero (bug_tail_uninit_read_as_zero; Kani reads uninitialized bytes as
//   any value);
// - the aggregate wrote the FIRST declared field's type whatever field the
//   aggregate names;
// - a newtype field (`Wrap(u32)`, repr(transparent), a PhantomData second
//   field, a nested newtype) became a fresh union on the first branch bundle.
// Under `#[kani::should_panic]` a certified counterexample is the proof, so the
// false certificates were false PASSES (sp_ rows SUCCESSFUL where Kani fails).
// Fixed by codegen_stmt_union_bits.rs: every route builds the field's value
// from its MIR layout, or a fresh value with a booking.

use std::marker::PhantomData;

#[repr(C)]
#[derive(Clone, Copy)]
struct Words {
    lo: u64,
    hi: u64,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Q4 {
    a: u32,
    b: u32,
    c: u32,
    d: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Sgn {
    a: i32,
    b: i32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Small {
    a: u32,
    b: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct In {
    lo: u32,
    hi: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Nest {
    i: In,
    z: u64,
}

#[derive(Clone, Copy)]
struct Wrap(u32);

#[repr(transparent)]
#[derive(Clone, Copy)]
struct TWrap(u64);

#[derive(Clone, Copy)]
struct PWrap {
    v: u16,
    _p: PhantomData<u8>,
}

#[derive(Clone, Copy)]
struct Outer(Wrap);

#[repr(C)]
union U {
    w: Words,
    x: u128,
}

#[repr(C)]
union UQ4 {
    q: Q4,
    x: u128,
}

#[repr(C)]
union USgn {
    s: Sgn,
    x: u64,
}

#[repr(C)]
union USmall {
    w: Small,
    x: u128,
}

#[repr(C)]
union UNest {
    n: Nest,
    x: u128,
}

#[repr(C)]
union UN {
    small: u32,
    big: u64,
}

#[repr(C)]
union UB {
    b: [u8; 8],
    w: u64,
}

#[repr(C)]
union UBool {
    f: bool,
    n: u8,
}

#[repr(C)]
union UWrap {
    w: Wrap,
    x: u32,
}

#[repr(C)]
union UTWrap {
    t: TWrap,
    x: u64,
}

#[repr(C)]
union UPWrap {
    p: PWrap,
    x: u16,
}

#[repr(C)]
union UOuter {
    o: Outer,
    x: u32,
}

fn read_hi(u: &U) -> u64 {
    unsafe { u.w.hi }
}

// ---- reading a struct field out of the union's bits ----

#[kani::proof]
fn safe_read_words() {
    let u = U { x: 1 | (7 << 64) };
    let w = unsafe { u.w };
    assert!(w.lo == 1 && w.hi == 7);
}

#[kani::proof]
fn bug_read_words_lo() {
    let u = U { x: 1 | (7 << 64) };
    let w = unsafe { u.w };
    assert!(w.lo == 7);
}

#[kani::proof]
fn safe_read_words_nondet() {
    let v: u128 = kani::any();
    let u = U { x: v };
    let w = unsafe { u.w };
    assert!(w.lo == v as u64 && w.hi == (v >> 64) as u64);
}

#[kani::proof]
fn bug_read_words_nondet() {
    let v: u128 = kani::any();
    let u = U { x: v };
    let w = unsafe { u.w };
    assert!(w.lo == (v >> 64) as u64);
}

#[kani::proof]
fn safe_read_nested_field() {
    let u = U { x: 1 | (7 << 64) };
    assert!(unsafe { u.w.hi } == 7);
}

#[kani::proof]
fn bug_read_nested_field() {
    let u = U { x: 1 | (7 << 64) };
    assert!(unsafe { u.w.hi } == 1);
}

#[kani::proof]
fn safe_read_signed_fields() {
    let u = USgn { x: 0x0000_0002_ffff_fffe };
    let s = unsafe { u.s };
    assert!(s.a == -2 && s.b == 2);
}

#[kani::proof]
fn bug_read_signed_fields() {
    let u = USgn { x: 0x0000_0002_ffff_fffe };
    let s = unsafe { u.s };
    assert!(s.a == 2);
}

#[kani::proof]
fn safe_read_nested_struct() {
    let u = UNest { x: 1 | (2 << 32) | (3 << 64) };
    let n = unsafe { u.n };
    assert!(n.i.lo == 1 && n.i.hi == 2 && n.z == 3);
}

#[kani::proof]
fn bug_read_nested_struct() {
    let u = UNest { x: 1 | (2 << 32) | (3 << 64) };
    let n = unsafe { u.n };
    assert!(n.i.lo == 3);
}

#[kani::proof]
fn safe_read_through_reference() {
    let u = U { x: 1 | (7 << 64) };
    assert!(read_hi(&u) == 7);
}

#[kani::proof]
fn bug_read_through_reference() {
    let u = U { x: 1 | (7 << 64) };
    assert!(read_hi(&u) == 1);
}

#[kani::proof]
fn safe_read_array_element() {
    let i: usize = kani::any();
    kani::assume(i < 8);
    let u = UB { w: 0x0807_0605_0403_0201 };
    assert!(unsafe { u.b[i] } as usize == i + 1);
}

#[kani::proof]
fn bug_read_array_element() {
    let i: usize = kani::any();
    kani::assume(i < 8);
    let u = UB { w: 0x0807_0605_0403_0201 };
    assert!(unsafe { u.b[i] } as usize != 8);
}

#[kani::proof]
fn safe_read_bool() {
    let u = UBool { n: 1 };
    assert!(unsafe { u.f });
}

#[kani::proof]
fn bug_read_bool() {
    let u = UBool { n: 0 };
    assert!(unsafe { u.f });
}

// ---- writing a field, read back through another ----

#[kani::proof]
fn safe_write_high_word() {
    let u = U { w: Words { lo: 1, hi: 7 } };
    assert!(unsafe { u.x } == 1 | (7 << 64));
}

#[kani::proof]
fn bug_write_hi_only() {
    let u = U { w: Words { lo: 0, hi: 7 } };
    assert!(unsafe { u.x } >> 64 == 0);
}

#[kani::proof]
fn safe_write_four_fields() {
    let u = UQ4 { q: Q4 { a: 1, b: 2, c: 3, d: 4 } };
    assert!(unsafe { u.x } == 1 | (2 << 32) | (3 << 64) | (4 << 96));
}

#[kani::proof]
fn bug_write_four_fields() {
    let u = UQ4 { q: Q4 { a: 1, b: 2, c: 3, d: 4 } };
    assert!(unsafe { u.x } == 4 | (3 << 32) | (2 << 64) | (1 << 96));
}

#[kani::proof]
fn safe_write_nondet_fields() {
    let a: u32 = kani::any();
    let d: u32 = kani::any();
    let u = UQ4 { q: Q4 { a, b: 0, c: 0, d } };
    let x = unsafe { u.x };
    assert!(x as u32 == a && (x >> 96) as u32 == d);
}

#[kani::proof]
fn bug_write_nondet_fields() {
    let a: u32 = kani::any();
    let d: u32 = kani::any();
    let u = UQ4 { q: Q4 { a, b: 0, c: 0, d } };
    assert!((unsafe { u.x } >> 96) as u32 == a);
}

#[kani::proof]
fn safe_write_bool() {
    let u = UBool { f: true };
    assert!(unsafe { u.n } == 1);
}

#[kani::proof]
fn bug_write_bool() {
    let u = UBool { f: true };
    assert!(unsafe { u.n } == 0);
}

#[kani::proof]
fn safe_subfield_write() {
    let mut u = U { x: 1 | (7 << 64) };
    u.w.hi = 9;
    assert!(unsafe { u.x } == 1 | (9 << 64));
}

#[kani::proof]
fn bug_subfield_write() {
    let mut u = U { x: 1 | (7 << 64) };
    u.w.hi = 9;
    assert!(unsafe { u.w.lo } == 9);
}

#[kani::proof]
fn safe_narrow_write() {
    let mut u = UN { big: u64::MAX };
    u.small = 5;
    assert!(unsafe { u.big } == 0xffff_ffff_0000_0005);
}

#[kani::proof]
fn bug_narrow_write() {
    let mut u = UN { big: u64::MAX };
    u.small = 5;
    assert!(unsafe { u.big } == 5);
}

#[kani::proof]
fn safe_small_field_low_bytes() {
    let u = USmall { w: Small { a: 1, b: 2 } };
    assert!(unsafe { u.x } as u64 == 1 | (2 << 32));
}

/// The bytes past the written field are uninitialized: Kani reads them as any
/// value, so claiming they are zero fails.
#[kani::proof]
fn bug_tail_uninit_read_as_zero() {
    let u = USmall { w: Small { a: 1, b: 2 } };
    assert!(unsafe { u.x } >> 64 == 0);
}

#[kani::proof]
fn safe_round_trip() {
    let v: u128 = kani::any();
    let u = U { x: v };
    let w = unsafe { u.w };
    let u2 = U { w };
    assert!(unsafe { u2.x } == v);
}

#[kani::proof]
fn bug_round_trip_swapped() {
    let v: u128 = kani::any();
    let u = U { x: v };
    let w = unsafe { u.w };
    let u2 = U { w: Words { lo: w.hi, hi: w.lo } };
    assert!(unsafe { u2.x } == v);
}

// ---- newtype fields ----

#[kani::proof]
fn safe_newtype_field() {
    let v: u32 = kani::any();
    let u = UWrap { w: Wrap(v) };
    assert!(unsafe { u.x } == v);
}

#[kani::proof]
fn bug_newtype_field() {
    let u = UWrap { w: Wrap(9) };
    assert!(unsafe { u.x } == 8);
}

#[kani::proof]
fn safe_transparent_newtype_field() {
    let u = UTWrap { t: TWrap(0x1234) };
    assert!(unsafe { u.x } == 0x1234);
}

#[kani::proof]
fn bug_transparent_newtype_field() {
    let u = UTWrap { t: TWrap(0x1234) };
    assert!(unsafe { u.x } == 0x3412);
}

#[kani::proof]
fn safe_phantom_newtype_field() {
    let u = UPWrap { p: PWrap { v: 5, _p: PhantomData } };
    assert!(unsafe { u.x } == 5);
}

#[kani::proof]
fn bug_phantom_newtype_field() {
    let u = UPWrap { p: PWrap { v: 5, _p: PhantomData } };
    assert!(unsafe { u.x } == 6);
}

#[kani::proof]
fn safe_nested_newtype_field() {
    let u = UOuter { o: Outer(Wrap(3)) };
    assert!(unsafe { u.x } == 3);
}

#[kani::proof]
fn bug_nested_newtype_field() {
    let u = UOuter { o: Outer(Wrap(3)) };
    assert!(unsafe { u.x } == 4);
}

#[kani::proof]
fn safe_newtype_field_read() {
    let u = UWrap { x: 9 };
    assert!(unsafe { u.w }.0 == 9);
}

// ---- should_panic twins: each body never panics ----

#[kani::proof]
#[kani::should_panic]
fn sp_read_signed_fields() {
    let u = USgn { x: 0x0000_0002_ffff_fffe };
    let s = unsafe { u.s };
    assert!(s.b == 2);
}

#[kani::proof]
#[kani::should_panic]
fn sp_read_words() {
    let u = U { x: 1 | (7 << 64) };
    let w = unsafe { u.w };
    assert!(w.lo == 1 && w.hi == 7);
}

#[kani::proof]
#[kani::should_panic]
fn sp_read_words_nondet() {
    let v: u128 = kani::any();
    let u = U { x: v };
    let w = unsafe { u.w };
    assert!(w.lo == v as u64);
}

#[kani::proof]
#[kani::should_panic]
fn sp_write_high_word() {
    let u = U { w: Words { lo: 1, hi: 7 } };
    assert!(unsafe { u.x } == 1 | (7 << 64));
}

// Stores through a pointer CAST into a union, or into a struct that holds an
// address, narrower than the referent or at a byte offset (fourth review of
// fix/chc-false-certificates, 2026-09-28). The narrow-store splice took only
// referents that hold no address; every union and every struct with a pointer
// or reference field kept the same-type mirror, which wrote the narrow value,
// zero-extended, over the whole referent and ignored the offset. On main
// c22e1022e and the third-review branch alike: bug_union_u16_store_at_2,
// bug_union_u16_store_reads_h1, bug_union_u32_store_hi_nondet,
// bug_struct_ptr_field_store_y, bug_union_ptr_u32_store_hi and
// bug_union_u16_store_at_2_reads_bytes were clean proofs where Kani fails, and
// their safe twins (and the struct-with-reference rows) certified Genuine
// counterexamples. A union's image is its bitvector, a pointer field's bytes
// are its address; the store is spliced at the chain offset or fails closed.

#[derive(Clone, Copy)]
union UH {
    w: u32,
    h: [u16; 2],
    b: [u8; 4],
}

#[derive(Clone, Copy)]
union UQ {
    q: u64,
    d: [u32; 2],
}

#[derive(Clone, Copy)]
union UPtr {
    p: *const u8,
    n: u64,
    h: [u32; 2],
}

#[repr(C)]
#[derive(Clone, Copy)]
struct SPtr {
    x: u32,
    y: u32,
    p: *const u8,
}

#[repr(C)]
struct SRef<'a> {
    r: &'a u8,
    x: u16,
    y: u16,
}

#[kani::proof]
fn safe_union_u16_store_at_2() {
    let mut u = UH { w: 0 };
    let p = &mut u as *mut UH as *mut u16;
    unsafe { *p.byte_add(2) = 3 };
    assert!(unsafe { u.h[1] } == 3 && unsafe { u.h[0] } == 0);
}

#[kani::proof]
fn bug_union_u16_store_at_2() {
    let mut u = UH { w: 0 };
    let p = &mut u as *mut UH as *mut u16;
    unsafe { *p.byte_add(2) = 3 };
    assert!(unsafe { u.h[0] } == 3);
}

#[kani::proof]
fn safe_union_u16_store_at_2_reads_bytes() {
    let mut u = UH { w: 0 };
    let p = &mut u as *mut UH as *mut u16;
    unsafe { *p.byte_add(2) = 3 };
    assert!(unsafe { u.w } == 0x0003_0000 && unsafe { u.b[2] } == 3);
}

#[kani::proof]
fn bug_union_u16_store_at_2_reads_bytes() {
    let mut u = UH { w: 0 };
    let p = &mut u as *mut UH as *mut u16;
    unsafe { *p.byte_add(2) = 3 };
    assert!(unsafe { u.b[0] } == 3);
}

#[kani::proof]
fn safe_union_u16_store_reads_h1() {
    let mut u = UH { w: 0xFFFF_FFFF };
    let p = &mut u as *mut UH as *mut u16;
    unsafe { *p = 3 };
    assert!(unsafe { u.h[1] } == 0xFFFF && unsafe { u.w } == 0xFFFF_0003);
}

#[kani::proof]
fn bug_union_u16_store_reads_h1() {
    let mut u = UH { w: 0xFFFF_FFFF };
    let p = &mut u as *mut UH as *mut u16;
    unsafe { *p = 3 };
    assert!(unsafe { u.h[1] } == 0);
}

#[kani::proof]
fn safe_union_u32_store_hi_nondet() {
    let v: u32 = kani::any();
    let mut u = UQ { q: 0 };
    let p = &mut u as *mut UQ as *mut u32;
    unsafe { *p.byte_add(4) = v };
    assert!(unsafe { u.d[1] } == v && unsafe { u.d[0] } == 0);
}

#[kani::proof]
fn bug_union_u32_store_hi_nondet() {
    let v: u32 = kani::any();
    let mut u = UQ { q: 0 };
    let p = &mut u as *mut UQ as *mut u32;
    unsafe { *p.byte_add(4) = v };
    assert!(unsafe { u.d[0] } == v || v == 0);
}

#[kani::proof]
fn safe_union_ptr_u32_store_hi() {
    let mut u = UPtr { n: 0 };
    let p = &mut u as *mut UPtr as *mut u32;
    unsafe { *p.byte_add(4) = 1 };
    assert!(unsafe { u.h[1] } == 1 && unsafe { u.h[0] } == 0);
}

#[kani::proof]
fn bug_union_ptr_u32_store_hi() {
    let mut u = UPtr { n: 0 };
    let p = &mut u as *mut UPtr as *mut u32;
    unsafe { *p.byte_add(4) = 1 };
    assert!(unsafe { u.h[0] } == 1);
}

#[kani::proof]
fn safe_struct_ptr_field_store_y() {
    let z = 0u8;
    let mut s = SPtr { x: 1, y: 2, p: &z };
    let p = &mut s as *mut SPtr as *mut u32;
    unsafe { *p.byte_add(4) = 7 };
    assert!(s.x == 1 && s.y == 7);
}

#[kani::proof]
fn bug_struct_ptr_field_store_y() {
    let z = 0u8;
    let mut s = SPtr { x: 1, y: 2, p: &z };
    let p = &mut s as *mut SPtr as *mut u32;
    unsafe { *p.byte_add(4) = 7 };
    assert!(s.x == 7 || s.y == 2);
}

#[kani::proof]
fn safe_struct_ref_field_store_x() {
    let m = 1u8;
    let mut s = SRef { r: &m, x: 1, y: 2 };
    let p = &mut s as *mut SRef as *mut u16;
    unsafe { *p.byte_add(8) = 9 };
    assert!(s.x == 9 && s.y == 2);
}

#[kani::proof]
fn bug_struct_ref_field_store_x() {
    let m = 1u8;
    let mut s = SRef { r: &m, x: 1, y: 2 };
    let p = &mut s as *mut SRef as *mut u16;
    unsafe { *p.byte_add(8) = 9 };
    assert!(s.x == 1);
}

#[kani::proof]
fn safe_struct_ref_field_store_y() {
    let m = 1u8;
    let mut s = SRef { r: &m, x: 1, y: 2 };
    let p = &mut s as *mut SRef as *mut u16;
    unsafe { *p.byte_add(10) = 9 };
    assert!(s.y == 9 && s.x == 1 && *s.r == 1);
}

#[kani::proof]
fn bug_struct_ref_field_store_y() {
    let m = 1u8;
    let mut s = SRef { r: &m, x: 1, y: 2 };
    let p = &mut s as *mut SRef as *mut u16;
    unsafe { *p.byte_add(10) = 9 };
    assert!(s.y == 2);
}

#[kani::proof]
fn safe_box_as_mut_pointee() {
    let mut b = Box::new(5u32);
    *b.as_mut() = 6;
    assert!(*b == 6);
}

#[kani::proof]
#[kani::should_panic]
fn sp_union_u16_store_at_2() {
    let mut u = UH { w: 0 };
    let p = &mut u as *mut UH as *mut u16;
    unsafe { *p.byte_add(2) = 3 };
    assert!(unsafe { u.h[1] } == 3 && unsafe { u.h[0] } == 0);
}

#[kani::proof]
#[kani::should_panic]
fn sp_union_u16_store_at_2_reads_bytes() {
    let mut u = UH { w: 0 };
    let p = &mut u as *mut UH as *mut u16;
    unsafe { *p.byte_add(2) = 3 };
    assert!(unsafe { u.w } == 0x0003_0000 && unsafe { u.b[2] } == 3);
}

#[kani::proof]
#[kani::should_panic]
fn sp_union_u16_store_reads_h1() {
    let mut u = UH { w: 0xFFFF_FFFF };
    let p = &mut u as *mut UH as *mut u16;
    unsafe { *p = 3 };
    assert!(unsafe { u.h[1] } == 0xFFFF && unsafe { u.w } == 0xFFFF_0003);
}

#[kani::proof]
#[kani::should_panic]
fn sp_union_u32_store_hi_nondet() {
    let v: u32 = kani::any();
    let mut u = UQ { q: 0 };
    let p = &mut u as *mut UQ as *mut u32;
    unsafe { *p.byte_add(4) = v };
    assert!(unsafe { u.d[1] } == v && unsafe { u.d[0] } == 0);
}

#[kani::proof]
#[kani::should_panic]
fn sp_union_ptr_u32_store_hi() {
    let mut u = UPtr { n: 0 };
    let p = &mut u as *mut UPtr as *mut u32;
    unsafe { *p.byte_add(4) = 1 };
    assert!(unsafe { u.h[1] } == 1 && unsafe { u.h[0] } == 0);
}

#[kani::proof]
#[kani::should_panic]
fn sp_struct_ptr_field_store_y() {
    let z = 0u8;
    let mut s = SPtr { x: 1, y: 2, p: &z };
    let p = &mut s as *mut SPtr as *mut u32;
    unsafe { *p.byte_add(4) = 7 };
    assert!(s.x == 1 && s.y == 7);
}

#[kani::proof]
#[kani::should_panic]
fn sp_struct_ref_field_store_x() {
    let m = 1u8;
    let mut s = SRef { r: &m, x: 1, y: 2 };
    let p = &mut s as *mut SRef as *mut u16;
    unsafe { *p.byte_add(8) = 9 };
    assert!(s.x == 9 && s.y == 2);
}

#[kani::proof]
#[kani::should_panic]
fn sp_struct_ref_field_store_y() {
    let m = 1u8;
    let mut s = SRef { r: &m, x: 1, y: 2 };
    let p = &mut s as *mut SRef as *mut u16;
    unsafe { *p.byte_add(10) = 9 };
    assert!(s.y == 9 && s.x == 1 && *s.r == 1);
}
