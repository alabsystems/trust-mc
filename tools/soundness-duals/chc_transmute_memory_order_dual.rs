// Oracle: corpus-rev Kani 4c0fce8c3, measured 2026-09-26: every `bug_` harness
// FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: a transmute between a multi-field struct and a
// bitvector (an integer, or a wide slice pointer) went through the encoder's
// internal datatype flatten, which concatenates the fields MSB-first in
// declaration order. On a little-endian target the field at offset 0 is the
// LOW end, so every two-word struct had its words transposed. Measured on
// main 25905b622 (ay 643b2851f), chc lane: every bug_ row here PROVED
// (SUCCESSFUL) and every safe_ row FAILED certified Genuine;
// fix/chc-slice-length 619f6ad86 did the same on the review's probes of these
// shapes. The slice rows put the DATA word in the length half, so `s[2]` on a
// two-element slice was proved in bounds.
// codegen_stmt_transmute_layout.rs now builds the reinterpretation from the
// MIR layout (offsets, little-endian, word roles) or writes a fresh value.

use std::mem::transmute;

#[repr(C)]
#[derive(Clone, Copy)]
struct FatPtr {
    data: *const u8,
    len: usize,
}

// A two-word struct transmuted to `&[u8]`: the word at offset 8 is the length.
#[kani::proof]
fn bug_struct_to_slice_oob() {
    let a = [1u8, 2, 3];
    let raw = FatPtr { data: a.as_ptr(), len: 2 };
    let s: &[u8] = unsafe { transmute(raw) };
    let _x = s[2];
}

#[kani::proof]
fn bug_struct_to_slice_len() {
    let a = [1u8, 2, 3];
    let raw = FatPtr { data: a.as_ptr(), len: 2 };
    let s: &[u8] = unsafe { transmute(raw) };
    assert!(s.len() != 2);
}

#[kani::proof]
fn safe_struct_to_slice_len_and_data() {
    let a = [1u8, 2, 3];
    let raw = FatPtr { data: a.as_ptr(), len: 2 };
    let s: &[u8] = unsafe { transmute(raw) };
    assert!(s.len() == 2);
    assert!(s[1] == 2);
}

// The reverse: `&[u8]` transmuted to the struct reads the length at offset 8.
#[kani::proof]
fn bug_slice_to_struct_len() {
    let a = [1u8, 2, 3];
    let s: &[u8] = &a[..2];
    let raw: FatPtr = unsafe { transmute(s) };
    assert!(raw.len != 2);
}

#[kani::proof]
fn safe_slice_to_struct_len() {
    let a = [1u8, 2, 3];
    let s: &[u8] = &a[..2];
    let raw: FatPtr = unsafe { transmute(s) };
    assert!(raw.len == 2);
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Words {
    lo: u64,
    hi: u64,
}

// Integers: the field at offset 0 is the low word.
#[kani::proof]
fn bug_struct_to_u128_low_word() {
    let x: u128 = unsafe { transmute(Words { lo: 1, hi: 0 }) };
    assert!(x != 1);
}

#[kani::proof]
fn safe_struct_to_u128_low_word() {
    let x: u128 = unsafe { transmute(Words { lo: 1, hi: 0 }) };
    assert!(x == 1);
}

#[kani::proof]
fn bug_u128_to_struct_low_word() {
    let w: Words = unsafe { transmute(1u128) };
    assert!(w.lo != 1);
}

#[kani::proof]
fn safe_u128_to_struct_low_word() {
    let w: Words = unsafe { transmute(1u128 | (7u128 << 64)) };
    assert!(w.lo == 1 && w.hi == 7);
}

// A tuple of two u32 read as a u64.
#[kani::proof]
fn bug_tuple_to_u64_low_half() {
    let x: u64 = unsafe { transmute((1u32, 0u32)) };
    assert!(x != 1);
}

#[kani::proof]
fn safe_tuple_to_u64_low_half() {
    let x: u64 = unsafe { transmute((1u32, 2u32)) };
    assert!(x == 1 | (2 << 32));
}

// The same transmutes inside a callee body.
fn slice_len_of(raw: FatPtr) -> usize {
    let s: &[u8] = unsafe { transmute(raw) };
    s.len()
}

fn words_to_u128(w: Words) -> u128 {
    unsafe { transmute(w) }
}

#[kani::proof]
fn bug_callee_struct_to_slice_len() {
    let a = [1u8, 2, 3];
    assert!(slice_len_of(FatPtr { data: a.as_ptr(), len: 2 }) != 2);
}

#[kani::proof]
fn safe_callee_struct_to_slice_len() {
    let a = [1u8, 2, 3];
    assert!(slice_len_of(FatPtr { data: a.as_ptr(), len: 2 }) == 2);
}

#[kani::proof]
fn bug_callee_struct_to_u128() {
    assert!(words_to_u128(Words { lo: 1, hi: 0 }) != 1);
}

#[kani::proof]
fn safe_callee_struct_to_u128() {
    assert!(words_to_u128(Words { lo: 1, hi: 0 }) == 1);
}

// ---- second review (2026-09-27): arrays of one SORT but another layout ----
//
// A same-sort array transmute kept the value. Every fieldless enum translates
// to a 32-bit bitvector whatever its size, and a thin pointer's 64-bit term is
// its (object, offset) identity, not its address: `[E8; 4]` to `[u32; 1]` and
// `[*const u8; 2]` to `[usize; 2]` kept the wrong value (bug rows SUCCESSFUL,
// safe rows FAILED certified Genuine on main and on the first cut). The value
// is kept only for elements of one representation (equal types, or integers,
// floats and chars of one size); the rest go through both memory images.
// `<*const T>::addr` read the identity where `as usize` reads the address.

#[derive(Clone, Copy, PartialEq, Debug)]
#[repr(u8)]
enum E8 {
    A = 1,
    B = 2,
    C = 3,
    D = 4,
}

#[derive(Clone, Copy, PartialEq, Debug)]
#[repr(u16)]
enum E16 {
    A = 1,
    B = 2,
}

#[kani::proof]
fn safe_enum8_array_to_u32_array() {
    let a = [E8::A, E8::B, E8::C, E8::D];
    let t: [u32; 1] = unsafe { transmute(a) };
    assert!(t[0] == 0x0403_0201);
}

#[kani::proof]
fn bug_enum8_array_to_u32_array() {
    let a = [E8::A, E8::B, E8::C, E8::D];
    let t: [u32; 1] = unsafe { transmute(a) };
    assert!(t[0] == 1);
}

#[kani::proof]
fn safe_u32_array_to_enum8_array() {
    let t = [0x0403_0201u32];
    let a: [E8; 4] = unsafe { transmute(t) };
    assert!(a[0] == E8::A && a[3] == E8::D);
}

#[kani::proof]
fn safe_enum16_array_to_u32_array() {
    let a = [E16::A, E16::B];
    let t: [u32; 1] = unsafe { transmute(a) };
    assert!(t[0] == 0x0002_0001);
}

#[kani::proof]
fn bug_enum16_array_to_u32_array() {
    let a = [E16::A, E16::B];
    let t: [u32; 1] = unsafe { transmute(a) };
    assert!(t[0] == 1);
}

#[kani::proof]
fn safe_ptr_array_to_usize_array() {
    let x = 5u8;
    let y = 6u8;
    let a = [&x as *const u8, &y as *const u8];
    let t: [usize; 2] = unsafe { transmute(a) };
    assert!(t[0] == &x as *const u8 as usize && t[1] == &y as *const u8 as usize);
}

#[kani::proof]
fn bug_ptr_array_to_usize_array() {
    let x = 5u8;
    let y = 6u8;
    let a = [&x as *const u8, &y as *const u8];
    let t: [usize; 2] = unsafe { transmute(a) };
    assert!(t[0] == &y as *const u8 as usize);
}

#[kani::proof]
fn safe_char_array_to_u32_array() {
    let a = ['a', 'b'];
    let t: [u32; 2] = unsafe { transmute(a) };
    assert!(t[0] == 97 && t[1] == 98);
}

#[kani::proof]
fn safe_ptr_addr_method() {
    let x = 5u8;
    let p = &x as *const u8;
    assert!(p.addr() == p as usize);
}

#[kani::proof]
#[kani::should_panic]
fn sp_enum8_array_to_u32_array() {
    let a = [E8::A, E8::B, E8::C, E8::D];
    let t: [u32; 1] = unsafe { transmute(a) };
    assert!(t[0] == 0x0403_0201);
}

#[kani::proof]
#[kani::should_panic]
fn sp_ptr_array_to_usize_array() {
    let x = 5u8;
    let y = 6u8;
    let a = [&x as *const u8, &y as *const u8];
    let t: [usize; 2] = unsafe { transmute(a) };
    assert!(t[0] == &x as *const u8 as usize && t[1] == &y as *const u8 as usize);
}

#[kani::proof]
#[kani::should_panic]
fn sp_ptr_addr_method() {
    let x = 5u8;
    let p = &x as *const u8;
    assert!(p.addr() == p as usize);
}
