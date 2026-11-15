// Oracle: corpus-rev Kani 4c0fce8c3, measured 2026-09-26 and for the rows added
// 2026-10-01: every `bug_` harness FAILS, every `safe_` harness is SUCCESSFUL,
// and every `sp_` harness (`#[kani::should_panic]` over a program that never
// panics) FAILS.
//
// WHY THIS FILE EXISTS: the transmute cast of a multi-field struct follows the
// memory layout (chc_transmute_memory_order_dual.rs); two other routes
// reinterpret a struct's bytes and did not. Measured 2026-09-26 on main
// 25905b622 and on fix/chc-slice-length alike (ay 643b2851f, chc, 30 s):
// - a union written through a two-word struct field and read as u128 kept the
//   declaration-order flatten, so bug_union_struct_as_u128 PROVED (missed bug)
//   and safe_union_struct_as_u128 FAILED certified Genuine;
// - a pointer cast `&w as *const Words as *const u128` and the read through it
//   read a typed memory cell no store wrote, so both safe_ptr_cast_ rows FAILED
//   certified Genuine.
// Both routes now build the value from the layout (fix/chc-false-certificates).
// The union rows here cover the aggregate's write only; every other union
// route (reads, field writes, newtype fields) is in chc_union_memory_order_dual.rs,
// and a field read or a store through a pointer cast in
// chc_reinterpret_routes_dual.rs.
//
// ALIGNMENT. `Words` has alignment 8 and `u128` alignment 16, so Rust allows a
// u128 read through `&w` to be misaligned. Kani's layout puts every object at a
// highly aligned address (it PROVES `(&w as *const Words as usize) % 4096 == 0`
// for a local, measured 2026-09-26, corpus-rev Kani), so the read is aligned and
// Kani reports SUCCESSFUL. The fourth round of fix/chc-false-certificates kept
// a base aligned for the type only and certified the misaligned-pointer failure;
// the fifth round (2026-10-01) decided the shape by Kani's layout, the oracle:
// every base is 2^48-aligned, and `safe_eight_aligned_ptr_cast_struct_as_u128`
// (formerly `bug_underaligned_...`), `safe_pad_cast_u64` and `safe_sgn_cast_i64`
// are SUCCESSFUL, as in Kani. The struct-to-u128 pointer-cast rows still read
// a 16-aligned `AWords`.

#[repr(C)]
#[derive(Clone, Copy)]
struct Words {
    lo: u64,
    hi: u64,
}

/// `Words` with the alignment of `u128`, so a u128 read through it is aligned
/// on every execution.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
struct AWords {
    lo: u64,
    hi: u64,
}

#[repr(C)]
union U {
    w: Words,
    x: u128,
}

#[kani::proof]
fn bug_union_struct_as_u128() {
    let u = U { w: Words { lo: 1, hi: 0 } };
    let x = unsafe { u.x };
    assert!(x != 1);
}

#[kani::proof]
fn safe_union_struct_as_u128() {
    let u = U { w: Words { lo: 1, hi: 0 } };
    let x = unsafe { u.x };
    assert!(x == 1);
}

#[kani::proof]
fn bug_ptr_cast_struct_as_u128() {
    let w = AWords { lo: 1, hi: 0 };
    let x = unsafe { *(&w as *const AWords as *const u128) };
    assert!(x != 1);
}

#[kani::proof]
fn safe_ptr_cast_struct_as_u128() {
    let w = AWords { lo: 1, hi: 0 };
    let x = unsafe { *(&w as *const AWords as *const u128) };
    assert!(x == 1);
}

/// The 8-aligned struct read as a 16-aligned u128: aligned in Kani's layout
/// (see ALIGNMENT above).
#[kani::proof]
fn safe_eight_aligned_ptr_cast_struct_as_u128() {
    let w = Words { lo: 1, hi: 0 };
    let x = unsafe { *(&w as *const Words as *const u128) };
    assert!(x == 1);
}

#[kani::proof]
fn bug_ptr_cast_u128_as_struct() {
    let x: u128 = 1;
    let w = unsafe { *(&x as *const u128 as *const Words) };
    assert!(w.lo != 1);
}

#[kani::proof]
fn safe_ptr_cast_u128_as_struct() {
    let x: u128 = 1 | (7 << 64);
    let w = unsafe { *(&x as *const u128 as *const Words) };
    assert!(w.lo == 1 && w.hi == 7);
}

#[kani::proof]
#[kani::should_panic]
fn sp_eight_aligned_ptr_cast_struct_as_u128() {
    let w = Words { lo: 1, hi: 0 };
    let x = unsafe { *(&w as *const Words as *const u128) };
    assert!(x == 1);
}

/// A 4-aligned `#[repr(C)]` struct read whole as a `u64` at offset 0 (aligned
/// in Kani's layout; review probe `p1_ptr_cast.rs` `pad_cast_safe`).
#[repr(C)]
#[derive(Clone, Copy)]
struct Pad {
    a: u8,
    b: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Sgn {
    a: i32,
    b: i32,
}

#[kani::proof]
fn safe_pad_cast_u64() {
    let s = Pad { a: 1, b: 2 };
    let x = unsafe { *(&s as *const Pad as *const u64) };
    assert!((x & 0xff) == 1 && (x >> 32) == 2);
}

#[kani::proof]
fn bug_pad_cast_u64() {
    let s = Pad { a: 1, b: 2 };
    let x = unsafe { *(&s as *const Pad as *const u64) };
    assert!((x >> 32) == 1);
}

#[kani::proof]
#[kani::should_panic]
fn sp_pad_cast_u64() {
    let s = Pad { a: 1, b: 2 };
    let x = unsafe { *(&s as *const Pad as *const u64) };
    assert!((x & 0xff) == 1 && (x >> 32) == 2);
}

#[kani::proof]
fn safe_sgn_cast_i64() {
    let s = Sgn { a: -1, b: 1 };
    let x = unsafe { *(&s as *const Sgn as *const i64) };
    assert!(x == 0x0000_0001_ffff_ffff);
}

#[kani::proof]
fn bug_sgn_cast_i64() {
    let s = Sgn { a: -1, b: 1 };
    let x = unsafe { *(&s as *const Sgn as *const i64) };
    assert!(x == -1);
}

#[kani::proof]
#[kani::should_panic]
fn sp_sgn_cast_i64() {
    let s = Sgn { a: -1, b: 1 };
    let x = unsafe { *(&s as *const Sgn as *const i64) };
    assert!(x == 0x0000_0001_ffff_ffff);
}
