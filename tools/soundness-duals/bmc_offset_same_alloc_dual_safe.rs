// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle: MUST be SUCCESSFUL — every harness, on both lanes.
//
// The non-vacuity twin of `bmc_offset_same_alloc_dual.rs`: the same offsets
// kept inside their allocation, one-past-the-end included (Rust permits it,
// and Kani's `same_allocation` accepts it). A same-allocation check that
// fires here is a false failure; one CERTIFIED `Genuine` is a false
// certificate.
//
// Measured before the fix (2026-09-14, frozen dev-cli lane, BMC):
// `safe_add_one_past_end_offset_from` is tests/expected/offset-bounds-check/
// out_of_bounds_ub_check.rs `check_ptr_end`, which reported "pointer arithmetic
// overflow" and "Offset result and original pointer should point to the same
// allocation" [AY:CTREX_CAT:Genuine]: the stack address symbol was bounded by
// `addr <= usize::MAX - (size - 1)` and one stride region for `[addr, addr +
// size)`, so the one-past-the-end address could wrap to 0 or cross into the
// next stride.

/// out_of_bounds_ub_check.rs `check_ptr_end`: one past the end is in bounds.
#[kani::proof]
fn safe_add_one_past_end_offset_from() {
    let array = [0];
    let base_ptr = array.as_ptr();
    let end_ptr = unsafe { base_ptr.add(1) };
    assert_eq!(unsafe { end_ptr.offset_from(base_ptr) }, 1);
}

/// Every in-bounds element of a four-element array, and back.
#[kani::proof]
fn safe_add_within_array_then_sub() {
    let array = [1u64, 2, 3, 4];
    let base = array.as_ptr();
    let n: usize = kani::any();
    kani::assume(n <= 4);
    unsafe {
        let p = base.add(n);
        assert!(p.offset_from(base) == n as isize);
        assert!(p.sub(n) == base);
    }
}

/// offset_from.rs `check_offset_from_same_dangling`: equal pointers, however
/// far outside, have distance 0 and no allocation obligation.
#[kani::proof]
fn safe_offset_from_same_dangling() {
    let val = 10u128;
    let ptr: *const u128 = &val;
    let a: *const u128 = ptr.wrapping_add(10);
    let b: *const u128 = ptr.wrapping_add(5).wrapping_add(5);
    assert_eq!(unsafe { a.offset_from(b) }, 0);
}

/// A single scalar local: its address and one past it.
#[kani::proof]
fn safe_scalar_one_past() {
    let x = 5u32;
    let p: *const u32 = &x;
    let end = unsafe { p.add(1) };
    assert!(unsafe { end.offset_from(p) } == 1);
}

/// The twin: `wrapping_add(1)` / `wrapping_sub(1)` on a `u16` pointer move two
/// bytes, and no allocation obligation applies to a wrapping offset even when
/// it leaves the array.
#[kani::proof]
fn safe_wrapping_add_moves_elements() {
    let v = [0u16; 4];
    let base: *const u16 = v.as_ptr();
    let p = base.wrapping_add(1);
    assert!(p.addr() - base.addr() == 2);
    let far = base.wrapping_add(100).wrapping_sub(99);
    assert!(far == p);
}
