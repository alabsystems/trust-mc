// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle: MUST FAIL — every harness, on both lanes.
//
// Kani's pointer-offset models (library/kani_core/src/models.rs `offset`,
// `ptr_offset_from`) raise `kani::safety_check(same_allocation_internal(..))`:
// the result of `ptr::offset` / `add` / `sub`, and both operands of
// `offset_from`, must lie inside ONE allocation (one-past-the-end included).
// Kani prints, for each harness below:
//
//     Failed Checks: Offset result and original pointer must point to the same allocation
//     (or "... should point to the same allocation" for offset_from)
//
// A safety check is UB detection, never a panic, so `#[kani::should_panic]`
// does NOT excuse it (tests/expected/offset-bounds-check pins that).
//
// What the BMC lane did before this pair (measured 2026-09-14 on the frozen
// dev-cli lane): the same-allocation predicate compared `addr / HEAP_STRIDE`,
// a 1 MiB region, so a pointer 160 bytes past a 16-byte stack local was "the
// same allocation" and `bug_offset_from_wrapping_beyond_object` was not
// reported; and the offset models' labels fell to the `assertion` default in
// the driver, so `bug_sub_before_start_should_panic` printed SUCCESSFUL.

/// tests/expected/offset-bounds-check/offset_from.rs `check_offset_from_oob_ptr`,
/// without should_panic: 10 elements past a one-element object.
#[kani::proof]
fn bug_offset_from_wrapping_beyond_object() {
    let val = 10u128;
    let ptr: *const u128 = &val;
    let ptr_oob: *const u128 = ptr.wrapping_add(10);
    let _offset = unsafe { ptr_oob.offset_from(ptr) };
}

/// Two distinct stack locals are two allocations.
#[kani::proof]
fn bug_offset_from_two_locals() {
    let a = 1u32;
    let b = 2u32;
    let pa: *const u32 = &a;
    let pb: *const u32 = &b;
    let _d = unsafe { pa.offset_from(pb) };
}

/// One element BEFORE the start of an array is outside it.
#[kani::proof]
fn bug_sub_before_array_start() {
    let array = [0u8; 4];
    let base = array.as_ptr();
    let before = unsafe { base.sub(1) };
    assert!(before.addr() != base.addr());
}

/// Two past the end of a two-element array is outside it (one past is not).
#[kani::proof]
fn bug_add_two_past_end() {
    let array = [7u32; 2];
    let base = array.as_ptr();
    let past = unsafe { base.add(3) };
    assert!(past.addr() != base.addr());
}

/// The same UB under `should_panic`: a safety check is not a panic.
/// tests/expected/offset-bounds-check/out_of_bounds_ub_check.rs `check_ptr_oob`.
#[kani::proof]
#[kani::should_panic]
fn bug_sub_before_start_should_panic() {
    let array = [0];
    let base_ptr = array.as_ptr();
    let oob_ptr = unsafe { base_ptr.sub(1) };
    assert_ne!(oob_ptr.addr(), base_ptr.addr());
}

/// A symbolic count that may leave the object must be reported.
#[kani::proof]
fn bug_add_symbolic_count_may_leave() {
    let array = [1u16; 3];
    let base = array.as_ptr();
    let n: usize = kani::any();
    kani::assume(n <= 4);
    let p = unsafe { base.add(n) };
    assert!(p.addr() >= base.addr());
}

/// `<*const T>::wrapping_add(n)` moves `n * size_of::<T>()` bytes. The BMC lane
/// matched it as the integer method and moved `n` bytes, so a claim of a
/// ONE-byte move on a `u16` pointer proved. MUST FAIL.
#[kani::proof]
fn bug_wrapping_add_moves_bytes_not_elements() {
    let v = [0u16; 4];
    let base: *const u16 = v.as_ptr();
    let p = base.wrapping_add(1);
    assert!(p.addr() - base.addr() == 1);
}
