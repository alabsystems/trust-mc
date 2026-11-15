// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `offset_from` with an operand outside its allocation is undefined behavior, and undefined
//! behavior is not a panic: `#[kani::should_panic]` does not accept it. One past the end is in
//! bounds.
//!
//! Oracle: Rust semantics (`<*const T>::offset_from` safety section), cross-checked with upstream
//! Kani (see the manifest rows).
//!   MUST FAIL: bug_offset_from_oob_should_panic (tests/expected/offset-bounds-check/offset_from.rs
//!     check_offset_from_oob_ptr), bug_offset_from_two_past_end.
//!   MUST PASS: safe_offset_from_one_past_end, safe_offset_from_one_past_end_array.

#[kani::proof]
#[kani::should_panic]
fn bug_offset_from_oob_should_panic() {
    let val = 10u128;
    let ptr: *const u128 = &val;
    let ptr_oob: *const u128 = ptr.wrapping_add(10);
    let _offset = unsafe { ptr_oob.offset_from(ptr) };
}

#[kani::proof]
fn bug_offset_from_two_past_end() {
    let val = 10u128;
    let ptr: *const u128 = &val;
    let ptr_oob: *const u128 = ptr.wrapping_add(2);
    let offset = unsafe { ptr_oob.offset_from(ptr) };
    assert!(offset == 2);
}

#[kani::proof]
fn safe_offset_from_one_past_end() {
    let val = 10u128;
    let ptr: *const u128 = &val;
    let end: *const u128 = ptr.wrapping_add(1);
    let offset = unsafe { end.offset_from(ptr) };
    assert!(offset == 1);
}

#[kani::proof]
fn safe_offset_from_one_past_end_array() {
    let arr = [1u32, 2, 3];
    let first: *const u32 = &arr[0];
    let end: *const u32 = first.wrapping_add(3);
    let offset = unsafe { end.offset_from(first) };
    assert!(offset == 3);
}
