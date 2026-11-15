// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `offset_from_unsigned`'s `self >= origin` UB precondition under `#[kani::should_panic]`.
//!
//! Oracle: upstream Kani 0.67.0, measured 2026-09-15 on this file.
//!   MUST be SUCCESSFUL (panics as expected): sp_unit_same_pointer, sp_unit_distinct_locals
//!   MUST be FAILED:                          sp_u8_reversed_in_bounds, u8_reversed_in_bounds
//!   MUST be SUCCESSFUL:                      u8_ordered_in_bounds
//!
//! trust-mc evaluates `ub_checks()` as true (#3299); Kani compiles every `RuntimeChecks`
//! to false, so `precondition_check` never runs there. The precondition failure path is a
//! `panic_nounwind_fmt`: an abort, not an unwinding panic.
//!
//! `sp_u8_reversed_in_bounds` is the guard. Its only violation is the precondition, and Kani
//! fails it on its own "Expected non-negative distance" check. Counting the precondition's
//! `panic_nounwind_fmt` as the expected panic would pass it: an unsound should_panic pass.
//!
//! `sp_unit_distinct_locals` is the corpus shape
//! (`tests/expected/offset-bounds-check/offset_from_unsigned.rs`,
//! `check_offset_from_unsigned_unit_panic`). On the frozen nightly with
//! `-C debug-assertions=on -C opt-level=0` the two `()` locals get distinct stack addresses
//! in declaration order, and the program aborts on "unsafe precondition(s) violated:
//! ptr::offset_from_unsigned requires `self >= origin`" before the ZST `assert!`. So a lane
//! that checks UB preconditions and fails it describes the debug build, not an encoding
//! artifact. At opt-level=2 the addresses are equal and the `assert!` panics.

#[kani::proof]
#[kani::should_panic]
fn sp_unit_distinct_locals() {
    let val1 = kani::any();
    let val2 = kani::any();
    let ptr1: *const () = &val1 as *const _ as *const ();
    let ptr2: *const () = &val2 as *const _ as *const ();
    let _offset = unsafe { ptr1.offset_from_unsigned(ptr2) };
}

#[kani::proof]
#[kani::should_panic]
fn sp_unit_same_pointer() {
    let val = ();
    let ptr: *const () = &val;
    let _offset = unsafe { ptr.offset_from_unsigned(ptr) };
}

#[kani::proof]
#[kani::should_panic]
fn sp_u8_reversed_in_bounds() {
    let arr: [u8; 4] = kani::any();
    let first: *const u8 = &arr[0];
    let last: *const u8 = &arr[3];
    let _offset = unsafe { first.offset_from_unsigned(last) };
}

#[kani::proof]
fn u8_reversed_in_bounds() {
    let arr: [u8; 4] = kani::any();
    let first: *const u8 = &arr[0];
    let last: *const u8 = &arr[3];
    let _offset = unsafe { first.offset_from_unsigned(last) };
}

#[kani::proof]
fn u8_ordered_in_bounds() {
    let arr: [u8; 4] = kani::any();
    let first: *const u8 = &arr[0];
    let last: *const u8 = &arr[3];
    let offset = unsafe { last.offset_from_unsigned(first) };
    assert!(offset == 3);
}
