// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Attribution of verdicts to checks, as route duals: panics that may bypass the Kani macro
//! overrides, mixed with a registered check, and `should_panic` over panics and UB.
//!
//! A counterexample through a bare `error` head names no property (the anonymous `chc.0`), so
//! it cannot show the failure was a panic: it must never stand as the expected panic of a
//! `should_panic` harness. What IS a panic follows Kani: its std turns `process::abort()` into
//! `kani::panic("Function abort() was invoked")` (`library/std/src/process.rs`), and
//! `hint::unreachable_unchecked` checks its `ub_checks` precondition, which panics before the
//! UB, so `sp_abort_holds` and `sp_unreachable_unchecked_holds` are expected panics. A null or
//! dangling read is UB with no panic in front of it, so those stay `_refuted`.

#![allow(unreachable_code)]

#[kani::proof]
fn core_assert_holds() {
    let x: u8 = kani::any();
    core::assert!((x as u16) + 1 > 0);
}

#[kani::proof]
fn core_assert_refuted() {
    let x: u8 = kani::any();
    core::assert!(x != 7);
}

#[kani::proof]
fn panic_any_refuted() {
    let x: u8 = kani::any();
    if x == 7 {
        std::panic::panic_any(7u8);
    }
}

#[kani::proof]
fn mixed_core_assert_holds() {
    let x: u8 = kani::any();
    let y = x / 2;
    kani::assert(y <= 127, "registered");
    core::assert!(y < 200);
}

#[kani::proof]
fn mixed_core_assert_refuted() {
    let x: u8 = kani::any();
    let y = x / 2;
    kani::assert(y <= 127, "registered");
    core::assert!(y != 5);
}

#[kani::proof]
fn abort_refuted() {
    let x: u8 = kani::any();
    if x == 9 {
        std::process::abort();
    }
}

#[kani::proof]
#[kani::should_panic]
fn sp_panic_holds() {
    let x: u8 = kani::any();
    if x < 200 {
        panic!("mostly");
    }
    panic!("always");
}

#[kani::proof]
#[kani::should_panic]
fn sp_null_deref_refuted() {
    let p: *const u8 = std::ptr::null();
    let v = unsafe { *p };
    let _ = v;
}

#[kani::proof]
#[kani::should_panic]
fn sp_unreachable_unchecked_holds() {
    let x: u8 = kani::any();
    if x == 3 {
        unsafe { std::hint::unreachable_unchecked() }
    }
    kani::assume(x == 3);
}

#[kani::proof]
#[kani::should_panic]
fn sp_dangling_read_refuted() {
    let p: *const u32 = {
        let v = Box::new(5u32);
        &*v as *const u32
    };
    let _ = unsafe { *p };
}

#[kani::proof]
#[kani::should_panic]
fn sp_abort_holds() {
    std::process::abort();
}
