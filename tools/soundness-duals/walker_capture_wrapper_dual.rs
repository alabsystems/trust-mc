// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- `unchecked_add` on a closure CAPTURE
//! inside a `Box<dyn Fn>` body, where the walker cannot read the capture.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_capture_core_wrapper  -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_capture_raw_intrinsic -> VERIFICATION:- FAILED  (same check)
//!   safe_capture_core_wrapper -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. The walked closure body adds its argument to a capture
//! the walker cannot read (`rvalue_gap_Use_root_projected`), so the operand of
//! the UB-carrying op is untranslatable. Written as the RAW intrinsic, the
//! BinOp sits in the closure body and the walker's helper fails closed
//! (`inline_rvalue_ub_check_dropped`). Written as core's `u8::unchecked_add`,
//! the untranslatable argument stops the walker at the CALL: the wrapper is
//! havocked under the blessed `nested_call_overapprox`, and because the
//! obligation sighting (`body_has_visible_obligation`) sees local-crate bodies
//! only, the wrapper's BinOp obligation vanished and the harness verified
//! SUCCESSFUL clean. The nested-call fallback now fails closed on a havocked
//! core `unchecked_*` wrapper or raw intrinsic by name
//! (`callee_is_ub_carrying_arithmetic` -> `nested_call_dropped_obligation`).
//!
//! Both bug rows are therefore non-certified FAILED (sound, not a certificate),
//! and the safe twin is demoted the same way (a precision cost, tracked on its
//! row): reading the capture is the precise fix and is not done here.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_capture_wrapper_dual.rs
#![feature(core_intrinsics)]
#![allow(internal_features)]

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

#[kani::proof]
fn bug_capture_core_wrapper() {
    let k: u8 = kani::any();
    let x: u8 = kani::any();
    let f: Box<dyn Fn(u8) -> u8> = Box::new(move |v: u8| unsafe { v.unchecked_add(k) });
    sink(f(x));
}

#[kani::proof]
fn bug_capture_raw_intrinsic() {
    let k: u8 = kani::any();
    let x: u8 = kani::any();
    let f: Box<dyn Fn(u8) -> u8> =
        Box::new(move |v: u8| unsafe { core::intrinsics::unchecked_add(v, k) });
    sink(f(x));
}

#[kani::proof]
fn safe_capture_core_wrapper() {
    let k: u8 = kani::any();
    let x: u8 = kani::any();
    kani::assume(k < 100 && x < 100);
    let f: Box<dyn Fn(u8) -> u8> = Box::new(move |v: u8| unsafe { v.unchecked_add(k) });
    sink(f(x));
}
