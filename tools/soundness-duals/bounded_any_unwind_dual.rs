// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- Kani's unwinding assertion on the loops
//! of the kani library's `bounded_any::<N>` for `String` and `Box<[P]>`, a call
//! the BMC lane models, under a declared unwind bound (fix/chc-walker-fail-closed,
//! the merge with main's Rule D, 2026-10-14; `bounded_enum_payload_panic_dual.rs`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-14):
//!   ba1_string_n4_u6_safe     -> VERIFICATION:- SUCCESSFUL
//!   ba1_string_n8_u3_bug      -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   ba2_box_slice_n4_u6_safe  -> VERIFICATION:- SUCCESSFUL
//!   ba2_box_slice_n8_u3_bug   -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!
//! MECHANISM UNDER TEST. Repair round 4 made the BMC lane state Kani's
//! unwinding assertion for a modelled call whose callee may loop, failing it
//! closed where no trip bound is known (`bmc_model_call_unwinding_check`). The
//! modelled `bounded_any::<N>` had none, so `bounded_enum_payload_panic_dual.rs`'s
//! safe row failed closed where main and Kani prove it. Each loop the library's
//! `String`, `Vec<P>` and `Box<[P]>` impls run takes at most `N` passes (the
//! `0..len` fill, `Utf8Chunks::next` over `N` bytes), so `N` is the bound
//! (`statement/terminator.rs`, `bmc_model_call_trip_bound`): the bound under
//! `U` drops the check, the bug rows fail on it.
//!
//! Lane scope: BMC and CHC.
//!
//! Run: trust-mc-driver -Z unstable-options --harness-timeout=30s bounded_any_unwind_dual.rs

#[kani::proof]
#[kani::unwind(6)]
fn ba1_string_n4_u6_safe() {
    let s: String = kani::bounded_any::<_, 4>();
    assert!(s.len() <= 4);
}

#[kani::proof]
#[kani::unwind(3)]
fn ba1_string_n8_u3_bug() {
    let s: String = kani::bounded_any::<_, 8>();
    assert!(s.len() <= 8);
}

#[kani::proof]
#[kani::unwind(6)]
fn ba2_box_slice_n4_u6_safe() {
    let b: Box<[u8]> = kani::bounded_any::<_, 4>();
    assert!(b.len() <= 4);
}

#[kani::proof]
#[kani::unwind(3)]
fn ba2_box_slice_n8_u3_bug() {
    let b: Box<[u8]> = kani::bounded_any::<_, 8>();
    assert!(b.len() <= 8);
}
