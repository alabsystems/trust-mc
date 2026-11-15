// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r11b): Joined Option/Result == over other payload layouts (i16, unit, u64, Result<(), u8>).
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r11b. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   opt_i16_join_must_fail     -> VERIFICATION:- FAILED (assertion)
//   opt_i16_join_safe          -> VERIFICATION:- SUCCESSFUL
//   opt_unit_join_must_fail    -> VERIFICATION:- FAILED (assertion)
//   opt_unit_join_safe         -> VERIFICATION:- SUCCESSFUL
//   opt_u64_join_must_fail     -> VERIFICATION:- FAILED (assertion)
//   opt_u64_join_safe          -> VERIFICATION:- SUCCESSFUL
//   result_unit_join_must_fail -> VERIFICATION:- FAILED (assertion)
//   result_unit_join_safe      -> VERIFICATION:- SUCCESSFUL

#[kani::proof]
fn opt_i16_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<i16> = if b { Some(-3) } else { Some(-3) };
    assert!(!(o == Some(-3)));
}
#[kani::proof]
fn opt_i16_join_safe() {
    let b: bool = kani::any();
    let o: Option<i16> = if b { Some(-3) } else { Some(-3) };
    assert!(o == Some(-3));
}
#[kani::proof]
fn opt_unit_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<()> = if b { Some(()) } else { Some(()) };
    assert!(!(o == Some(())));
}
#[kani::proof]
fn opt_unit_join_safe() {
    let b: bool = kani::any();
    let o: Option<()> = if b { Some(()) } else { Some(()) };
    assert!(o == Some(()));
}
#[kani::proof]
fn opt_u64_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u64> = if b { Some(1 << 40) } else { Some(1 << 40) };
    assert!(!(o == Some(1 << 40)));
}
#[kani::proof]
fn opt_u64_join_safe() {
    let b: bool = kani::any();
    let o: Option<u64> = if b { Some(1 << 40) } else { Some(1 << 40) };
    assert!(o == Some(1 << 40));
}
#[kani::proof]
fn result_unit_join_must_fail() {
    let b: bool = kani::any();
    let o: Result<(), u8> = if b { Ok(()) } else { Ok(()) };
    assert!(!(o == Ok(())));
}
#[kani::proof]
fn result_unit_join_safe() {
    let b: bool = kani::any();
    let o: Result<(), u8> = if b { Ok(()) } else { Ok(()) };
    assert!(o == Ok(()));
}
