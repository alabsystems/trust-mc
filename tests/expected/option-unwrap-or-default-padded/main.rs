// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// A single-field struct NARROWER than the flattened Option payload. The phi
// merging `<S as Default>::default()` (a datatype) with the `Some` arm (a
// bv64) used to flatten MSB-first with TRAILING zero padding, parking the
// field in bits 63..56, while the erased-wrapper read takes bits 7..0 — so a
// default of 7 was PROVED to be 0. u64 (no padding) was always right; u8 and
// u32 were both wrong.

struct S8 { a: u8 }
impl Default for S8 { fn default() -> S8 { S8 { a: 7 } } }
struct S32 { v: u32 }
impl Default for S32 { fn default() -> S32 { S32 { v: 0x0102_0304 } } }

#[kani::proof]
fn u8_default_is_seven() { let o: Option<S8> = None; assert!(o.unwrap_or_default().a == 7); }
#[kani::proof]
fn u8_default_is_not_zero() { let o: Option<S8> = None; assert!(o.unwrap_or_default().a == 0); }
#[kani::proof]
fn u32_default_is_exact() { let o: Option<S32> = None; assert!(o.unwrap_or_default().v == 0x0102_0304); }
#[kani::proof]
fn u32_default_is_not_zero() { let o: Option<S32> = None; assert!(o.unwrap_or_default().v == 0); }
#[kani::proof]
fn some_arm_still_wins() { let o: Option<S8> = Some(S8 { a: 3 }); assert!(o.unwrap_or_default().a == 3); }
