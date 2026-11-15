// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Two defects of one encoding, and the certificate rule that follows from it.
//
// A `&mut [T]` fat pointer built by the BMC lane (rvalue_address_of.rs
// `try_build_fat_pointer`) does not reuse the pointee's length or data for a
// MUTABLE borrow when the pointee's value is not a constructor of the fat
// sort. It fabricated both: a fresh LENGTH variable (`meta_name`) and a data
// array `const_array(one fresh element)` — EVERY element equal, an
// UNDER-approximation. Neither fabrication recorded anything, so a
// counterexample reading them was certified `Genuine`.
//
// Measured 2026-09-14 before the fix (frozen dev-cli lane, BMC):
//  * `safe_mut_slice_reads_first_element` FAILED `[AY:CTREX_CAT:Genuine]` on
//    `assertion failed: s.len() == 3` — a false CERTIFICATE on a program Kani
//    verifies. Expectation NOT_GENUINE: a counterexample over an encoder-minted
//    stand-in may be reported, never certified.
//  * `bug_mut_slice_elements_claimed_equal` FAILED (the fresh length made the
//    index checks fail too). MUST FAIL: `[1, 2, 3]` has s[0] != s[1], and the
//    forced-equal array alone would have PROVED `s[0] == s[1]`.
//
// The fix makes the data a fresh ARRAY (each element free) and records both
// fabrications with bmc_sound_havoc, so a SAT result classifies
// OverApproximation.

#[kani::proof]
fn bug_mut_slice_elements_claimed_equal() {
    let mut a = [1u8, 2, 3];
    let s: &mut [u8] = &mut a;
    assert!(s[0] == s[1]);
}

#[kani::proof]
fn safe_mut_slice_reads_first_element() {
    let mut a = [1u8, 2, 3];
    let s: &mut [u8] = &mut a;
    assert!(s.len() == 3);
    assert!(s[0] == 1);
}
