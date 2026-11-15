// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// DUAL (must-fail twin): a slice range whose backing does not resolve.
//
// WHY THIS FILE EXISTS. `codegen_call_slice_range/range_to.rs` and
// `range_from.rs` REGISTERED the "range end/start index out of range for
// slice" property and then emitted its rule only inside
// `if let Some(ref backing) = resolve_slice_backing(..)`. When the backing did
// not resolve the check was DROPPED while the property stayed in the table.
//
// That is not caught by the driver's lost-error-rules gate: the gate is
// harness-global, so any other `error` rule in the same harness satisfies it,
// and `chc_success_properties` then marks EVERY registered property `Success`.
// A genuinely out-of-bounds range would have been reported proved — the same
// shape as `lost_error_rules_dual.rs`, which exists because that shortcut was
// once a false proof.
//
// EXTENDED 2026-09-17: `range.rs` — the FULL `&s[a..b]` sibling in the same
// directory — was never fixed. It is strictly worse than the two above: it
// emits its REVERSED-range rule unconditionally, so `error_pN` stays derivable
// and even a ruleless-property gate cannot see the dropped OOB obligation.
//
// Oracle: MUST FAIL. Each harness pairs a check that DOES encode (so the
// harness carries another `error` rule and the gate stays quiet) with an
// out-of-bounds slice range reached through a pointer round-trip that defeats
// backing resolution.

#[kani::proof]
fn range_to_out_of_bounds_must_fail() {
    let data: [u8; 4] = [1, 2, 3, 4];
    // A check that encodes normally, so the harness has an `error` rule.
    assert!(data[0] == 1);
    // Defeat backing resolution: reach the slice through a raw round-trip.
    let p = data.as_ptr();
    let s: &[u8] = unsafe { core::slice::from_raw_parts(p, 4) };
    let n = kani::any_where(|n: &usize| *n > 4 && *n < 16);
    let sub = &s[..n];
    assert!(sub.len() <= 4);
}

#[kani::proof]
fn range_from_out_of_bounds_must_fail() {
    let data: [u8; 4] = [1, 2, 3, 4];
    assert!(data[3] == 4);
    let p = data.as_ptr();
    let s: &[u8] = unsafe { core::slice::from_raw_parts(p, 4) };
    let n = kani::any_where(|n: &usize| *n > 4 && *n < 16);
    let sub = &s[n..];
    assert!(sub.is_empty());
}

// NOT A WITNESS — measured 2026-09-18. This harness reports FAILED with the
// `range.rs` repair REVERTED, so it does not discriminate: something else in it
// fails first. The repair still stands on the code — the property is registered,
// the reversed-range rule keeps `error_pN` derivable, and the OOB rule is
// emitted only when the backing resolves — but a harness whose ONLY possible
// failure is the dropped OOB check has not been written yet. Wanted.
#[kani::proof]
fn range_full_out_of_bounds_must_fail() {
    let data: [u8; 4] = [1, 2, 3, 4];
    assert!(data[1] == 2);
    let p = data.as_ptr();
    let s: &[u8] = unsafe { core::slice::from_raw_parts(p, 4) };
    let n = kani::any_where(|n: &usize| *n > 4 && *n < 16);
    let sub = &s[1..n];
    assert!(sub.len() <= 3);
}
