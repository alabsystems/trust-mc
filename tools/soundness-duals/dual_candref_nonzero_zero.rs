// kani-flags: -Z valid-value-checks -Z mem-predicates
//
// VALVALID_ARRAY_NONZERO_KANIMEM dual (missed-bug tripwire): a pointer to a
// zeroed `NonZeroU32` must NOT be dereferenceable as `NonZeroU32` (0 is the one
// forbidden bit-pattern). Asserting `can_dereference` on it must FAIL.
//
// Before the fix, `NonZero<T>` fell through to the "single-variant ADT" / scalar
// field recursion, whose opaque `NonZeroInner` field was treated as an
// unconstrained (always-valid) integer — silently admitting the zero value.
// If this harness is SUCCESSFUL the NonZero validity model is unsound.
//
// Run:
//   trust-mc-driver --ay-chc -Z unstable-options -Z valid-value-checks \
//     -Z mem-predicates --harness-timeout=15s dual_candref_nonzero_zero.rs
//
// Expected: VERIFICATION:- FAILED (can_dereference == false -> assert fails).
use std::num::NonZeroU32;

#[kani::proof]
fn dual_candref_nonzero_zero() {
    let z: u32 = 0; // the one invalid NonZeroU32 bit-pattern
    let p = &z as *const u32 as *const NonZeroU32;
    // can_dereference must be FALSE for the zero value, so this assert FAILS.
    assert!(kani::mem::can_dereference(p));
}
