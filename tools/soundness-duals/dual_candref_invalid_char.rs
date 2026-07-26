// kani-flags: -Z valid-value-checks -Z mem-predicates
//
// VALVALID_ARRAY_NONZERO_KANIMEM dual (CRITICAL / missed-bug tripwire): a
// pointer to bytes forming an INVALID `char` (0x110000 is one past the maximum
// Unicode scalar value) must NOT be dereferenceable as a `char`. Asserting
// `can_dereference` on it must therefore FAIL.
//
// This is the exact missed bug of the old allocation-only lowering
// (`heap_is_allocated` alone): the bytes are allocated, so the pre-fix model
// answered `true` and this harness spuriously PROVED. If it is SUCCESSFUL again
// the value-validity model is unsound — fix or revert.
//
// Run:
//   trust-mc-driver --ay-chc -Z unstable-options -Z valid-value-checks \
//     -Z mem-predicates --harness-timeout=15s dual_candref_invalid_char.rs
//
// Expected: VERIFICATION:- FAILED (can_dereference == false -> assert fails).
#[kani::proof]
fn dual_candref_invalid_char() {
    let bad: u32 = 0x11_0000; // one past char::MAX -> invalid char bit-pattern
    let p = &bad as *const u32 as *const char;
    // can_dereference must be FALSE for the invalid value, so this assert FAILS.
    assert!(kani::mem::can_dereference(p));
}
