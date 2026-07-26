// kani-flags: -Z valid-value-checks -Z mem-predicates
//
// VALVALID_ARRAY_NONZERO_KANIMEM dual (positive): a pointer to a KNOWN-valid
// `char` must be dereferenceable. Guards against the fix over-constraining and
// turning a genuinely-valid value into a spurious `can_dereference == false`.
//
// Run:
//   trust-mc-driver --ay-chc -Z unstable-options -Z valid-value-checks \
//     -Z mem-predicates --harness-timeout=15s dual_candref_valid_char.rs
//
// Expected: VERIFICATION:- SUCCESSFUL.
#[kani::proof]
fn dual_candref_valid_char() {
    let c: char = 'Z';
    let p = &c as *const char;
    assert!(kani::mem::can_dereference(p));
}
