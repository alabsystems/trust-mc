// SOUNDNESS DUAL (enum-array-element-read vs enum-literal eq consistency).
//
// EXPECTED VERDICT: VERIFICATION:- SUCCESSFUL.
//
// Twin of the enum-element-read-eq fix: an `Option<u8>` read out of an array
// (canonical compact flatten) is compared against a directly-constructed
// `Some(7)` enum literal in derived `PartialEq::eq`. The fix makes the literal
// referent resolve to its decoded datatype value (not its pointer address), so
// both operands share one bit-layout and `a[i] == Some(7)` is provable when it
// is genuinely true. A FAILURE here would mean the true equality is not
// provable (the regression this dual guards).
#[kani::proof]
fn check() {
    let a = [Some(7u8); 5];
    let i: usize = kani::any();
    kani::assume(i < 5);
    assert_eq!(a[i], Some(7));
}
