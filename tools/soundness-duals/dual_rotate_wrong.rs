// Rotate dual (Rotate skeptic): targets the restored guard constraints on
// per-property `error_p{N}` rules NOT accidentally making the error rules
// UNSAT. With x == 1 and 0 < n < 32, `x.rotate_left(n) == 1 << n != 1`, so
// the assertion is genuinely false for every admitted n. MUST stay
// VERIFICATION:- FAILED after the pruner fix — a SUCCESSFUL here means a
// mistranslated/UNSAT restored guard deleted the real error edge.

#[kani::proof]
fn dual_rotate_wrong() {
    let x: u32 = kani::any();
    let n: u32 = kani::any();
    kani::assume(x == 1);
    kani::assume(n < 32 && n > 0);
    assert!(x.rotate_left(n) == x);
}
