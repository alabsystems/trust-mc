// Rotate dual (u64-only): the wide-width sibling of rot_dual_skeptic — pins
// the rotate intrinsic error edge on u64 (the dead-var pruner is width-generic
// and a width-specific guard regression would only show on the wide lane).
// x == 1, 0 < n < 64 => x.rotate_left(n) == 1u64 << n != 1. MUST stay
// VERIFICATION:- FAILED; a SUCCESSFUL means the restored guard went UNSAT and
// deleted the real error edge (missed bug).

#[kani::proof]
fn rot_dual_u64only() {
    let x: u64 = kani::any();
    let n: u32 = kani::any();
    kani::assume(x == 1);
    kani::assume(n < 64 && n > 0);
    assert!(x.rotate_left(n) == x);
}
