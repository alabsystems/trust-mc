// Rotate dual (skeptic): guards the pruner/dead-var fix on the rotate
// intrinsic lane — the restored per-property error_p{N} guard constraints
// must NOT make the error rule UNSAT. With x == 1 and 0 < n < 16 on a u16,
// x.rotate_left(n) == 1 << n != 1 for every admitted n, so the assertion is
// genuinely false. MUST stay VERIFICATION:- FAILED; a SUCCESSFUL here means a
// mistranslated restored guard deleted the real error edge (missed bug).

#[kani::proof]
fn rot_dual_skeptic() {
    let x: u16 = kani::any();
    let n: u32 = kani::any();
    kani::assume(x == 1);
    kani::assume(n < 16 && n > 0);
    // rotate_left by a nonzero amount moves the single set bit off position 0.
    assert!(x.rotate_left(n) == x);
}
