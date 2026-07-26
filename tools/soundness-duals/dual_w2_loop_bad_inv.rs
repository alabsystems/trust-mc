// Wall-2 dual: loop invariant VIOLATED ON ENTRY — the base case of the
// loop-contract proof rule must FAIL (never vacuously pass).
// kani-flags: -Z loop-contracts

#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn bad_inv_on_entry() {
    let mut x: u8 = 10;
    // x = 10 on entry, invariant claims x >= 20: base case is false.
    #[kani::loop_invariant(x >= 20)]
    while x > 5 {
        x = x - 1;
    }
    assert!(x == 5);
}
