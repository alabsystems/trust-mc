// Wall-2 dual twin: same loop with a CORRECT invariant — must PASS (or
// demote honestly), proving the bad-invariant FAIL above is a real check.
// kani-flags: -Z loop-contracts

#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn good_inv_on_entry() {
    let mut x: u8 = 10;
    #[kani::loop_invariant(x >= 5)]
    while x > 5 {
        x = x - 1;
    }
    assert!(x == 5);
}
