// Dual C (loop-contract skeptic): multiple_loops variant targeting a REAL
// post-loop assertion violation. Starting from x == 10 with guard `x > 5`
// and body `x = x - 6`: one iteration gives x = 4, so the loop exits with
// x == 4 and `assert!(x == 5 || x == 20)` is genuinely violated. MUST stay
// VERIFICATION:- FAILED after the pruner fix (exercises restored `__mid`
// entry-chain equalities feeding a user assert after loop composition).
// Plain loops, no loop contracts, no extra flags needed.

#[kani::proof]
fn dual_multiloop_assert() {
    let mut x: u16 = kani::any();
    kani::assume(x == 10);
    while x > 5 {
        x = x - 6;
    }
    // Second loop keeps the multiple_loops fragment-composition shape.
    let mut y: u16 = 0;
    while y < 3 {
        y += 1;
    }
    assert!(x == 5 || x == 20);
}
