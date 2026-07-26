// dual 2: NON-INDUCTIVE — i += 2 can jump from 4 to 6, invariant i<=5 not re-established. MUST FAIL.
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn lc_dual_noninductive() {
    let mut i: u32 = 0;

    #[kani::loop_invariant(i <= 5)]
    while i < 5 {
        i += 2;
    }
}
