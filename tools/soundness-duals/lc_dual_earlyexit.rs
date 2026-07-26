// dual 4 (CRITICAL): loop panics at iteration 3; invariant goes false at iteration 1.
// The old encoding silently EXITED the loop when the invariant went false (fail-open),
// hiding the panic and reporting SUCCESS. MUST FAIL.
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn lc_dual_earlyexit() {
    let mut i: u32 = 0;

    #[kani::loop_invariant(i == 0)]
    while i < 5 {
        if i == 3 {
            panic!("iteration 3 reached");
        }
        i += 1;
    }
}
