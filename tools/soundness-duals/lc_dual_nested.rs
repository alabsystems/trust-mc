// dual 5: NESTED loops with a WRONG inner invariant (j <= 1 is not re-established). MUST FAIL.
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn lc_dual_nested() {
    let mut i: u32 = 0;
    let mut s: u32 = 0;

    #[kani::loop_invariant(i <= 3)]
    while i < 3 {
        let mut j: u32 = 0;
        #[kani::loop_invariant(j <= 1)]
        while j < 2 {
            j += 1;
            s += 1;
        }
        i += 1;
    }
}
