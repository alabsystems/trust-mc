// dual 1: BASE violation — entry allows x==2 but invariant claims x>=3. MUST FAIL.
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn lc_dual_base() {
    let mut x: u8 = kani::any_where(|i| *i >= 2);

    #[kani::loop_invariant(x >= 3)]
    while x > 2 {
        x = x - 1;
    }
}
