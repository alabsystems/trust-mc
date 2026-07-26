// dual 3: WEAK invariant — inv admits x==1 at exit but post asserts x==2. MUST FAIL.
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[kani::proof]
fn lc_dual_weak() {
    let mut x: u8 = kani::any_where(|i| *i >= 2);

    #[kani::loop_invariant(x >= 1)]
    while x > 2 {
        x = x - 1;
    }

    assert!(x == 2);
}
