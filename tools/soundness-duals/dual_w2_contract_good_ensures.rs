// Wall-2 dual twin: same contract with a CORRECT ensures — must PASS (or
// demote honestly), proving the bad-ensures FAIL above is a real check.
// kani-flags: -Zfunction-contracts

#[kani::ensures(|result| *result == a + 1)]
fn add_one(a: u8) -> u8 {
    a + 1
}

#[kani::proof_for_contract(add_one)]
fn check_add_one() {
    let a: u8 = kani::any();
    kani::assume(a < 100);
    let _ = add_one(a);
}
