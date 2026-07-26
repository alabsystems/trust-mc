// Wall-2 dual: contracted fn whose ensures is VIOLATED, exercised through the
// kani::internal::run_contract_fn closure shape — must FAIL.
// kani-flags: -Zfunction-contracts

#[kani::ensures(|result| *result == a + 2)]
fn add_one(a: u8) -> u8 {
    a + 1
}

#[kani::proof_for_contract(add_one)]
fn check_add_one() {
    let a: u8 = kani::any();
    kani::assume(a < 100);
    let _ = add_one(a);
}
