// Oracle (per harness) — the 'bad twin'/'good twin' below, by name:
//   check_violated_ensures_walked -> VERIFICATION:- FAILED
//   check_correct_ensures_walked  -> VERIFICATION:- SUCCESSFUL
//
// DUAL for the transformed-body walker keystone:
// With RAW callee bodies, kani_contract_mode() inside a walker-inlined contract
// fn is the macro dummy ORIGINAL=0, so the ensures check arm (ASSERT=4) is
// never taken and the check is VACUOUS. With TRANSFORMED bodies the mode is a
// real constant and the dispatch folds to the assert arm.
//
// bad twin: ensures is VIOLATED (body returns a + 1, ensures demands a + 2).
//   MUST be FAILED — ideally a genuine CTREX on the ensures closure, not a
//   demotion-carried failure.
// good twin: ensures is CORRECT. MUST be SUCCESSFUL — no fabricated CEX.
//
// Shallow on purpose: single u32 add, no loops, no deep std chains, so the
// walker fully inlines the contract chain without depth exhaustion.
//
// Run: trust-mc-driver --ay-chc -Z unstable-options -Z function-contracts \
//        --harness-timeout=45s walker_mode_dual.rs

#[kani::ensures(|result| *result == a + 2)] // WRONG: body computes a + 1
fn add_two_bad(a: u32) -> u32 {
    a + 1
}

#[kani::ensures(|result| *result == a + 1)] // correct
fn add_one_good(a: u32) -> u32 {
    a + 1
}

#[kani::proof]
fn check_violated_ensures_walked() {
    let a: u32 = kani::any();
    kani::assume(a < 1000);
    let r = add_two_bad(a);
    // Use the result so the call is not dead-code eliminated.
    kani::assume(r < 2000);
}

#[kani::proof]
fn check_correct_ensures_walked() {
    let a: u32 = kani::any();
    kani::assume(a < 1000);
    let r = add_one_good(a);
    kani::assume(r < 2000);
}
