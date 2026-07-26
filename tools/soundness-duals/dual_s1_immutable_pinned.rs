// P2-S1 precision dual: a contract that relies on the value of an IMMUTABLE
// (non-interior-mut) static. Immutable statics are truly constant, so they
// must STAY PINNED to their initializer in contract mode — this harness must
// verify SUCCESSFULLY both before and after the static-havoc fix.

static LIMIT: u32 = 10;

#[kani::requires(x < LIMIT)]
#[kani::ensures(|result| *result < 20)]
pub fn below_twice_limit(x: u32) -> u32 {
    // Only correct because LIMIT really is 10.
    x + LIMIT - 10
}

#[kani::proof_for_contract(below_twice_limit)]
fn check_below_twice_limit() {
    below_twice_limit(kani::any());
}
