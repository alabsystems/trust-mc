// Task #71 vacuity sentinel: same body as dual71_correct_twin.rs but the
// ensures is a false-equivalent predicate (x != x through the as_ptr read
// lane). This harness must FAIL. If it reports SUCCESSFUL, the contract
// pipeline is proving VACUOUSLY (the ensures closure is never truly
// evaluated against reachable post-states) — the trap that plagued this
// family.
// kani-flags: -Zfunction-contracts

use std::cell::Cell;

struct InteriorMutability {
    x: Cell<u32>,
}

#[kani::requires(im.x.get() < 100)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| im.x.get() != im.x.get())]
fn modify(im: &InteriorMutability) {
    im.x.set(im.x.get() + 1)
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability = InteriorMutability { x: Cell::new(kani::any()) };
    modify(&im)
}
