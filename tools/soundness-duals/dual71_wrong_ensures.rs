// Task #71 adversarial dual: Cell-through-contract with a deliberately
// VIOLATED ensures — the body adds 1 but the ensures claims +2. This harness
// must FAIL (Genuine preferred; demotion-carried acceptable). If it reports
// SUCCESSFUL the ensures never observed the store (vacuous-ensures false
// Safe — the representation-lane divergence trap).
// kani-flags: -Zfunction-contracts

use std::cell::Cell;

struct InteriorMutability {
    x: Cell<u32>,
}

#[kani::requires(im.x.get() < 100)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| im.x.get() == old(im.x.get()) + 2)]
fn modify(im: &InteriorMutability) {
    im.x.set(im.x.get() + 1)
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability = InteriorMutability { x: Cell::new(kani::any()) };
    modify(&im)
}
