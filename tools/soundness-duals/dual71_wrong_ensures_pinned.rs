// Task #71 adversarial dual (pinned-initial variant, no old()): requires pins
// the pre-state to exactly 5, the body adds 1 (post == 6), and the ensures
// claims 7 — deliberately violated. Must FAIL. SUCCESSFUL here would mean the
// ensures never observed the store (vacuous-ensures false Safe).
// kani-flags: -Zfunction-contracts

use std::cell::Cell;

struct InteriorMutability {
    x: Cell<u32>,
}

#[kani::requires(im.x.get() == 5)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| im.x.get() == 7)]
fn modify(im: &InteriorMutability) {
    im.x.set(im.x.get() + 1)
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability = InteriorMutability { x: Cell::new(kani::any()) };
    modify(&im)
}
