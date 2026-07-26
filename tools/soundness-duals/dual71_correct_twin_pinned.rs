// Task #71 adversarial dual twin (pinned-initial variant, no old()): same
// shape as dual71_wrong_ensures_pinned.rs with the CORRECT ensures (6).
// Must PASS — the non-vacuity control proving the wrong twin's FAILURE comes
// from the model observing the store (5 -> set(6) -> read 6), not from
// blanket failure.
// kani-flags: -Zfunction-contracts

use std::cell::Cell;

struct InteriorMutability {
    x: Cell<u32>,
}

#[kani::requires(im.x.get() == 5)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| im.x.get() == 6)]
fn modify(im: &InteriorMutability) {
    im.x.set(im.x.get() + 1)
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability = InteriorMutability { x: Cell::new(kani::any()) };
    modify(&im)
}
