// Task #71 adversarial dual twin: same shape as dual71_wrong_ensures.rs but
// with the CORRECT ensures (+1). This harness must PASS (SUCCESSFUL) — it is
// the non-vacuity witness that the FAILURE of the wrong-ensures dual comes
// from the model actually observing the store, not from blanket failure.
// kani-flags: -Zfunction-contracts

use std::cell::Cell;

struct InteriorMutability {
    x: Cell<u32>,
}

#[kani::requires(im.x.get() < 100)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| im.x.get() == old(im.x.get()) + 1)]
fn modify(im: &InteriorMutability) {
    im.x.set(im.x.get() + 1)
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability = InteriorMutability { x: Cell::new(kani::any()) };
    modify(&im)
}
