// Dual (c): FC-06 frame condition. Field `y` is NOT in the modifies clause,
// but the body writes it via `im.y.set(42)`. The frame check MUST FAIL —
// proving the Cell::set store is subject to the modifies frame condition
// (the store targets a real object inside the frame checker's view).
// kani-flags: -Zfunction-contracts
use std::cell::Cell;

struct InteriorMutability {
    x: Cell<u32>,
    y: Cell<u32>,
}

#[kani::requires(im.x.get() < 100)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| im.x.get() < 101)]
fn modify(im: &InteriorMutability) {
    im.x.set(im.x.get() + 1);
    im.y.set(42);
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability =
        InteriorMutability { x: Cell::new(kani::any()), y: Cell::new(kani::any()) };
    modify(&im)
}
