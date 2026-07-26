// fcim dual (b) — FC-06 modifies-frame violation through interior mutability:
// field y: Cell<u32> is NOT in the modifies clause but the body writes it.
// The frame check MUST FAIL on the recovered real (obj, offset), proving the
// fc-interior-mut fix made the check precise rather than dropped (guards
// against repeating MISSED-BUG E, the modifies-frame store offset-drop).
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
    im.y.set(0) // FRAME VIOLATION: im.y is not in modifies(&im.x)
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability =
        InteriorMutability { x: Cell::new(kani::any()), y: Cell::new(kani::any()) };
    modify(&im)
}
