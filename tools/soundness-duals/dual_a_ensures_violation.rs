// Dual (a): store/read must AGREE — the ensures violation must be caught.
// Body sets x = get()+2. With x=99 (allowed by requires x<100), the new value
// is 101, so `im.x.get() < 101` is FALSE. This MUST FAIL — proving the store
// and the ensures-read observe the same object (no vacuous pass).
// kani-flags: -Zfunction-contracts
use std::cell::Cell;

struct InteriorMutability {
    x: Cell<u32>,
}

#[kani::requires(im.x.get() < 100)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| im.x.get() < 101)]
fn modify(im: &InteriorMutability) {
    im.x.set(im.x.get() + 2)
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability = InteriorMutability { x: Cell::new(kani::any()) };
    modify(&im)
}
