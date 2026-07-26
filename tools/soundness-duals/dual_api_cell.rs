// api/cell soundness dual: set(get()+2), modifies as_ptr, requires<100 ensures<101.
// MUST FAIL (x=99 -> 101). Proves store + get ensures-read agree under as_ptr modifies.
// kani-flags: -Zfunction-contracts
use std::cell::Cell;
struct IM { x: Cell<u32> }
#[kani::requires(im.x.get() < 100)]
#[kani::modifies(im.x.as_ptr())]
#[kani::ensures(|_| im.x.get() < 101)]
fn modify(im: &IM) { im.x.set(im.x.get() + 2) }
#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: IM = IM { x: Cell::new(kani::any()) };
    modify(&im)
}
